#include <vector>

#ifdef __cplusplus
extern "C"
{
#endif

#include "postgres.h"
#include "access/relscan.h"
#include "access/sysattr.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "catalog/pg_statistic.h"
#include "catalog/pg_am.h"
#include "commands/defrem.h"
#include "commands/explain.h"
#include "executor/executor.h"
#include "executor/nodeCustom.h"
#include "executor/nodeIndexscan.h"
#include "fmgr.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/nodes.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/paths.h"
#include "optimizer/pathnode.h"
#include "optimizer/plancat.h"
#include "optimizer/planmain.h"
#include "optimizer/placeholder.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/subselect.h"
#include "optimizer/var.h"
#include "optimizer/paramassign.h"
#include "optimizer/predtest.h"
#include "parser/parsetree.h"
#include "storage/bufmgr.h"
#include "storage/itemptr.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/ruleutils.h"
#include "utils/spccache.h"
#include "utils/selfuncs.h"
#include "utils/syscache.h"

PG_MODULE_MAGIC;

/*
 * HybridQueryState
 */
typedef struct {
	CustomScanState	css;
	IndexScan  *quals_is;
	IndexScan  *anns_is;
	IndexScanState *quals_iss;
	IndexScanState *anns_iss;
	ExprState  *indexqualorig;
	List	   *indexorderbyorig;
	ScanKey		iss_ScanKeys;
	int			iss_NumScanKeys;
	ScanKey		iss_OrderByKeys;
	int			iss_NumOrderByKeys;
	IndexRuntimeKeyInfo *iss_RuntimeKeys;
	int			iss_NumRuntimeKeys;
	bool		iss_RuntimeKeysReady;
	ExprContext *iss_RuntimeContext;
	Relation	iss_RelationDesc;
	IndexScanDesc iss_ScanDesc;

	pairingheap *iss_ReorderQueue;
	bool		iss_ReachedEnd;
	Datum	   *iss_OrderByValues;
	bool	   *iss_OrderByNulls;
	SortSupport iss_SortSupport;
	bool	   *iss_OrderByTypByVals;
	int16	   *iss_OrderByTypLens;
	Size		iss_PscanLen;
} HybridQueryState;

/* static variables */
static bool		enable_hybridquery;
static set_rel_pathlist_hook_type set_rel_pathlist_next = NULL;
double cost_from_distance_tables;
double cost_from_two_codes;

/* function declarations */
void _PG_init(void);
void _PG_fini(void);

static void set_hybridquery_path(PlannerInfo *root,
							RelOptInfo *rel,
							Index rti,
							RangeTblEntry *rte);

/* CustomPathMethods */
static Plan *PlanHybridQueryPath(PlannerInfo *root,
							  RelOptInfo *rel,
							  CustomPath *best_path,
							  List *tlist,
							  List *clauses,
							  List *custom_plans);

/* CustomScanMethods */
static Node *CreateHybridQueryScanState(CustomScan *custom_plan);

/* CustomScanExecMethods */
static void BeginHybridQueryScan(CustomScanState *node, EState *estate, int eflags);
static TupleTableSlot *ExecHybridQueryScan(CustomScanState *node);
static void EndHybridQueryScan(CustomScanState *node);
static void ReScanHybridQueryScan(CustomScanState *node);
static void ExplainHybridQueryScan(CustomScanState *node, List *ancestors,
							ExplainState *es);

/* static table of custom-scan callbacks */
static CustomPathMethods	hybridquery_path_methods = {
	"hybridquery",				/* CustomName */
	PlanHybridQueryPath,		/* PlanCustomPath */
	NULL,						/* ReparameterizeCustomPathByChild */
};

static CustomScanMethods	hybridquery_scan_methods = {
	"hybridquery",				/* CustomName */
	CreateHybridQueryScanState,	/* CreateCustomScanState */
};

static CustomExecMethods	hybridquery_exec_methods = {
	"hybridquery",				/* CustomName */
	BeginHybridQueryScan,			/* BeginCustomScan */
	ExecHybridQueryScan,			/* ExecCustomScan */
	EndHybridQueryScan,			/* EndCustomScan */
	ReScanHybridQueryScan,			/* ReScanCustomScan */
	NULL,					/* MarkPosCustomScan */
	NULL,					/* RestrPosCustomScan */
	NULL,					/* EstimateDSMCustomScan */
	NULL,					/* InitializeDSMCustomScan */
	NULL,					/* ReInitializeDSMCustomScan */
	NULL,					/* InitializeWorkerCustomScan */
	NULL,					/* ShutdownCustomScan */
	ExplainHybridQueryScan,		/* ExplainCustomScan */
};

static IndexOptInfo *
tryfind_anns_index(PlannerInfo *root,
						  RelOptInfo *baserel)
{
	IndexOptInfo   *indexOpt = NULL;
	ListCell	   *cell;

	/* skip if no indexes */
	if (baserel->indexlist == NIL)
		return NULL;

	foreach (cell, baserel->indexlist)
	{
		IndexOptInfo   *index = (IndexOptInfo *) lfirst(cell);
		List		   *temp = NIL;
		ListCell	   *lc;
		long			nblocks;

		/* Protect limited-size array in IndexClauseSets */
		Assert(index->ncolumns <= INDEX_MAX_KEYS);

		// NOTE: baserel->baserestrictinfo中不包含order by语句，需要按照create_hybridquery_path中检查order by语句那样去进行检查

		/* 16386: pg_ivfpq am oid */
		if (index->relam != 16386)
			continue;

		indexOpt = index;
	}

	return indexOpt;
}

/* Data structure for collecting qual clauses that match an index */
typedef struct
{
	bool		nonempty;		/* True if lists are not all empty */
	/* Lists of RestrictInfos, one per index column */
	List	   *indexclauses[INDEX_MAX_KEYS];
} IndexClauseSet;

/*
 * simple_match_clause_to_indexcol
 *
 * It is a simplified version of match_clause_to_indexcol.
 * Also see optimizer/path/indxpath.c
 */
static bool
simple_match_clause_to_indexcol(IndexOptInfo *index,
								int indexcol,
								RestrictInfo *rinfo)
{
	Expr	   *clause = rinfo->clause;
	Index		index_relid = index->rel->relid;
	Oid			opfamily = index->opfamily[indexcol];
	Oid			idxcollation = index->indexcollations[indexcol];
	Node	   *leftop;
	Node	   *rightop;
	Relids		left_relids;
	Relids		right_relids;
	Oid			expr_op;
	Oid			expr_coll;

	/* Clause must be a binary opclause */
	if (!is_opclause(clause))
		return false;

	leftop = get_leftop(clause);
	rightop = get_rightop(clause);
	if (!leftop || !rightop)
		return false;
	left_relids = rinfo->left_relids;
	right_relids = rinfo->right_relids;
	expr_op = ((OpExpr *) clause)->opno;
	expr_coll = ((OpExpr *) clause)->inputcollid;

	if (OidIsValid(idxcollation) && idxcollation != expr_coll)
		return false;

	/*
	 * Check for clauses of the form:
	 *    (indexkey operator constant) OR
	 *    (constant operator indexkey)
	 */
	if (match_index_to_operand(leftop, indexcol, index) &&
		!bms_is_member(index_relid, right_relids) &&
		!contain_volatile_functions(rightop) &&
		op_in_opfamily(expr_op, opfamily))
		return true;

	if (match_index_to_operand(rightop, indexcol, index) &&
		!bms_is_member(index_relid, left_relids) &&
		!contain_volatile_functions(leftop) &&
		op_in_opfamily(get_commutator(expr_op), opfamily))
		return true;

	return false;
}

/*
 * simple_match_clause_to_index
 *
 * It is a simplified version of match_clause_to_index.
 * Also see optimizer/path/indxpath.c
 */
static void
simple_match_clause_to_index(IndexOptInfo *index,
							 RestrictInfo *rinfo,
							 IndexClauseSet *clauseset)
{
	int		indexcol;

	/*
	 * Never match pseudoconstants to indexes.  (Normally a match could not
	 * happen anyway, since a pseudoconstant clause couldn't contain a Var,
	 * but what if someone builds an expression index on a constant? It's not
	 * totally unreasonable to do so with a partial index, either.)
	 */
	if (rinfo->pseudoconstant)
		return;

	/*
	 * If clause can't be used as an indexqual because it must wait till after
	 * some lower-security-level restriction clause, reject it.
	 */
	if (!restriction_is_securely_promotable(rinfo, index->rel))
		return;

	/* OK, check each index column for a match */
	for (indexcol = 0; indexcol < index->ncolumns; indexcol++)
	{
		if (simple_match_clause_to_indexcol(index,
											indexcol,
											rinfo))
		{
			clauseset->indexclauses[indexcol] =
				list_append_unique_ptr(clauseset->indexclauses[indexcol],
									   rinfo);
			clauseset->nonempty = true;
			break;
		}
	}
}

static List *
deconstruct_indexquals_for_hybridquery(IndexOptInfo *index, List *index_quals, List *quals_columns)
{
	List	   *result = NIL;
	ListCell   *lcc,
			   *lci;

	forboth(lcc, index_quals, lci, quals_columns)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lcc);
		int			indexcol = lfirst_int(lci);
		Expr	   *clause;
		Node	   *leftop,
				   *rightop;
		IndexQualInfo *qinfo;

		clause = rinfo->clause;

		qinfo = (IndexQualInfo *) palloc(sizeof(IndexQualInfo));
		qinfo->rinfo = rinfo;
		qinfo->indexcol = indexcol;

		if (IsA(clause, OpExpr))
		{
			qinfo->clause_op = ((OpExpr *) clause)->opno;
			leftop = get_leftop(clause);
			rightop = get_rightop(clause);
			if (match_index_to_operand(leftop, indexcol, index))
			{
				qinfo->varonleft = true;
				qinfo->other_operand = rightop;
			}
			else
			{
				Assert(match_index_to_operand(rightop, indexcol, index));
				qinfo->varonleft = false;
				qinfo->other_operand = leftop;
			}
		}
		else if (IsA(clause, RowCompareExpr))
		{
			RowCompareExpr *rc = (RowCompareExpr *) clause;

			qinfo->clause_op = linitial_oid(rc->opnos);
			/* Examine only first columns to determine left/right sides */
			if (match_index_to_operand((Node *) linitial(rc->largs),
									   indexcol, index))
			{
				qinfo->varonleft = true;
				qinfo->other_operand = (Node *) rc->rargs;
			}
			else
			{
				Assert(match_index_to_operand((Node *) linitial(rc->rargs),
											  indexcol, index));
				qinfo->varonleft = false;
				qinfo->other_operand = (Node *) rc->largs;
			}
		}
		else if (IsA(clause, ScalarArrayOpExpr))
		{
			ScalarArrayOpExpr *saop = (ScalarArrayOpExpr *) clause;

			qinfo->clause_op = saop->opno;
			/* index column is always on the left in this case */
			Assert(match_index_to_operand((Node *) linitial(saop->args),
										  indexcol, index));
			qinfo->varonleft = true;
			qinfo->other_operand = (Node *) lsecond(saop->args);
		}
		else if (IsA(clause, NullTest))
		{
			qinfo->clause_op = InvalidOid;
			Assert(match_index_to_operand((Node *) ((NullTest *) clause)->arg,
										  indexcol, index));
			qinfo->varonleft = true;
			qinfo->other_operand = NULL;
		}
		else
		{
			elog(ERROR, "unsupported indexqual type: %d",
				 (int) nodeTag(clause));
		}

		result = lappend(result, qinfo);
	}
	return result;
}

static void
genericcostestimate_for_hybridquery(PlannerInfo *root,
					IndexOptInfo *index,
					List *indexQuals,
					List *qinfos,
					GenericCosts *costs)
{
	// IndexOptInfo *index = path->indexinfo;
	// List	   *indexQuals = path->indexquals;
	// List	   *indexOrderBys = path->indexorderbys;
	Cost		indexStartupCost;
	Cost		indexTotalCost;
	Selectivity indexSelectivity;
	double		indexCorrelation;
	double		numIndexPages;
	double		numIndexTuples;
	double		spc_random_page_cost;
	double		num_sa_scans;
	double		num_outer_scans;
	double		num_scans;
	double		qual_op_cost;
	double		qual_arg_cost;
	List	   *selectivityQuals;
	ListCell   *l;

	/*
	 * If the index is partial, AND the index predicate with the explicitly
	 * given indexquals to produce a more accurate idea of the index
	 * selectivity.
	 */
	selectivityQuals = add_predicate_to_quals(index, indexQuals);

	/*
	 * Check for ScalarArrayOpExpr index quals, and estimate the number of
	 * index scans that will be performed.
	 */
	num_sa_scans = 1;
	foreach(l, indexQuals)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(l);

		if (IsA(rinfo->clause, ScalarArrayOpExpr))
		{
			ScalarArrayOpExpr *saop = (ScalarArrayOpExpr *) rinfo->clause;
			int			alength = estimate_array_length(lsecond(saop->args));

			if (alength > 1)
				num_sa_scans *= alength;
		}
	}

	/* Estimate the fraction of main-table tuples that will be visited */
	indexSelectivity = clauselist_selectivity(root, selectivityQuals,
											  index->rel->relid,
											  JOIN_INNER,
											  NULL);

	/*
	 * If caller didn't give us an estimate, estimate the number of index
	 * tuples that will be visited.  We do it in this rather peculiar-looking
	 * way in order to get the right answer for partial indexes.
	 */
	numIndexTuples = costs->numIndexTuples;
	if (numIndexTuples <= 0.0)
	{
		numIndexTuples = indexSelectivity * index->rel->tuples;

		/*
		 * The above calculation counts all the tuples visited across all
		 * scans induced by ScalarArrayOpExpr nodes.  We want to consider the
		 * average per-indexscan number, so adjust.  This is a handy place to
		 * round to integer, too.  (If caller supplied tuple estimate, it's
		 * responsible for handling these considerations.)
		 */
		numIndexTuples = rint(numIndexTuples / num_sa_scans);
	}

	/*
	 * We can bound the number of tuples by the index size in any case. Also,
	 * always estimate at least one tuple is touched, even when
	 * indexSelectivity estimate is tiny.
	 */
	if (numIndexTuples > index->tuples)
		numIndexTuples = index->tuples;
	if (numIndexTuples < 1.0)
		numIndexTuples = 1.0;

	/*
	 * Estimate the number of index pages that will be retrieved.
	 *
	 * We use the simplistic method of taking a pro-rata fraction of the total
	 * number of index pages.  In effect, this counts only leaf pages and not
	 * any overhead such as index metapage or upper tree levels.
	 *
	 * In practice access to upper index levels is often nearly free because
	 * those tend to stay in cache under load; moreover, the cost involved is
	 * highly dependent on index type.  We therefore ignore such costs here
	 * and leave it to the caller to add a suitable charge if needed.
	 */
	if (index->pages > 1 && index->tuples > 1)
		numIndexPages = ceil(numIndexTuples * index->pages / index->tuples);
	else
		numIndexPages = 1.0;

	/* fetch estimated page cost for tablespace containing index */
	get_tablespace_page_costs(index->reltablespace,
							  &spc_random_page_cost,
							  NULL);

	/*
	 * Now compute the disk access costs.
	 *
	 * The above calculations are all per-index-scan.  However, if we are in a
	 * nestloop inner scan, we can expect the scan to be repeated (with
	 * different search keys) for each row of the outer relation.  Likewise,
	 * ScalarArrayOpExpr quals result in multiple index scans.  This creates
	 * the potential for cache effects to reduce the number of disk page
	 * fetches needed.  We want to estimate the average per-scan I/O cost in
	 * the presence of caching.
	 *
	 * We use the Mackert-Lohman formula (see costsize.c for details) to
	 * estimate the total number of page fetches that occur.  While this
	 * wasn't what it was designed for, it seems a reasonable model anyway.
	 * Note that we are counting pages not tuples anymore, so we take N = T =
	 * index size, as if there were one "tuple" per page.
	 */
	// NOTE: loop_count恒等于1
	// num_outer_scans = loop_count;
	num_outer_scans = 1;
	num_scans = num_sa_scans * num_outer_scans;

	if (num_scans > 1)
	{
		double		pages_fetched;

		/* total page fetches ignoring cache effects */
		pages_fetched = numIndexPages * num_scans;

		/* use Mackert and Lohman formula to adjust for cache effects */
		pages_fetched = index_pages_fetched(pages_fetched,
											index->pages,
											(double) index->pages,
											root);

		/*
		 * Now compute the total disk access cost, and then report a pro-rated
		 * share for each outer scan.  (Don't pro-rate for ScalarArrayOpExpr,
		 * since that's internal to the indexscan.)
		 */
		indexTotalCost = (pages_fetched * spc_random_page_cost)
			/ num_outer_scans;
	}
	else
	{
		/*
		 * For a single index scan, we just charge spc_random_page_cost per
		 * page touched.
		 */
		indexTotalCost = numIndexPages * spc_random_page_cost;
	}

	/*
	 * CPU cost: any complex expressions in the indexquals will need to be
	 * evaluated once at the start of the scan to reduce them to runtime keys
	 * to pass to the index AM (see nodeIndexscan.c).  We model the per-tuple
	 * CPU costs as cpu_index_tuple_cost plus one cpu_operator_cost per
	 * indexqual operator.  Because we have numIndexTuples as a per-scan
	 * number, we have to multiply by num_sa_scans to get the correct result
	 * for ScalarArrayOpExpr cases.  Similarly add in costs for any index
	 * ORDER BY expressions.
	 *
	 * Note: this neglects the possible costs of rechecking lossy operators.
	 * Detecting that that might be needed seems more expensive than it's
	 * worth, though, considering all the other inaccuracies here ...
	 */
	// NOTE: 直接去掉order by的代价
	// qual_arg_cost = other_operands_eval_cost(root, qinfos) +
	// 	orderby_operands_eval_cost(root, path);
	// qual_op_cost = cpu_operator_cost *
	// 	(list_length(indexQuals) + list_length(indexOrderBys));
	qual_arg_cost = other_operands_eval_cost(root, qinfos);
	qual_op_cost = cpu_operator_cost * list_length(indexQuals);

	indexStartupCost = qual_arg_cost;
	indexTotalCost += qual_arg_cost;
	indexTotalCost += numIndexTuples * num_sa_scans * (cpu_index_tuple_cost + qual_op_cost);

	/*
	 * Generic assumption about index correlation: there isn't any.
	 */
	indexCorrelation = 0.0;

	/*
	 * Return everything to caller.
	 */
	costs->indexStartupCost = indexStartupCost;
	costs->indexTotalCost = indexTotalCost;
	costs->indexSelectivity = indexSelectivity;
	costs->indexCorrelation = indexCorrelation;
	costs->numIndexPages = numIndexPages;
	costs->numIndexTuples = numIndexTuples;
	costs->spc_random_page_cost = spc_random_page_cost;
	costs->num_sa_scans = num_sa_scans;
}

static IndexPath *
create_structured_index_path(PlannerInfo *root,
							 RelOptInfo *baserel,
							 IndexOptInfo *index,
							 IndexClauseSet *clauseset)
{
	List	  *result = NIL;
	IndexPath *ipath;
	List	  *index_clauses;
	List	  *clause_columns;
	Relids	   outer_relids;
	double	   loop_count;
	List	  *orderbyclauses;
	List	  *orderbyclausecols;
	List	  *index_pathkeys;
	List	  *useful_pathkeys;
	bool	   found_lower_saop_clause;
	bool	   pathkeys_possibly_useful;
	bool	   index_is_ordered;
	bool	   index_only_scan;
	int		   indexcol;

	for (indexcol = 0; indexcol < index->ncolumns; indexcol++)
	{
		ListCell   *lc;

		foreach (lc, clauses->indexclauses[indexcol])
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			index_clauses = lappend(index_clauses, rinfo);
			clause_columns = lappend_int(clause_columns, indexcol);
		}

		if (index_clauses == NIL && !index->amoptionalkey)
			return NIL;
	}

	/* 忽略结构化条件的ORDER BY表达式 */
	useful_pathkeys = NIL;
	orderbyclauses = NIL;
	orderbyclausecols = NIL;

	/*
	 * NOTE:
	 * 结构化条件只用来缩小向量索引的搜索范围，只需要得到行数据在原始表中的ItemPointerData，
	 * 因此此处只需要创建T_IndexOnlyScan。
	 */
	ipath = create_index_path(root, index,
							index_clauses,
							clause_columns,
							NIL,
							NIL,
							useful_pathkeys,
							ForwardScanDirection,	// ForwardScanDirection
							true,					// T_IndexOnlyScan
							NULL,
							1.0,
							false);
	
	/* 
	 * TODO: 
	 * 默认ForwardScanDirection，但不确定ForwardScanDirection和BackwardScanDirection的代价是否一样，
	 * 如果不一样，还需要考虑BackwardScanDirection的路径，然后选择代价比较低的路径（选择率必定是一样的）。
	 */	

	return ipath;
}

static List *
find_structured_index_paths(PlannerInfo *root,
							RelOptInfo *baserel)
{
	List		*index_paths = NIL;
	ListCell	*icell;

	/* skip if no indexes */
	if (baserel->indexlist == NIL)
		return NULL;

	foreach (icell, baserel->indexlist)
	{
		IndexOptInfo	*index = (IndexOptInfo *) lfirst(icell);
		ListCell		*rcell;
		IndexPath		*index_path;
		IndexClauseSet	 clauseset;
		int				 indrestrictcols = 0;

		/* Protect limited-size array in IndexClauseSets */
		Assert(index->ncolumns <= INDEX_MAX_KEYS);

		/* Ignore partial indexes that do not match the query. */
		if (index->indpred != NIL && !index->predOK)
			continue;

		/* NOTE: 现在只处理创建了btree索引的结构化条件。 */
		if (index->relam != BTREE_AM_OID)
			continue;

		MemSet(&clauseset, 0, sizeof(clauseset));

		/* 
		 * 每个IndexOptInfo里面的indrestrictinfo成员和RelOptInfo的baserestrictinfo成员都指向同一个值，
		 * 表示RelOptInfo上非连接的约束条件。
		 */
		foreach (rcell, index->indrestrictinfo)
		{
			RestrictInfo *rinfo = lfirst_node(RestrictInfo, rcell);

			/*
			 * NOTE:
			 * 因为还没有完全理解ScalarArrayOpExpr的处理方式，
			 * 因此这里暂时不处理ScalarArrayOpExpr类型的约束条件。
			 */
			if (IsA(rinfo->clause, ScalarArrayOpExpr))
			{
				continue;
			}

			simple_match_clause_to_index(index, rinfo, &clauseset);
		}
		if (!clauseset.nonempty)
			continue;
		
		/* 
		 * NOTE:
		 * 目前单列属性的选择率估计得比较准，而多列属性的选择率估计得不是很准，
		 * 因此暂时只使用单列属性的索引。
		 */
		for (int indexcol = 0; indexcol < INDEX_MAX_KEYS; indexcol++)
		{
			List *indexclause = clauseset.indexclauses[indexcol];
			if (indexclause != NULL)
				indrestrictcols++;
		}
		if (indrestrictcols > 1)
			continue;
		
		index_path = create_structured_index_path(root, baserel, index, &clauseset);
		lappend(index_paths, index_path);
	}

	return index_paths;
}

/* 
typedef struct IndexPath
{
	Path		path;
	IndexOptInfo *indexinfo;
	List	   *indexclauses;
	List	   *indexquals;
	List	   *indexqualcols;
	List	   *indexorderbys;
	List	   *indexorderbycols;
	ScanDirection indexscandir;
	Cost		indextotalcost;
	Selectivity indexselectivity;
} IndexPath;
*/

static double
approximate_joinrel_size(PlannerInfo *root, Relids relids)
{
	double		rowcount = 1.0;
	int			relid;

	relid = -1;
	while ((relid = bms_next_member(relids, relid)) >= 0)
	{
		RelOptInfo *rel;

		/* Paranoia: ignore bogus relid indexes */
		if (relid >= root->simple_rel_array_size)
			continue;
		rel = root->simple_rel_array[relid];
		if (rel == NULL)
			continue;
		Assert(rel->relid == relid);	/* sanity check on array */

		/* Relation could be proven empty, if so ignore */
		if (IS_DUMMY_REL(rel))
			continue;

		/* Otherwise, rel's rows estimate should be valid by now */
		Assert(rel->rows > 0);

		/* Accumulate product */
		rowcount *= rel->rows;
	}
	return rowcount;
}

static double
adjust_rowcount_for_semijoins(PlannerInfo *root,
							  Index cur_relid,
							  Index outer_relid,
							  double rowcount)
{
	ListCell   *lc;

	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);

		if (sjinfo->jointype == JOIN_SEMI &&
			bms_is_member(cur_relid, sjinfo->syn_lefthand) &&
			bms_is_member(outer_relid, sjinfo->syn_righthand))
		{
			/* Estimate number of unique-ified rows */
			double		nraw;
			double		nunique;

			nraw = approximate_joinrel_size(root, sjinfo->syn_righthand);
			nunique = estimate_num_groups(root,
										  sjinfo->semi_rhs_exprs,
										  nraw,
										  NULL);
			if (rowcount > nunique)
				rowcount = nunique;
		}
	}
	return rowcount;
}

static double
get_loop_count(PlannerInfo *root, Index cur_relid, Relids outer_relids)
{
	double		result;
	int			outer_relid;

	/* For a non-parameterized path, just return 1.0 quickly */
	if (outer_relids == NULL)
		return 1.0;

	result = 0.0;
	outer_relid = -1;
	while ((outer_relid = bms_next_member(outer_relids, outer_relid)) >= 0)
	{
		RelOptInfo *outer_rel;
		double		rowcount;

		/* Paranoia: ignore bogus relid indexes */
		if (outer_relid >= root->simple_rel_array_size)
			continue;
		outer_rel = root->simple_rel_array[outer_relid];
		if (outer_rel == NULL)
			continue;
		Assert(outer_rel->relid == outer_relid);	/* sanity check on array */

		/* Other relation could be proven empty, if so ignore */
		if (IS_DUMMY_REL(outer_rel))
			continue;

		/* Otherwise, rel's rows estimate should be valid by now */
		Assert(outer_rel->rows > 0);

		/* Check to see if rel is on the inside of any semijoins */
		rowcount = adjust_rowcount_for_semijoins(root,
												 cur_relid,
												 outer_relid,
												 outer_rel->rows);

		/* Remember smallest row count estimate among the outer rels */
		if (result == 0.0 || result > rowcount)
			result = rowcount;
	}
	/* Return 1.0 if we found no valid relations (shouldn't happen) */
	return (result > 0.0) ? result : 1.0;
}

/* XXX see PartCollMatchesExprColl */
#define IndexCollMatchesExprColl(idxcollation, exprcollation) \
	((idxcollation) == InvalidOid || (idxcollation) == (exprcollation))

static Expr *
hybridquery_match_clause_to_ordering_op(IndexOptInfo *index,
							int indexcol,
							Expr *clause,
							Oid pk_opfamily)
{
	Oid			opfamily;
	Oid			idxcollation;
	Node	   *leftop,
			   *rightop;
	Oid			expr_op;
	Oid			expr_coll;
	Oid			sortfamily;
	bool		commuted;

	Assert(indexcol < index->nkeycolumns);

	opfamily = index->opfamily[indexcol];
	idxcollation = index->indexcollations[indexcol];

	/*
	 * Clause must be a binary opclause.
	 */
	if (!is_opclause(clause))
		return NULL;
	leftop = get_leftop(clause);
	rightop = get_rightop(clause);
	if (!leftop || !rightop)
		return NULL;
	expr_op = ((OpExpr *) clause)->opno;
	expr_coll = ((OpExpr *) clause)->inputcollid;

	/*
	 * We can forget the whole thing right away if wrong collation.
	 */
	if (!IndexCollMatchesExprColl(idxcollation, expr_coll))
		return NULL;

	/*
	 * Check for clauses of the form: (indexkey operator constant) or
	 * (constant operator indexkey).
	 */
	if (match_index_to_operand(leftop, indexcol, index) &&
		!contain_var_clause(rightop) &&
		!contain_volatile_functions(rightop))
	{
		commuted = false;
	}
	else if (match_index_to_operand(rightop, indexcol, index) &&
			 !contain_var_clause(leftop) &&
			 !contain_volatile_functions(leftop))
	{
		/* Might match, but we need a commuted operator */
		expr_op = get_commutator(expr_op);
		if (expr_op == InvalidOid)
			return NULL;
		commuted = true;
	}
	else
		return NULL;

	/*
	 * Is the (commuted) operator an ordering operator for the opfamily? And
	 * if so, does it yield the right sorting semantics?
	 */
	sortfamily = get_op_opfamily_sortfamily(expr_op, opfamily);
	if (sortfamily != pk_opfamily)
		return NULL;

	/* We have a match.  Return clause or a commuted version thereof. */
	if (commuted)
	{
		OpExpr	   *newclause = makeNode(OpExpr);

		/* flat-copy all the fields of clause */
		memcpy(newclause, clause, sizeof(OpExpr));

		/* commute it */
		newclause->opno = expr_op;
		newclause->opfuncid = InvalidOid;
		newclause->args = list_make2(rightop, leftop);

		clause = (Expr *) newclause;
	}

	return clause;
}

static void
hybridquery_match_pathkeys_to_index(IndexOptInfo *index, List *pathkeys,
						List **orderby_clauses_p,
						List **clause_columns_p)
{
	List	   *orderby_clauses = NIL;
	List	   *clause_columns = NIL;
	ListCell   *lc1;

	*orderby_clauses_p = NIL;	/* set default results */
	*clause_columns_p = NIL;

	/* Only indexes with the amcanorderbyop property are interesting here */
	if (!index->amcanorderbyop)
		return;

	foreach(lc1, pathkeys)
	{
		PathKey    *pathkey = (PathKey *) lfirst(lc1);
		bool		found = false;
		ListCell   *lc2;

		/*
		 * Note: for any failure to match, we just return NIL immediately.
		 * There is no value in matching just some of the pathkeys.
		 */

		/* Pathkey must request default sort order for the target opfamily */
		/* TODO: */
		if (pathkey->pk_strategy != BTLessStrategyNumber ||
			pathkey->pk_nulls_first)
			return;

		/* If eclass is volatile, no hope of using an indexscan */
		if (pathkey->pk_eclass->ec_has_volatile)
			return;

		/*
		 * Try to match eclass member expression(s) to index.  Note that child
		 * EC members are considered, but only when they belong to the target
		 * relation.  (Unlike regular members, the same expression could be a
		 * child member of more than one EC.  Therefore, the same index could
		 * be considered to match more than one pathkey list, which is OK
		 * here.  See also get_eclass_for_sort_expr.)
		 */
		foreach(lc2, pathkey->pk_eclass->ec_members)
		{
			EquivalenceMember *member = (EquivalenceMember *) lfirst(lc2);
			int			indexcol;

			/* No possibility of match if it references other relations */
			if (!bms_equal(member->em_relids, index->rel->relids))
				continue;

			/*
			 * We allow any column of the index to match each pathkey; they
			 * don't have to match left-to-right as you might expect.  This is
			 * correct for GiST, which is the sole existing AM supporting
			 * amcanorderbyop.  We might need different logic in future for
			 * other implementations.
			 */
			for (indexcol = 0; indexcol < index->ncolumns; indexcol++)
			{
				Expr	   *expr;

				expr = hybridquery_match_clause_to_ordering_op(index,
												   indexcol,
												   member->em_expr,
												   pathkey->pk_opfamily);
				if (expr)
				{
					orderby_clauses = lappend(orderby_clauses, expr);
					clause_columns = lappend_int(clause_columns, indexcol);
					found = true;
					break;
				}
			}

			if (found)			/* don't want to look at remaining members */
				break;
		}

		if (!found)				/* fail if no match for this pathkey */
			return;
	}

	*orderby_clauses_p = orderby_clauses;	/* success! */
	*clause_columns_p = clause_columns;
}

static Name
GetIndexAmNameByAmOid(Oid amoid, bool noerror)
{
	HeapTuple tuple;
	Form_pg_am amform;
	Name amname;

	tuple = SearchSysCache1(AMOID, ObjectIdGetDatum(amoid));
	if (!HeapTupleIsValid(tuple))
	{
		if (noerror)
			return NULL;
		elog(ERROR, "cache lookup failed for access method %u",
			 amoid);
	}
	amform = (Form_pg_am)GETSTRUCT(tuple);

	/* Check if it's an index access method as opposed to some other AM */
	if (amform->amtype != AMTYPE_INDEX)
	{
		if (noerror)
		{
			ReleaseSysCache(tuple);
			return NULL;
		}
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("access method \"%s\" is not of type %s",
						NameStr(amform->amname), "INDEX")));
	}

	amname = &(amform->amname);

	ReleaseSysCache(tuple);

	return amname;
}

static Oid
GetIndexAmOidByAmName(const char *amname)
{
	Oid amoid;
	HeapTuple tuple;

	tuple = SearchSysCache1(AMNAME, PointerGetDatum(amname));
	if (!HeapTupleIsValid(tuple))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_OBJECT),
				errmsg("access method \"%s\" does not exist", amname)));
	amoid = HeapTupleGetOid(tuple);

	return amoid;
}

bool
is_anns_index(Oid amoid)
{
	Name amname = GetIndexAmNameByAmOid(amoid, true);

	if (!amname)
		return false;
	
	char *amname_str = amname->data;

	/* NOTE: 现在只有pg_ivfpq索引支持联合查询。*/
	if (strcmp("pg_ivfpq", amname_str) == 0)
		return true;
	else
		return false;
}

static IndexPath *
create_anns_index_path(PlannerInfo *root,
					   IndexOptInfo *index,
					   List *orderbyclauses,
					   List *orderbyclausecols)
{
	IndexPath *ipath;

	/*
	 * NOTE:
	 * 1. 向量索引扫描方向只能设置为NoMovementScanDirection；
	 * 2. 向量索引目前不支持T_IndexOnlyScan，因此只能创建T_IndexScan。
	 */
	ipath = create_index_path(root, index,
							NIL,
							NIL,
							orderbyclauses,
							orderbyclausecols,
							root->query_pathkeys,
							NoMovementScanDirection,	// NoMovementScanDirection
							false,						// T_IndexScan
							NULL,
							1.0,
							false);

	return ipath;
}

static List *
find_anns_index_paths(PlannerInfo *root,
					  RelOptInfo *baserel)
{
	List		*index_paths = NIL;
	ListCell	*icell;

	/* skip if no indexes */
	if (baserel->indexlist == NIL)
		return NULL;

	foreach (icell, baserel->indexlist)
	{
		IndexOptInfo	*index = (IndexOptInfo *) lfirst(icell);
		IndexPath		*index_path;
		List			*orderbyclauses;
		List			*orderbyclausecols;

		/* Protect limited-size array in IndexClauseSets */
		Assert(index->ncolumns <= INDEX_MAX_KEYS);

		/* Ignore partial indexes that do not match the query. */
		if (index->indpred != NIL && !index->predOK)
			continue;
		
		if (!is_anns_index(index->relam))
			continue;

		/* see if we can generate ordering operators for query_pathkeys */
		hybridquery_match_pathkeys_to_index(index, root->query_pathkeys,
								&orderbyclauses,
								&orderbyclausecols);
		if (orderbyclauses != NIL && \
			orderbyclausecols != NIL)
			continue;
		
		index_path = create_anns_index_path(root, baserel, index, orderbyclauses, orderbyclausecols);
		lappend(index_paths, index_path);
	}

	return index_paths;
}

static bool
find_best_paths(List *structured_index_paths, List *anns_index_paths,
				List **p_best_structured_index_path, List **p_best_anns_index_path)
{
	bool		 use_hybridquery = false;
	IndexPath	*best_structured_index_path = NIL;
	IndexPath	*best_anns_index_path = NIL;
	ListCell	*lc;

	/* 
	 * NOTE:
	 * 这里只关注选择率，因为要通过结构化索引的结果去优化向量索引的搜索，
	 * 结构化索引的选择率越低，向量索引的搜索越快。
	 */
	Selectivity best_selectivity = 1.0;
	foreach (lc, structured_index_paths)
	{
		IndexPath *index_path = (IndexPath *)lfirst(lc);
		if (best_selectivity > index_path->indexselectivity)
		{
			best_selectivity = index_path->indexselectivity;
			best_structured_index_path = index_path;
		}
	}

	Cost best_anns_cost = DBL_MAX;
	foreach (lc, anns_index_paths)
	{
		IndexPath *index_path = (IndexPath *)lfirst(lc);
		if (best_anns_cost > index_path->indextotalcost)
		{
			best_anns_cost = index_path->indextotalcost;
			best_anns_index_path = index_path;
		}
	}

	int32 n = 1000000;
	int32 ni = 64;
	Cost anns_structured_cost;
	Cost structured_anns_cost;
	anns_structured_cost = (128.0 / 512.0) * n * cost_from_distance_tables;
	structured_anns_cost = best_structured_index_path->indextotalcost + best_selectivity * n * cost_from_distance_tables;

	Cost anns_structured_anns_io_cost;
	Cost structured_anns_anns_io_cost;
	anns_structured_anns_io_cost = (128.0 / 512.0) * ((float)n / ni) * DEFAULT_SEQ_PAGE_COST;
	structured_anns_anns_io_cost = best_selectivity * n * DEFAULT_RANDOM_PAGE_COST;

	anns_structured_cost += anns_structured_anns_io_cost;
	structured_anns_cost += structured_anns_anns_io_cost;

	if (anns_structured_cost > structured_anns_cost)
	{
		use_hybridquery = true;
		// TODO: 更新结构化索引和向量索引的cost
		*p_best_structured_index_path = best_structured_index_path;
		*p_best_anns_index_path = best_anns_index_path;
	}

	return use_hybridquery;
}

/*
 * set_hybridquery_path
 */
static void
set_hybridquery_path(PlannerInfo *root, RelOptInfo *baserel,
				Index rtindex, RangeTblEntry *rte)
{
	CustomPath	*cpath;
	List		*structured_index_paths;
	List		*anns_index_paths;
	// NOTE: 如果进行联合查询，向量索引肯定是最后执行的。
	IndexPath	*best_structured_index_path = NIL;
	IndexPath	*best_anns_index_path = NIL;
	bool		 use_hybridquery;

	/* 
	 * 使用联合查询的条件：
	 * 1. 从原始表查询；
	 * 2. 联合查询开启；
	 * 3. 查询能使用结构化索引；
	 * 4. 查询能使用向量索引；
	 * 5. 联合查询的代价比非联合查询的代价低。
	 */

	// 1. 从原始表查询
	if (baserel->rtekind != RTE_RELATION || \
		rte->rtekind != RTE_RELATION)
		return;

	// 2. 联合查询开启；
	if (!enable_hybridquery)
		return;
	
	// 3. 结构化索引
	structured_index_paths = find_structured_index_paths(root, baserel);
	if (structured_index_paths->length == 0)
		return;
	
	// 4. 向量索引
	anns_index_paths = find_anns_index_paths(root, baserel);
	if (anns_index_paths->length == 0)
		return;
	
	// 5. 联合查询的代价比非联合查询的代价低
	use_hybridquery = find_best_paths(structured_index_paths, anns_index_paths,
									  &best_structured_index_path, &best_anns_index_path);
	// 是否进行联合查询，不使用联合查询则直接返回，此时会使用PostgreSQL规划的路径。
	if (!use_hybridquery)
		return;

	// 填充CustomPath数据结构，并将best_structured_path和best_anns_path放到CustomPath中。
	cpath = makeNode(CustomPath);
	cpath->path.pathtype = T_CustomScan;

	cpath->path.parent = baserel;
	cpath->path.pathtarget = baserel->reltarget;

	// TODO: 搞清楚这里
	cpath->path.param_info = get_baserel_parampathinfo(root, baserel,
													   baserel->lateral_relids);
	// NOTE: 暂时不支持并行查询
	cpath->path.parallel_aware = false;
	cpath->path.parallel_safe = baserel->consider_parallel;
	cpath->path.parallel_workers = 0;

	// TODO: 待确认startup_cost和total_cost这样设置是否正确
	cpath->path.rows = 512;  // TODO: be fixed to 512 now and to be fixed later.
	cpath->path.startup_cost = best_structured_index_path->indextotalcost;
	cpath->path.total_cost = best_anns_index_path->indextotalcost;

	cpath->path.pathkeys = root->query_pathkeys;

	cpath->flags = 0;
	cpath->custom_paths = list_make2(best_structured_index_path, best_anns_index_path);
	cpath->custom_private = NULL;
	cpath->methods = &hybridquery_path_methods;

	// 将CustomPath（即联合查询的最优路径）添加到baserel的pathlist中。
	add_path(baserel, &cpath->path);  // 其实就是传递的CustomPath的指针，这样做是为了达到类似C++的多态效果。
}

static Node *
replace_nestloop_params_mutator(Node *node, PlannerInfo *root)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		Var		   *var = (Var *) node;

		/* Upper-level Vars should be long gone at this point */
		Assert(var->varlevelsup == 0);
		/* If not to be replaced, we can just return the Var unmodified */
		if (!bms_is_member(var->varno, root->curOuterRels))
			return node;
		/* Replace the Var with a nestloop Param */
		return (Node *) replace_nestloop_param_var(root, var);
	}
	if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar *phv = (PlaceHolderVar *) node;

		/* Upper-level PlaceHolderVars should be long gone at this point */
		Assert(phv->phlevelsup == 0);

		/*
		 * Check whether we need to replace the PHV.  We use bms_overlap as a
		 * cheap/quick test to see if the PHV might be evaluated in the outer
		 * rels, and then grab its PlaceHolderInfo to tell for sure.
		 */
		if (!bms_overlap(phv->phrels, root->curOuterRels) ||
			!bms_is_subset(find_placeholder_info(root, phv, false)->ph_eval_at,
						   root->curOuterRels))
		{
			/*
			 * We can't replace the whole PHV, but we might still need to
			 * replace Vars or PHVs within its expression, in case it ends up
			 * actually getting evaluated here.  (It might get evaluated in
			 * this plan node, or some child node; in the latter case we don't
			 * really need to process the expression here, but we haven't got
			 * enough info to tell if that's the case.)  Flat-copy the PHV
			 * node and then recurse on its expression.
			 *
			 * Note that after doing this, we might have different
			 * representations of the contents of the same PHV in different
			 * parts of the plan tree.  This is OK because equal() will just
			 * match on phid/phlevelsup, so setrefs.c will still recognize an
			 * upper-level reference to a lower-level copy of the same PHV.
			 */
			PlaceHolderVar *newphv = makeNode(PlaceHolderVar);

			memcpy(newphv, phv, sizeof(PlaceHolderVar));
			newphv->phexpr = (Expr *)
				replace_nestloop_params_mutator((Node *) phv->phexpr,
												root);
			return (Node *) newphv;
		}
		/* Replace the PlaceHolderVar with a nestloop Param */
		return (Node *) replace_nestloop_param_placeholdervar(root, phv);
	}
	return expression_tree_mutator(node,
								   replace_nestloop_params_mutator,
								   (void *) root);
}

static Node *
replace_nestloop_params(PlannerInfo *root, Node *expr)
{
	/* No setup needed for tree walk, so away we go */
	return replace_nestloop_params_mutator(expr, root);
}

extern void *copyObjectImpl(const void *obj);
#define copyObject(obj) copyObjectImpl(obj)

static Node *
fix_indexqual_operand(Node *node, IndexOptInfo *index, int indexcol)
{
	Var		   *result;
	int			pos;
	ListCell   *indexpr_item;

	/*
	 * Remove any binary-compatible relabeling of the indexkey
	 */
	if (IsA(node, RelabelType))
		node = (Node *) ((RelabelType *) node)->arg;

	Assert(indexcol >= 0 && indexcol < index->ncolumns);

	if (index->indexkeys[indexcol] != 0)
	{
		/* It's a simple index column */
		if (IsA(node, Var) &&
			((Var *) node)->varno == index->rel->relid &&
			((Var *) node)->varattno == index->indexkeys[indexcol])
		{
			result = (Var *) copyObject(node);
			result->varno = INDEX_VAR;
			result->varattno = indexcol + 1;
			return (Node *) result;
		}
		else
			elog(ERROR, "index key does not match expected index column");
	}

	/* It's an index expression, so find and cross-check the expression */
	indexpr_item = list_head(index->indexprs);
	for (pos = 0; pos < index->ncolumns; pos++)
	{
		if (index->indexkeys[pos] == 0)
		{
			if (indexpr_item == NULL)
				elog(ERROR, "too few entries in indexprs list");
			if (pos == indexcol)
			{
				Node	   *indexkey;

				indexkey = (Node *) lfirst(indexpr_item);
				if (indexkey && IsA(indexkey, RelabelType))
					indexkey = (Node *) ((RelabelType *) indexkey)->arg;
				if (equal(node, indexkey))
				{
					result = makeVar(INDEX_VAR, indexcol + 1,
									 exprType(lfirst(indexpr_item)), -1,
									 exprCollation(lfirst(indexpr_item)),
									 0);
					return (Node *) result;
				}
				else
					elog(ERROR, "index key does not match expected index column");
			}
			indexpr_item = lnext(indexpr_item);
		}
	}

	/* Oops... */
	elog(ERROR, "index key does not match expected index column");
	return NULL;				/* keep compiler quiet */
}

static List *
fix_indexqual_references(PlannerInfo *root, IndexPath *index_path)
{
	IndexOptInfo *index = index_path->indexinfo;
	List	   *fixed_indexquals;
	ListCell   *lcc,
			   *lci;

	fixed_indexquals = NIL;

	forboth(lcc, index_path->indexquals, lci, index_path->indexqualcols)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lcc);
		int			indexcol = lfirst_int(lci);
		Node	   *clause;

		/*
		 * Replace any outer-relation variables with nestloop params.
		 *
		 * This also makes a copy of the clause, so it's safe to modify it
		 * in-place below.
		 */
		clause = replace_nestloop_params(root, (Node *) rinfo->clause);

		if (IsA(clause, OpExpr))
		{
			OpExpr	   *op = (OpExpr *) clause;

			if (list_length(op->args) != 2)
				elog(ERROR, "indexqual clause is not binary opclause");

			/*
			 * Check to see if the indexkey is on the right; if so, commute
			 * the clause.  The indexkey should be the side that refers to
			 * (only) the base relation.
			 */
			if (!bms_equal(rinfo->left_relids, index->rel->relids))
				CommuteOpExpr(op);

			/*
			 * Now replace the indexkey expression with an index Var.
			 */
			linitial(op->args) = fix_indexqual_operand(linitial(op->args),
													   index,
													   indexcol);
		}
		else if (IsA(clause, RowCompareExpr))
		{
			RowCompareExpr *rc = (RowCompareExpr *) clause;
			Expr	   *newrc;
			List	   *indexcolnos;
			bool		var_on_left;
			ListCell   *lca,
					   *lcai;

			/*
			 * Re-discover which index columns are used in the rowcompare.
			 */
			newrc = adjust_rowcompare_for_index(rc,
												index,
												indexcol,
												&indexcolnos,
												&var_on_left);

			/*
			 * Trouble if adjust_rowcompare_for_index thought the
			 * RowCompareExpr didn't match the index as-is; the clause should
			 * have gone through that routine already.
			 */
			if (newrc != (Expr *) rc)
				elog(ERROR, "inconsistent results from adjust_rowcompare_for_index");

			/*
			 * Check to see if the indexkey is on the right; if so, commute
			 * the clause.
			 */
			if (!var_on_left)
				CommuteRowCompareExpr(rc);

			/*
			 * Now replace the indexkey expressions with index Vars.
			 */
			Assert(list_length(rc->largs) == list_length(indexcolnos));
			forboth(lca, rc->largs, lcai, indexcolnos)
			{
				lfirst(lca) = fix_indexqual_operand(lfirst(lca),
													index,
													lfirst_int(lcai));
			}
		}
		else if (IsA(clause, ScalarArrayOpExpr))
		{
			ScalarArrayOpExpr *saop = (ScalarArrayOpExpr *) clause;

			/* Never need to commute... */

			/* Replace the indexkey expression with an index Var. */
			linitial(saop->args) = fix_indexqual_operand(linitial(saop->args),
														 index,
														 indexcol);
		}
		else if (IsA(clause, NullTest))
		{
			NullTest   *nt = (NullTest *) clause;

			/* Replace the indexkey expression with an index Var. */
			nt->arg = (Expr *) fix_indexqual_operand((Node *) nt->arg,
													 index,
													 indexcol);
		}
		else
			elog(ERROR, "unsupported indexqual type: %d",
				 (int) nodeTag(clause));

		fixed_indexquals = lappend(fixed_indexquals, clause);
	}

	return fixed_indexquals;
}

static List *
fix_indexorderby_references(PlannerInfo *root, IndexPath *index_path)
{
	IndexOptInfo *index = index_path->indexinfo;
	List	   *fixed_indexorderbys;
	ListCell   *lcc,
			   *lci;

	fixed_indexorderbys = NIL;

	forboth(lcc, index_path->indexorderbys, lci, index_path->indexorderbycols)
	{
		Node	   *clause = (Node *) lfirst(lcc);
		int			indexcol = lfirst_int(lci);

		/*
		 * Replace any outer-relation variables with nestloop params.
		 *
		 * This also makes a copy of the clause, so it's safe to modify it
		 * in-place below.
		 */
		clause = replace_nestloop_params(root, clause);

		if (IsA(clause, OpExpr))
		{
			OpExpr	   *op = (OpExpr *) clause;

			if (list_length(op->args) != 2)
				elog(ERROR, "indexorderby clause is not binary opclause");

			/*
			 * Now replace the indexkey expression with an index Var.
			 */
			linitial(op->args) = fix_indexqual_operand(linitial(op->args),
													   index,
													   indexcol);
		}
		else
			elog(ERROR, "unsupported indexorderby type: %d",
				 (int) nodeTag(clause));

		fixed_indexorderbys = lappend(fixed_indexorderbys, clause);
	}

	return fixed_indexorderbys;
}

static List *
order_qual_clauses(PlannerInfo *root, List *clauses)
{
	typedef struct
	{
		Node	   *clause;
		Cost		cost;
		Index		security_level;
	} QualItem;
	int			nitems = list_length(clauses);
	QualItem   *items;
	ListCell   *lc;
	int			i;
	List	   *result;

	/* No need to work hard for 0 or 1 clause */
	if (nitems <= 1)
		return clauses;

	/*
	 * Collect the items and costs into an array.  This is to avoid repeated
	 * cost_qual_eval work if the inputs aren't RestrictInfos.
	 */
	items = (QualItem *) palloc(nitems * sizeof(QualItem));
	i = 0;
	foreach(lc, clauses)
	{
		Node	   *clause = (Node *) lfirst(lc);
		QualCost	qcost;

		cost_qual_eval_node(&qcost, clause, root);
		items[i].clause = clause;
		items[i].cost = qcost.per_tuple;
		if (IsA(clause, RestrictInfo))
		{
			RestrictInfo *rinfo = (RestrictInfo *) clause;

			/*
			 * If a clause is leakproof, it doesn't have to be constrained by
			 * its nominal security level.  If it's also reasonably cheap
			 * (here defined as 10X cpu_operator_cost), pretend it has
			 * security_level 0, which will allow it to go in front of
			 * more-expensive quals of lower security levels.  Of course, that
			 * will also force it to go in front of cheaper quals of its own
			 * security level, which is not so great, but we can alleviate
			 * that risk by applying the cost limit cutoff.
			 */
			if (rinfo->leakproof && items[i].cost < 10 * cpu_operator_cost)
				items[i].security_level = 0;
			else
				items[i].security_level = rinfo->security_level;
		}
		else
			items[i].security_level = 0;
		i++;
	}

	/*
	 * Sort.  We don't use qsort() because it's not guaranteed stable for
	 * equal keys.  The expected number of entries is small enough that a
	 * simple insertion sort should be good enough.
	 */
	for (i = 1; i < nitems; i++)
	{
		QualItem	newitem = items[i];
		int			j;

		/* insert newitem into the already-sorted subarray */
		for (j = i; j > 0; j--)
		{
			QualItem   *olditem = &items[j - 1];

			if (newitem.security_level > olditem->security_level ||
				(newitem.security_level == olditem->security_level &&
				 newitem.cost >= olditem->cost))
				break;
			items[j] = *olditem;
		}
		items[j] = newitem;
	}

	/* Convert back to a list */
	result = NIL;
	for (i = 0; i < nitems; i++)
		result = lappend(result, items[i].clause);

	return result;
}

static IndexOnlyScan *
make_indexonlyscan(List *qptlist,
				   List *qpqual,
				   Index scanrelid,
				   Oid indexid,
				   List *indexqual,
				   List *indexorderby,
				   List *indextlist,
				   ScanDirection indexscandir)
{
	IndexOnlyScan *node = makeNode(IndexOnlyScan);
	Plan	   *plan = &node->scan.plan;

	plan->targetlist = qptlist;
	plan->qual = qpqual;
	plan->lefttree = NULL;
	plan->righttree = NULL;
	node->scan.scanrelid = scanrelid;
	node->indexid = indexid;
	node->indexqual = indexqual;
	node->indexorderby = indexorderby;
	node->indextlist = indextlist;
	node->indexorderdir = indexscandir;

	return node;
}

static IndexScan *
make_indexscan(List *qptlist,
			   List *qpqual,
			   Index scanrelid,
			   Oid indexid,
			   List *indexqual,
			   List *indexqualorig,
			   List *indexorderby,
			   List *indexorderbyorig,
			   List *indexorderbyops,
			   ScanDirection indexscandir)
{
	IndexScan  *node = makeNode(IndexScan);
	Plan	   *plan = &node->scan.plan;

	plan->targetlist = qptlist;
	plan->qual = qpqual;
	plan->lefttree = NULL;
	plan->righttree = NULL;
	node->scan.scanrelid = scanrelid;
	node->indexid = indexid;
	node->indexqual = indexqual;
	node->indexqualorig = indexqualorig;
	node->indexorderby = indexorderby;
	node->indexorderbyorig = indexorderbyorig;
	node->indexorderbyops = indexorderbyops;
	node->indexorderdir = indexscandir;

	return node;
}

static void
copy_generic_path_info(Plan *dest, Path *src)
{
	dest->startup_cost = src->startup_cost;
	dest->total_cost = src->total_cost;
	dest->plan_rows = src->rows;
	dest->plan_width = src->pathtarget->width;
	dest->parallel_aware = src->parallel_aware;
	dest->parallel_safe = src->parallel_safe;
}

static Scan *
hybridquery_create_indexscan_plan(PlannerInfo *root,
					  IndexPath *best_path,
					  List *tlist,
					  List *scan_clauses,
					  bool indexonly)
{
	Scan	   *scan_plan;
	List	   *indexquals = best_path->indexquals;
	List	   *indexorderbys = best_path->indexorderbys;
	Index		baserelid = best_path->path.parent->relid;
	Oid			indexoid = best_path->indexinfo->indexoid;
	List	   *qpqual;
	List	   *stripped_indexquals;
	List	   *fixed_indexquals;
	List	   *fixed_indexorderbys;
	List	   *indexorderbyops = NIL;
	ListCell   *l;

	/* it should be a base rel... */
	Assert(baserelid > 0);
	Assert(best_path->path.parent->rtekind == RTE_RELATION);

	/*
	 * Build "stripped" indexquals structure (no RestrictInfos) to pass to
	 * executor as indexqualorig
	 */
	stripped_indexquals = get_actual_clauses(indexquals);

	/*
	 * The executor needs a copy with the indexkey on the left of each clause
	 * and with index Vars substituted for table ones.
	 */
	fixed_indexquals = fix_indexqual_references(root, best_path);

	/*
	 * Likewise fix up index attr references in the ORDER BY expressions.
	 */
	fixed_indexorderbys = fix_indexorderby_references(root, best_path);

	/*
	 * The qpqual list must contain all restrictions not automatically handled
	 * by the index, other than pseudoconstant clauses which will be handled
	 * by a separate gating plan node.  All the predicates in the indexquals
	 * will be checked (either by the index itself, or by nodeIndexscan.c),
	 * but if there are any "special" operators involved then they must be
	 * included in qpqual.  The upshot is that qpqual must contain
	 * scan_clauses minus whatever appears in indexquals.
	 *
	 * In normal cases simple pointer equality checks will be enough to spot
	 * duplicate RestrictInfos, so we try that first.
	 *
	 * Another common case is that a scan_clauses entry is generated from the
	 * same EquivalenceClass as some indexqual, and is therefore redundant
	 * with it, though not equal.  (This happens when indxpath.c prefers a
	 * different derived equality than what generate_join_implied_equalities
	 * picked for a parameterized scan's ppi_clauses.)
	 *
	 * In some situations (particularly with OR'd index conditions) we may
	 * have scan_clauses that are not equal to, but are logically implied by,
	 * the index quals; so we also try a predicate_implied_by() check to see
	 * if we can discard quals that way.  (predicate_implied_by assumes its
	 * first input contains only immutable functions, so we have to check
	 * that.)
	 *
	 * Note: if you change this bit of code you should also look at
	 * extract_nonindex_conditions() in costsize.c.
	 */
	qpqual = NIL;
	foreach(l, scan_clauses)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, l);

		if (rinfo->pseudoconstant)
			continue;			/* we may drop pseudoconstants here */
		if (list_member_ptr(indexquals, rinfo))
			continue;			/* simple duplicate */
		if (is_redundant_derived_clause(rinfo, indexquals))
			continue;			/* derived from same EquivalenceClass */
		if (!contain_mutable_functions((Node *) rinfo->clause) &&
			predicate_implied_by(list_make1(rinfo->clause), indexquals, false))
			continue;			/* provably implied by indexquals */
		qpqual = lappend(qpqual, rinfo);
	}

	/* Sort clauses into best execution order */
	qpqual = order_qual_clauses(root, qpqual);

	/* Reduce RestrictInfo list to bare expressions; ignore pseudoconstants */
	qpqual = extract_actual_clauses(qpqual, false);

	/*
	 * We have to replace any outer-relation variables with nestloop params in
	 * the indexqualorig, qpqual, and indexorderbyorig expressions.  A bit
	 * annoying to have to do this separately from the processing in
	 * fix_indexqual_references --- rethink this when generalizing the inner
	 * indexscan support.  But note we can't really do this earlier because
	 * it'd break the comparisons to predicates above ... (or would it?  Those
	 * wouldn't have outer refs)
	 */
	if (best_path->path.param_info)
	{
		stripped_indexquals = (List *)
			replace_nestloop_params(root, (Node *) stripped_indexquals);
		qpqual = (List *)
			replace_nestloop_params(root, (Node *) qpqual);
		indexorderbys = (List *)
			replace_nestloop_params(root, (Node *) indexorderbys);
	}

	/*
	 * If there are ORDER BY expressions, look up the sort operators for their
	 * result datatypes.
	 */
	if (indexorderbys)
	{
		ListCell   *pathkeyCell,
				   *exprCell;

		/*
		 * PathKey contains OID of the btree opfamily we're sorting by, but
		 * that's not quite enough because we need the expression's datatype
		 * to look up the sort operator in the operator family.
		 */
		Assert(list_length(best_path->path.pathkeys) == list_length(indexorderbys));
		forboth(pathkeyCell, best_path->path.pathkeys, exprCell, indexorderbys)
		{
			PathKey    *pathkey = (PathKey *) lfirst(pathkeyCell);
			Node	   *expr = (Node *) lfirst(exprCell);
			Oid			exprtype = exprType(expr);
			Oid			sortop;

			/* Get sort operator from opfamily */
			sortop = get_opfamily_member(pathkey->pk_opfamily,
										 exprtype,
										 exprtype,
										 pathkey->pk_strategy);
			if (!OidIsValid(sortop))
				elog(ERROR, "missing operator %d(%u,%u) in opfamily %u",
					 pathkey->pk_strategy, exprtype, exprtype, pathkey->pk_opfamily);
			indexorderbyops = lappend_oid(indexorderbyops, sortop);
		}
	}

	/* Finally ready to build the plan node */
	if (indexonly)
		scan_plan = (Scan *) make_indexonlyscan(tlist,
												qpqual,
												baserelid,
												indexoid,
												fixed_indexquals,
												fixed_indexorderbys,
												best_path->indexinfo->indextlist,
												best_path->indexscandir);
	else
		scan_plan = (Scan *) make_indexscan(tlist,
											qpqual,
											baserelid,
											indexoid,
											fixed_indexquals,
											stripped_indexquals,
											fixed_indexorderbys,
											indexorderbys,
											indexorderbyops,
											best_path->indexscandir);

	copy_generic_path_info(&scan_plan->plan, &best_path->path);

	return scan_plan;
}

/*
typedef struct IndexScan
{
	Scan		scan;
	Oid			indexid;		
	List	   *indexqual;		
	List	   *indexqualorig;	
	List	   *indexorderby;	
	List	   *indexorderbyorig;
	List	   *indexorderbyops;
	ScanDirection indexorderdir;
} IndexScan;
*/
/*
 * PlanHybridQueryPath
 */
static Plan *
PlanHybridQueryPath(PlannerInfo *root,
				 RelOptInfo *rel,
				 CustomPath *best_path,
				 List *tlist,
				 List *clauses,
				 List *custom_plans)
{
	CustomScan	*cscan = makeNode(CustomScan);
	IndexPath	*structured_ipath;
	IndexPath	*anns_ipath;
	IndexScan	*structured_indexscan;
	IndexScan	*anns_indexscan;

	structured_ipath = (IndexPath *) lfirst(list_head(best_path->custom_paths));
	anns_ipath = (IndexPath *) lfirst(list_tail(best_path->custom_private));

	
	structured_indexscan = (IndexScan *)hybridquery_create_indexscan_plan(root, structured_ipath, tlist, clauses, false);

	// 1. 以createplan.c中create_indexscan_plan函数的方式，调用make_indexscan创建Scan对象（实际上是Plan的子类），
	// make_indexscan函数需要的参数存放在CustomPath中，而CustomPath会在create_hybridquery_path被填充。
	
	anns_indexscan = (IndexScan *)hybridquery_create_indexscan_plan(root, anns_ipath, tlist, clauses, false);

	// 2. 填充CustomScan
	cscan->scan = anns_indexscan->scan;  // TODO: 基类的成员该使用什么值进行初始化？暂时使用的向量索引对应的IndexScan的基类进行初始化的
	NodeSetTag(cscan, T_CustomScan);
	cscan->flags = best_path->flags;
	cscan->custom_plans = list_make1(structured_indexscan);  // 保存结构化索引的IndexScan到CustomScan
	cscan->custom_private = list_make1(anns_indexscan);  // 保存IndexScan到CustomScan
	cscan->methods = &hybridquery_scan_methods;

	return &cscan->scan.plan;  // 其实就是返回CustomScan的指针，只是为了达到类似C++的多态效果
}

/*
 * CreateHybridQueryScanState
 */
static Node *
CreateHybridQueryScanState(CustomScan *custom_plan)
{
	HybridQueryState  *hqs = (HybridQueryState *)palloc0(sizeof(HybridQueryState));

	NodeSetTag(hqs, T_CustomScanState);
	hqs->css.flags = custom_plan->flags;
	hqs->css.methods = &hybridquery_exec_methods;

	hqs->quals_is = (IndexScan *) lfirst(list_head(custom_plan->custom_plans));
	hqs->anns_is = (IndexScan *) lfirst(list_head(custom_plan->custom_private));

	return (Node *)&hqs->css;
}

/*
typedef struct IndexScanState
{
	ScanState	ss;				// its first field is NodeTag
	ExprState  *indexqualorig;
	List	   *indexorderbyorig;
	ScanKey		iss_ScanKeys;
	int			iss_NumScanKeys;
	ScanKey		iss_OrderByKeys;
	int			iss_NumOrderByKeys;
	IndexRuntimeKeyInfo *iss_RuntimeKeys;
	int			iss_NumRuntimeKeys;
	bool		iss_RuntimeKeysReady;
	ExprContext *iss_RuntimeContext;
	Relation	iss_RelationDesc;
	IndexScanDesc iss_ScanDesc;

	// These are needed for re-checking ORDER BY expr ordering
	pairingheap *iss_ReorderQueue;
	bool		iss_ReachedEnd;
	Datum	   *iss_OrderByValues;
	bool	   *iss_OrderByNulls;
	SortSupport iss_SortSupport;
	bool	   *iss_OrderByTypByVals;
	int16	   *iss_OrderByTypLens;
	Size		iss_PscanLen;
} IndexScanState;
*/
typedef struct HybridQueryIndexScanState
{
	ExprState  *indexqualorig;
	List	   *indexorderbyorig;
	ScanKey		iss_ScanKeys;
	int			iss_NumScanKeys;
	ScanKey		iss_OrderByKeys;
	int			iss_NumOrderByKeys;
	IndexRuntimeKeyInfo *iss_RuntimeKeys;
	int			iss_NumRuntimeKeys;
	bool		iss_RuntimeKeysReady;
	ExprContext *iss_RuntimeContext;
	Relation	iss_RelationDesc;
	IndexScanDesc iss_ScanDesc;

	pairingheap *iss_ReorderQueue;
	bool		iss_ReachedEnd;
	Datum	   *iss_OrderByValues;
	bool	   *iss_OrderByNulls;
	SortSupport iss_SortSupport;
	bool	   *iss_OrderByTypByVals;
	int16	   *iss_OrderByTypLens;
	Size		iss_PscanLen;	
} HybridQueryIndexScanState;

/*
 * BeginHybridQueryScan
 */
static void
BeginHybridQueryScan(CustomScanState *css, EState *estate, int eflags)
{
	HybridQueryState  *hqs = (HybridQueryState *)css;

	hqs->quals_iss = (IndexScanState *) ExecInitNode(&(hqs->quals_is->scan.plan), estate, eflags);
	
	// 完成所提供的CustomScanState的初始化。标准的域已经被ExecInitCustomScan初始化，但是任何私有的域应该在这里被初始化。
	// 完成HybridQueryState中除CustomScanState的其他成员的初始化
	HybridQueryIndexScanState *indexstate = (HybridQueryIndexScanState *)((char *)hqs + offsetof(HybridQueryState, anns_iss));
	IndexScan *node = hqs->anns_is;  // IndexScan

	Relation	currentRelation;
	bool		relistarget;

	indexstate->indexqualorig =
		ExecInitQual(node->indexqualorig, (PlanState *) hqs);
	indexstate->indexorderbyorig =
		ExecInitExprList(node->indexorderbyorig, (PlanState *) hqs);
	
	if (eflags & EXEC_FLAG_EXPLAIN_ONLY)
		return;
	
	relistarget = ExecRelationIsTargetRelation(estate, node->scan.scanrelid);
	indexstate->iss_RelationDesc = index_open(node->indexid,
											  relistarget ? NoLock : AccessShareLock);

	/*
	 * Initialize index-specific scan state
	 */
	indexstate->iss_RuntimeKeysReady = false;
	indexstate->iss_RuntimeKeys = NULL;
	indexstate->iss_NumRuntimeKeys = 0;

	/*
	 * build the index scan keys from the index qualification
	 */
	ExecIndexBuildScanKeys((PlanState *) hqs,
						   indexstate->iss_RelationDesc,
						   node->indexqual,
						   false,
						   &indexstate->iss_ScanKeys,
						   &indexstate->iss_NumScanKeys,
						   &indexstate->iss_RuntimeKeys,
						   &indexstate->iss_NumRuntimeKeys,
						   NULL,	/* no ArrayKeys */
						   NULL);

	/*
	 * any ORDER BY exprs have to be turned into scankeys in the same way
	 */
	ExecIndexBuildScanKeys((PlanState *) hqs,
						   indexstate->iss_RelationDesc,
						   node->indexorderby,
						   true,
						   &indexstate->iss_OrderByKeys,
						   &indexstate->iss_NumOrderByKeys,
						   &indexstate->iss_RuntimeKeys,
						   &indexstate->iss_NumRuntimeKeys,
						   NULL,	/* no ArrayKeys */
						   NULL);

	/* Initialize sort support, if we need to re-check ORDER BY exprs */
	if (indexstate->iss_NumOrderByKeys > 0)
	{
		int			numOrderByKeys = indexstate->iss_NumOrderByKeys;
		int			i;
		ListCell   *lco;
		ListCell   *lcx;

		/*
		 * Prepare sort support, and look up the data type for each ORDER BY
		 * expression.
		 */
		Assert(numOrderByKeys == list_length(node->indexorderbyops));
		Assert(numOrderByKeys == list_length(node->indexorderbyorig));
		indexstate->iss_SortSupport = (SortSupportData *)
			palloc0(numOrderByKeys * sizeof(SortSupportData));
		indexstate->iss_OrderByTypByVals = (bool *)
			palloc(numOrderByKeys * sizeof(bool));
		indexstate->iss_OrderByTypLens = (int16 *)
			palloc(numOrderByKeys * sizeof(int16));
		i = 0;
		forboth(lco, node->indexorderbyops, lcx, node->indexorderbyorig)
		{
			Oid			orderbyop = lfirst_oid(lco);
			Node	   *orderbyexpr = (Node *) lfirst(lcx);
			Oid			orderbyType = exprType(orderbyexpr);
			Oid			orderbyColl = exprCollation(orderbyexpr);
			SortSupport orderbysort = &indexstate->iss_SortSupport[i];

			/* Initialize sort support */
			orderbysort->ssup_cxt = CurrentMemoryContext;
			orderbysort->ssup_collation = orderbyColl;
			/* See cmp_orderbyvals() comments on NULLS LAST */
			orderbysort->ssup_nulls_first = false;
			/* ssup_attno is unused here and elsewhere */
			orderbysort->ssup_attno = 0;
			/* No abbreviation */
			orderbysort->abbreviate = false;
			PrepareSortSupportFromOrderingOp(orderbyop, orderbysort);

			get_typlenbyval(orderbyType,
							&indexstate->iss_OrderByTypLens[i],
							&indexstate->iss_OrderByTypByVals[i]);
			i++;
		}

		/* allocate arrays to hold the re-calculated distances */
		indexstate->iss_OrderByValues = (Datum *)
			palloc(numOrderByKeys * sizeof(Datum));
		indexstate->iss_OrderByNulls = (bool *)
			palloc(numOrderByKeys * sizeof(bool));

		/* and initialize the reorder queue */
		// TODO: 现在暂时不用这个
		indexstate->iss_ReorderQueue = NULL;
	}

	if (indexstate->iss_NumRuntimeKeys != 0)
	{
		ExprContext *stdecontext = hqs->css.ss.ps.ps_ExprContext;

		ExecAssignExprContext(estate, &hqs->css.ss.ps);
		indexstate->iss_RuntimeContext = hqs->css.ss.ps.ps_ExprContext;
		hqs->css.ss.ps.ps_ExprContext = stdecontext;
	}
	else
	{
		indexstate->iss_RuntimeContext = NULL;
	}

	return;
}

typedef struct PGIVFPQScanOpaqueData
{
	MemoryContext scan_ctx;
	pairingheap *queue;
	ItemPointerData *quals_ipds;
	uint32 quals_ipds_cnt;
	bool first_call;
} PGIVFPQScanOpaqueData;
typedef PGIVFPQScanOpaqueData * PGIVFPQScanOpaque;

/*
 * HybridQueryAccess
 */
static TupleTableSlot *
HybridQueryAccess(CustomScanState *css)
{
	HybridQueryState  *hqs = (HybridQueryState *)css;
	HybridQueryIndexScanState *node = (HybridQueryIndexScanState *)((char *)hqs + offsetof(HybridQueryState, anns_iss));

	EState	   *estate;
	ExprContext *econtext;
	ScanDirection direction;
	IndexScanDesc scandesc;
	HeapTuple	tuple;
	TupleTableSlot *slot;

	TupleTableSlot *quals_slot;
	int quals_cnt = 0;

	// TODO:
	hqs->quals_iss->ss.ps.ps_ProjInfo = NULL;

	std::vector<ItemPointerData> ipd_vec;

	/*
	 * extract necessary information from index scan node
	 */
	estate = hqs->css.ss.ps.state;
	direction = estate->es_direction;
	// /* flip direction if this is an overall backward scan */
	// if (ScanDirectionIsBackward(((IndexScan *) node->ss.ps.plan)->indexorderdir))
	// {
	// 	if (ScanDirectionIsForward(direction))
	// 		direction = BackwardScanDirection;
	// 	else if (ScanDirectionIsBackward(direction))
	// 		direction = ForwardScanDirection;
	// }
	direction = NoMovementScanDirection;
	scandesc = node->iss_ScanDesc;
	econtext = hqs->css.ss.ps.ps_ExprContext;
	slot = hqs->css.ss.ss_ScanTupleSlot;

	if (scandesc == NULL)
	{
		/*
		 * We reach here if the index scan is not parallel, or if we're
		 * serially executing an index scan that was planned to be parallel.
		 */
		scandesc = index_beginscan(hqs->css.ss.ss_currentRelation,
								   node->iss_RelationDesc,
								   estate->es_snapshot,
								   node->iss_NumScanKeys,
								   node->iss_NumOrderByKeys);

		node->iss_ScanDesc = scandesc;

		/*
		 * If no run-time keys to calculate or they are ready, go ahead and
		 * pass the scankeys to the index AM.
		 */
		if (node->iss_NumRuntimeKeys == 0 || node->iss_RuntimeKeysReady)
			index_rescan(scandesc,
						 node->iss_ScanKeys, node->iss_NumScanKeys,
						 node->iss_OrderByKeys, node->iss_NumOrderByKeys);
	}

	// 获取结构化条件的结果
	// TODO: 把结构化条件的结果存放在opaque中，但是需要抽象出来作为基类，这样就不依赖某种特定的向量索引了，但所有向量索引的opaque都需要继承这个基类
	PGIVFPQScanOpaque so = (PGIVFPQScanOpaque)scandesc->opaque;
	if (so->first_call)
	{
		for (;;)
		{
			quals_slot = ExecProcNode(&(hqs->quals_iss->ss.ps));
			if (TupIsNull(quals_slot))
			{
				break;
			}
			else
			{
				ipd_vec.push_back(quals_slot->tts_tuple->t_self);
				quals_cnt++;
			}
		}
		elog(WARNING, "quals_cnt: %d", quals_cnt);

		MemoryContext old_ctx;

		old_ctx = MemoryContextSwitchTo(so->scan_ctx);
		ItemPointerData *quals_ipds = (ItemPointerData *) palloc0(sizeof(ItemPointerData) * quals_cnt);
		for (int i = 0; i < quals_cnt; i++)
			quals_ipds[i] = ipd_vec[i];
		
		so->quals_ipds = quals_ipds;
		so->quals_ipds_cnt = quals_cnt;

		MemoryContextSwitchTo(old_ctx);
	}

	/*
	 * ok, now that we have what we need, fetch the next tuple.
	 */
	while ((tuple = index_getnext(scandesc, direction)) != NULL)
	{
		CHECK_FOR_INTERRUPTS();

		/*
		 * Store the scanned tuple in the scan tuple slot of the scan state.
		 * Note: we pass 'false' because tuples returned by amgetnext are
		 * pointers onto disk pages and must not be pfree()'d.
		 */
		ExecStoreTuple(tuple,	/* tuple to store */
					   slot,	/* slot to store in */
					   scandesc->xs_cbuf,	/* buffer containing tuple */
					   false);	/* don't pfree */

		/*
		 * If the index was lossy, we have to recheck the index quals using
		 * the fetched tuple.
		 */
		if (scandesc->xs_recheck)
		{
			econtext->ecxt_scantuple = slot;
			if (!ExecQualAndReset(node->indexqualorig, econtext))
			{
				/* Fails recheck, so drop it and loop back for another */
				InstrCountFiltered2(node, 1);
				continue;
			}
		}

		return slot;
	}

	/*
	 * if we get here it means the index scan failed so we are at the end of
	 * the scan..
	 */
	node->iss_ReachedEnd = true;
	return ExecClearTuple(slot);
}

/*
 * HybridQueryRecheck
 */
static bool
HybridQueryRecheck(CustomScanState *node, TupleTableSlot *slot)
{
	// TODO:
	return true;
}

/*
 * ExecHybridQueryScan
 */
static TupleTableSlot *
ExecHybridQueryScan(CustomScanState *node)
{
	// accessMtd的执行方式与IndexNext函数相同，只是添加了对Filter的处理。（其实就是从IndexNext函数改写而来，如果不处理Filter，则执行过程与IndexNext函数完全相同）
	// 1. accessMtd参数所指向的函数中，添加对Filter的处理，得到结构化条件的结果，然后将结构化条件得到的结果传入scandesc的opaque中，
	//    在向量搜索扩展中会对opaque中的结构化条件的结果进行处理；
	// 2. recheckMtd暂无其他处理，返回true。
	return ExecScan(&node->ss,
					(ExecScanAccessMtd) HybridQueryAccess,
					(ExecScanRecheckMtd) HybridQueryRecheck);
}

/*
 * EndHybridQueryScan
 */
static void
EndHybridQueryScan(CustomScanState *node)
{
	HybridQueryState *hqs = (HybridQueryState *)node;

	// 对比nodeCustom.c的ExecEndCustomScan函数和nodeIndexscan.c的ExecEndIndexScan函数，按照后者的处理方式，完成本函数。
	Relation	indexRelationDesc;
	IndexScanDesc indexScanDesc;
	Relation	relation;

	/*
	 * extract information from the node
	 */
	indexRelationDesc = hqs->iss_RelationDesc;
	indexScanDesc = hqs->iss_ScanDesc;
	relation = hqs->css.ss.ss_currentRelation;

	/*
	 * close the index relation (no-op if we didn't open it)
	 */
	if (indexScanDesc)
		index_endscan(indexScanDesc);
	// if (indexRelationDesc)
	// 	index_close(indexRelationDesc, NoLock);

	ExecEndNode(&(hqs->quals_iss->ss.ps));
}

/*
 * ReScanHybridQueryScan
 */
static void
ReScanHybridQueryScan(CustomScanState *node)
{
	HybridQueryState *hqs = (HybridQueryState *)node;
	// 对比nodeCustom.c的ExecReScanCustomScan函数和nodeIndexscan.c的ExecReScanIndexScan函数，按照后者的处理方式，完成本函数。
	if (hqs->iss_NumRuntimeKeys != 0)
	{
		ExprContext *econtext = hqs->iss_RuntimeContext;

		ResetExprContext(econtext);
		ExecIndexEvalRuntimeKeys(econtext,
								 hqs->iss_RuntimeKeys,
								 hqs->iss_NumRuntimeKeys);
	}
	hqs->iss_RuntimeKeysReady = true;

	/* flush the reorder queue */
	if (hqs->iss_ReorderQueue)
	{
		// TODO: 现在暂时不用这个
	}

	/* reset index scan */
	if (hqs->iss_ScanDesc)
		index_rescan(hqs->iss_ScanDesc,
					 hqs->iss_ScanKeys, hqs->iss_NumScanKeys,
					 hqs->iss_OrderByKeys, hqs->iss_NumOrderByKeys);
	hqs->iss_ReachedEnd = false;

	ExecScanReScan(&hqs->css.ss);
}

/*
 * ExplainCtidScan - A method of CustomScanState; that shows extra info
 * on EXPLAIN command.
 */
static void
ExplainHybridQueryScan(CustomScanState *node, List *ancestors, ExplainState *es)
{
	// TODO:
	return;
}

/*
 * Entrypoint of this extension
 */
void
_PG_init(void)
{
	DefineCustomBoolVariable("enable_hybridquery",
							 "Enables the planner's use of hybrid-query plans.",
							 NULL,
							 &enable_hybridquery,
							 true,
							 PGC_USERSET,
							 GUC_NOT_IN_SAMPLE,
							 NULL, NULL, NULL);
	
	// 计算distance tables和一条pq code之间的距离的cost
	DefineCustomRealVariable("cost_from_distance_tables",
							 "Cost of compute distance from distance tables",
							 NULL,
							 &cost_from_distance_tables,
							 DEFAULT_CPU_OPERATOR_COST / 32.0,
							 0,
							 DBL_MAX,
							 PGC_USERSET,
							 GUC_NOT_IN_SAMPLE,
							 NULL, NULL, NULL);

	// 计算索引中任意一条pq code与一个原始向量之间的距离的cost
	DefineCustomRealVariable("cost_from_two_codes",
							 "Cost of compute distance from two codes",
							 NULL,
							 &cost_from_two_codes,
							 DEFAULT_CPU_OPERATOR_COST / 16.0,
							 0,
							 DBL_MAX,
							 PGC_USERSET,
							 GUC_NOT_IN_SAMPLE,
							 NULL, NULL, NULL);

	/* registration of the hook to add alternative path */
	set_rel_pathlist_next = set_rel_pathlist_hook;
	set_rel_pathlist_hook = set_hybridquery_path;
}

void _PG_fini(void)
{
	set_rel_pathlist_hook = NULL;
}

#ifdef __cplusplus
}
#endif