#include <vector>
#include <chrono>

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
#include "utils/datum.h"
#include "utils/elog.h"

#include <math.h>

PG_MODULE_MAGIC;

/*
 * HybridQueryState
 */
typedef struct {
	CustomScanState		css;
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

	index_clauses = NIL;
	clause_columns = NIL;
	for (indexcol = 0; indexcol < index->ncolumns; indexcol++)
	{
		ListCell   *lc;

		foreach (lc, clauseset->indexclauses[indexcol])
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			index_clauses = lappend(index_clauses, rinfo);
			clause_columns = lappend_int(clause_columns, indexcol);
		}

		if (index_clauses == NIL && !index->amoptionalkey)
			return NULL;
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
	// TODO: 创建路径需要自己实现，pathtarget和代价都要自己计算
	ipath = create_index_path(root, index,
							index_clauses,
							clause_columns,
							NIL,
							NIL,
							useful_pathkeys,
							ForwardScanDirection,	// ForwardScanDirection
							false,					// T_IndexScan
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
		return NIL;

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
		 * 对于一个非局部索引（non-partial index），
		 * 每个IndexOptInfo里面的indrestrictinfo成员和
		 * RelOptInfo的baserestrictinfo成员都指向同一个值，
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
		index_paths = lappend(index_paths, index_path);
	}

	return index_paths;
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
		return NIL;

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
		if (orderbyclauses == NIL || \
			orderbyclausecols == NIL)
			continue;
		
		// TODO: 创建路径需要自己实现，pathtarget和代价都要自己计算
		index_path = create_anns_index_path(root, index, orderbyclauses, orderbyclausecols);
		index_paths = lappend(index_paths, index_path);
	}

	return index_paths;
}

// static void
// estimate_cost_for_ivfpq(IndexPath *best_structured_index_path, IndexPath *best_anns_index_path,
// 						Cost *hybrid_cost, Cost *not_hybrid_cost)
// {
// 	/* 向量索引+结构化过滤的代价 */
// 	int32 n = 1000000;
// 	int32 ni = 64;
// 	Cost anns_structured_cost;
// 	Cost structured_anns_cost;
// 	anns_structured_cost = (128.0 / 512.0) * n * cost_from_distance_tables;
// 	structured_anns_cost = best_structured_index_path->indextotalcost + best_selectivity * n * cost_from_distance_tables;

// 	/* 结构化+向量索引的代价 */
// 	Cost anns_structured_anns_io_cost;
// 	Cost structured_anns_anns_io_cost;
// 	anns_structured_anns_io_cost = (128.0 / 512.0) * ((float)n / ni) * DEFAULT_SEQ_PAGE_COST;
// 	structured_anns_anns_io_cost = best_selectivity * n * DEFAULT_RANDOM_PAGE_COST;

// 	anns_structured_cost += anns_structured_anns_io_cost;
// 	structured_anns_cost += structured_anns_anns_io_cost;
// }

typedef struct PGIVFPQPageOpaqueData
{
	uint16 flag;
	OffsetNumber max_offset;
	BlockNumber next_page_blkno;
} PGIVFPQPageOpaqueData;

typedef struct PGIVFPQIVFCentroidTuple
{
	// TODO: FLEXIBLE_ARRAY_MEMBER
	float centroid[512];
	BlockNumber data_entry_blkno;
} PGIVFPQIVFCentroidTuple;

typedef struct PGIVFPQPQCentroidTuple
{
	// TODO: FLEXIBLE_ARRAY_MEMBER
	float centroid[4*256];
} PGIVFPQPQCentroidTuple;

typedef struct PGIVFPQDataTuple
{
	// TODO: FLEXIBLE_ARRAY_MEMBER
	ItemPointerData ipd;
	uint8 pq_code[128];	
} PGIVFPQDataTuple;

static Cost
estimate_hybrid_ivfpq_cost(IndexPath *index_path, Selectivity selectivity)
{
	IndexOptInfo *index_path = path->indexinfo;
	GenericCosts costs;

	/* 
	 * IVFPQ算法在搜索过程中，计算向量之间的距离时，有2种向量形式：
	 * 1. 计算两个原始向量之间的距离（使用情况：搜索最近的IVF。）；
	 * 2. 计算两个原始向量的pq码之间的距离（使用情况：扫描IVF。有两种方式：通过distance table计算；直接计算。
	 *    哪种方式速度较快，与底库大小和搜索参数nprobe有关，需要进一步测试。）。
	 * 3. 计算pq centroid与residual各个子段之间的距离（使用情况：计算distance table。）
	 * 因此，计算一次两个向量之间的距离，有4种代价参数。
	 */

	Cost io_cost = 0.0;
	Cost cpu_cost = 0.0;
	Cost run_cost = 0.0;

	int32 io_cnt = 0;
	int32 compute_raw_distance_cnt = 0;
	// TODO: 在扫描IVF，这里暂时只考虑通过distance table计算这种方式的代价。
	int32 compute_dt_distance_cnt = 0;
	// int32 compute_pq_distance_cnt = 0;
	int32 compute_pq_centroid_and_residual_sub_cnt = 0;

	/* 
	 * NOTE:
	 * 现在的代价计算，只能用于与联合查询的向量搜索的代价比较，
	 * 而不能用于与暴力搜索的代价比较，原因如下：
	 * 1. 暴力搜索的距离计算（两个feature之间）与向量搜索的距离计算（两个feature的pq码之间），
	 *    没有在同一操作符下进行比较（可通过设置不同的代价参数解决）；
	 * 2. 通过向量索引进行搜索时，会计算投影列上的代价，其中包括投影列上的表达式的代价，这里的表达式也包括操作符，
	 *    操作符表达式的代价即为定义操作符对应的函数时指定的代价（与暴力搜索时的表达式代价一样），
	 *    这部分代价为set_baserel_size_estimates函数中估计的行数x操作符表达式代价，但这里的函数估计，是从其他表达式中估计出来的，
	 *    不包括索引对应的表达式（比如一般向量索引会返回TopK个数据，总共TopK行），
	 *    因此这部分代价的大小是不定的，且不能通过索引扩展估计出来（暂时无法在向量索引的搜索时去掉操作符表达式代价，无法解决）。
	 * 3. 使用向量索引进行搜索时，ExecProject函数里面会执行操作符对应的函数，但操作符底层的函数，是直接从缓存result_distances中获取结果的，
	 *    因此操作符表达式的代价在向量索引的搜索中是多估计出来的，如果与暴力搜索的代价比较，
	 *    会导致不能正确选择较好的查询计划（暂时无法在向量索引的搜索时去掉操作符表达式代价，无法解决）。
	 */

	/*
	 * NOTE:
	 * 1、搜索过程中的最大堆排序的CPU代价暂时忽略；
	 * 2、搜索过程中的计算residuals的CPU代价暂时忽略；
	 * 3、搜索过程中打开索引元页的IO代价暂时忽略;
	 * 4、搜索过程中对查询向量进行解密的代价直接忽略，因为不管哪种方式的搜索方式都需要对查询向量进行解密，但暴力搜索还需要对底库向量进行解密。
	 */

	/* 
	 * TODO:
	 * 1. 获取索引创建的相关参数（dimension、ivf num、pq num、pq centroid num）和索引搜索的相关参数（nprobe）;
	 * 2. 获取索引数量。
	 */
	uint32 ivf_dim;
	uint32 ivf_centroid_num;
	uint32 pq_sub_dim;
	uint32 pq_sub_num;
	uint32 pq_per_sub_centroid_num;

	ivf_dim = 512;
	ivf_centroid_num = 512;
	pq_sub_dim = 4;
	pq_sub_num = 128;
	pq_per_sub_centroid_num = 256;

	int32 nprobe = 128;
	int32 ntotal = 1000000;
	int32 numIndexTuples = 512;

	Size page_sz = BLCKSZ;
	Size page_opaque_sz = MAXALIGN(sizeof(PGIVFPQPageOpaqueData));
	Size ivf_ctup_sz = MAXALIGN(sizeof(PGIVFPQIVFCentroidTuple));
	Size pq_ctup_sz = MAXALIGN(sizeof(PGIVFPQPQCentroidTuple));
	Size dtup_sz = MAXALIGN(sizeof(PGIVFPQDataTuple));

	int32 per_page_ivf_ctup_num = (page_sz - page_opaque_sz) / ivf_ctup_sz;
	int32 per_page_pq_ctup_num = (page_sz - page_opaque_sz) / pq_ctup_sz;
	int32 per_page_dtup_num = (page_sz - page_opaque_sz) / dtup_sz;

	elog(WARNING, "\npage_sz: %d,\npage_opaque_sz: %d,\nivf_ctup_sz: %d,\npq_ctup_sz: %d,\ndtup_sz: %d",
					page_sz, page_opaque_sz, ivf_ctup_sz, pq_ctup_sz, dtup_sz);
	
	elog(WARNING, "\nper_page_ivf_ctup_num: %d,\nper_page_pq_ctup_num: %d,\nper_page_dtup_num: %d",
					per_page_ivf_ctup_num, per_page_pq_ctup_num, per_page_dtup_num);

	/* IO cost: a. 搜索最近的IVF；b. compute residuals；c. 计算distance_table；d. 扫描IVF。 */
	io_cnt += ceil((float) ivf_centroid_num / per_page_ivf_ctup_num);
	io_cnt += nprobe;
	io_cnt += ceil((float) pq_sub_num / per_page_pq_ctup_num);
	/* NOTE: 每个IVF的数据量与数据分布有关，因此这里对IVF扫描的IO次数不能确定，这里的估计假设数据是均匀分布的，每个IVF的数据量一致。
	 * TODO: 在索引元页里面添加对每个IVF的统计信息。
	 */
	io_cnt += ceil(selectivity * ntotal);

	elog(WARNING, "\nivf io: %d,\nresiduals io: %d,\ndistance tables io: %d,\nscan ivf io: %d",
					(int32) ceil((float) ivf_centroid_num / per_page_ivf_ctup_num),
					nprobe,
					(int32) ceil((float) pq_sub_num / per_page_pq_ctup_num),
					(int32) ceil((float) nprobe / ivf_centroid_num * ntotal / per_page_dtup_num));

	/* CPU cost: a. 搜索最近的IVF（没有CPU cost）；b. compute residuals（没有CPU cost）；c. 计算distance_table（没有CPU cost）；d. 扫描IVF。 */
	/* FIXME: 现在CPU cost只计算通过distance_table进行距离计算的次数。 */
	/* NOTE: 每个IVF的数据量与数据分布有关，因此这里对IVF扫描的IO次数不能确定，这里的估计假设数据是均匀分布的，每个IVF的数据量一致。 */
	compute_raw_distance_cnt += ivf_centroid_num;
	compute_pq_centroid_and_residual_sub_cnt += (pq_per_sub_centroid_num * pq_sub_num) * nprobe;
	compute_dt_distance_cnt += ceil(selectivity * ntotal);

	/* TODO: 获取cost_from_distance_tables */
	double cost_from_raw = DEFAULT_CPU_OPERATOR_COST * 20.0;
	// double cost_from_pq = DEFAULT_CPU_OPERATOR_COST * 1000.0;
	double cost_from_dt = DEFAULT_CPU_OPERATOR_COST * 10.0;
	double cost_from_pq_centroid_and_residual_sub = DEFAULT_CPU_OPERATOR_COST * 20.0 * ((double) pq_sub_dim / ivf_dim);

	io_cost = io_cnt * DEFAULT_SEQ_PAGE_COST;
	cpu_cost = compute_raw_distance_cnt * cost_from_raw + \
			   compute_pq_centroid_and_residual_sub_cnt * cost_from_pq_centroid_and_residual_sub + \
			   compute_dt_distance_cnt * cost_from_dt;

	Cost op_evaluate_cost = DEFAULT_CPU_OPERATOR_COST * 5000.0 * path->path.parent->rows;
	elog(WARNING, "baserel->rows: %f, op_evaluate_cost: %f", path->path.parent->rows, op_evaluate_cost);

	elog(WARNING, "\nio_cnt: %d, io_cost: %f,"
				   "\nraw: %d, cost: %f,"
				   "\npq centroid and residual sub: %d, cost: %f,"
				   "\ndt: %d, cost: %f,"
				   "\ncpu_cost: %f",
		 io_cnt, io_cost,
		 compute_raw_distance_cnt, compute_raw_distance_cnt * cost_from_raw,
		 compute_pq_centroid_and_residual_sub_cnt, compute_pq_centroid_and_residual_sub_cnt * cost_from_pq_centroid_and_residual_sub,
		 compute_dt_distance_cnt, compute_dt_distance_cnt * cost_from_dt,
		 cpu_cost);

	run_cost += numIndexTuples * cpu_index_tuple_cost;

	elog(WARNING, "run_cost: %f", run_cost);

	costs.indexStartupCost = io_cost + cpu_cost;
	costs.indexTotalCost = io_cost + cpu_cost + run_cost;
	costs.indexSelectivity = min(selectivity, (double) numIndexTuples / ntotal);


	return 
}

static bool
find_best_paths(List *structured_index_paths, List *anns_index_paths,
				IndexPath **p_best_structured_index_path, IndexPath **p_best_anns_index_path)
{
	bool		 use_hybridquery = false;
	IndexPath	*best_structured_index_path = NULL;
	IndexPath	*best_anns_index_path = NULL;
	ListCell	*lc;

	Cost hybrid_cost;
	Cost not_hybrid_cost;

	Selectivity min_selectivity = 1.0;
	Cost		min_anns_cost = disable_cost;

	/* 
	 * NOTE:
	 * 这里只关注选择率，因为要通过结构化索引的结果去优化向量索引的搜索，
	 * 结构化索引的选择率越低，向量索引的搜索越快。
	 */
	foreach (lc, structured_index_paths)
	{
		IndexPath *index_path = (IndexPath *)lfirst(lc);
		if (min_selectivity > index_path->indexselectivity)
		{
			min_selectivity = index_path->indexselectivity;
			best_structured_index_path = index_path;
		}
	}

	/* 
	 * NOTE:
	 * 最优的结构化索引的选择规则为选择率最低，但是最优的向量索引的选择规则
	 * 需要根据结构化索引的选择率来判断，比如pg_ivfpq索引的搜索能够通过结构化索引
	 * 进行加速，但是pg_hnsw索引的搜索很难通过结构化索引进行加速。
	 */
	
	foreach (lc, anns_index_paths)
	{
		IndexPath *index_path = (IndexPath *)lfirst(lc);
		Name amname = GetIndexAmNameByAmOid(index_path->indexinfo->relam, false);
		Cost anns_cost;
		if (strcmp("pg_ivfpq", amname->data) == 0)
		{
			anns_cost = estimate_hybrid_ivfpq_cost(index_path, min_selectivity);
		}
		else
		{
			// TODO:
		}

		if (min_anns_cost > anns_cost)
		{
			min_anns_cost = anns_cost;
			best_anns_index_path = index_path;
		}
	}

	hybrid_cost = best_structured_index_path->indextotalcost + min_anns_cost;
	/* 
	 * TODO:
	 * 得到非联合查询的代价：直接使用向量索引的代价作为非联合查询的代价，
	 * 现在向量索引的amcostestimate函数还未实现，暂时在此处进行估计。
	 * 事实上，这里不需要计算非联合查询的代价，只需要计算联合查询的代价，
	 * 然后更新联合查询下向量索引的代价即可，PostgreSQL的查询规划模块会
	 * 自动选择代价最低的路径。
	 */
	int32 n = 1000000;
	int32 ni = 64;
	not_hybrid_cost = (128.0 / 512.0) * n * cost_from_distance_tables /* cpu cost */ + \
					  (128.0 / 512.0) * ((float)n / ni) * DEFAULT_SEQ_PAGE_COST /* io cost */;
	
	if (hybrid_cost < not_hybrid_cost)
		use_hybridquery = true;
	
	/* 更新联合查询下向量索引的代价 */

	best_anns_index_path->indextotalcost = min_anns_cost;
	// best_anns_index_path->indextotalcost = 0.0;

	/* 
	 * NOTE:
	 * 只要满足联合查询的条件，就会提供联合查询的查询路径，
	 * 是否使用联合查询，PostgreSQL会自动进行选择。
	 */
	*p_best_structured_index_path = best_structured_index_path;
	*p_best_anns_index_path = best_anns_index_path;

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
	IndexPath	*best_structured_index_path = NULL;
	IndexPath	*best_anns_index_path = NULL;
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
	if (structured_index_paths == NIL || \
		structured_index_paths->length == 0)
		return;
	
	// 4. 向量索引
	anns_index_paths = find_anns_index_paths(root, baserel);
	if (anns_index_paths == NIL || \
		anns_index_paths->length == 0)
		return;
	
	// 5. 联合查询的代价比非联合查询的代价低
	use_hybridquery = find_best_paths(structured_index_paths, anns_index_paths,
									  &best_structured_index_path, &best_anns_index_path);
	// 是否进行联合查询，不使用联合查询则直接返回，此时会使用PostgreSQL规划的路径。
	if (!use_hybridquery)
		elog(INFO, "Cost of hybrid query is greater than cost of ANNS + Filter");

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
	cpath->path.startup_cost = best_structured_index_path->indextotalcost + best_anns_index_path->indextotalcost;
	cpath->path.total_cost = best_anns_index_path->indextotalcost;
	// cpath->path.startup_cost = 0.0;
	// cpath->path.total_cost = 0.0;

	cpath->path.pathkeys = root->query_pathkeys;

	cpath->flags = 0;
	cpath->custom_paths = NIL;  // 内部会遍历这个列表，然后根据查询路径生成对应的查询计划，
								// 然后传给PlanCustomPath变量，此处希望全部执行过程都由本扩展掌控，
								// 因此把结构化索引和向量索引生成的查询路径放到custom_private中。
	cpath->custom_private = list_make2(best_structured_index_path, best_anns_index_path);
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
create_structured_is_plan(PlannerInfo *root,
					  IndexPath *best_path,
					  List *tlist)
{
	Scan	   *scan_plan;
	List	   *indexquals = best_path->indexquals;
	Index		baserelid = best_path->path.parent->relid;
	Oid			indexoid = best_path->indexinfo->indexoid;
	List	   *qpqual;
	List	   *stripped_indexquals;
	List	   *fixed_indexquals;
	ListCell   *l;

	/* scan_clauses直接使用索引路径的IndexOptInfo->indrestrictinfo变量加上参数化条件 */
	List *scan_clauses = best_path->indexinfo->indrestrictinfo;
	if (best_path->path.param_info)
		scan_clauses = list_concat(list_copy(scan_clauses),
								   best_path->path.param_info->ppi_clauses);

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
	}

	/* 对于联合查询中的结构化索引，因为是创建IndexOnlyScan，因此不需要得到对应的索引列，
	 * 只需要得到ItemPoinerData，因此tlist直接设置为空。
	 */
	scan_plan = (Scan *) make_indexscan(tlist,
										qpqual,
										baserelid,
										indexoid,
										fixed_indexquals,
										stripped_indexquals,
										NIL,
										NIL,
										NIL,
										best_path->indexscandir);
	// scan_plan = (Scan *) make_indexscan(NIL,
	// 										qpqual,
	// 										baserelid,
	// 										indexoid,
	// 										fixed_indexquals,
	// 										NIL,
	// 										best_path->indexinfo->indextlist,
	// 										best_path->indexscandir);

	copy_generic_path_info(&scan_plan->plan, &best_path->path);

	return scan_plan;
}

static Scan *
create_anns_is_plan(PlannerInfo *root,
					  IndexPath *best_path,
					  List *tlist,
					  List *scan_clauses)
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

static CustomScan *
create_customscan_plan(IndexScan *structured_is, IndexScan *anns_is)
{
	CustomScan	*cscan = makeNode(CustomScan);

	cscan->scan.plan.startup_cost = structured_is->scan.plan.total_cost + anns_is->scan.plan.startup_cost;
	cscan->scan.plan.total_cost = structured_is->scan.plan.total_cost + anns_is->scan.plan.total_cost;
	cscan->scan.plan.plan_rows = anns_is->scan.plan.plan_rows;
	cscan->scan.plan.plan_width = anns_is->scan.plan.plan_width;
	cscan->scan.plan.parallel_aware = false;
	cscan->scan.plan.parallel_safe = false;
	cscan->scan.plan.plan_node_id = anns_is->scan.plan.plan_node_id;  // TODO:
	cscan->scan.plan.targetlist = anns_is->scan.plan.targetlist;
	cscan->scan.plan.qual = anns_is->scan.plan.qual;
	cscan->scan.plan.lefttree = (Plan *)structured_is;
	cscan->scan.plan.righttree = (Plan *)anns_is;
	cscan->scan.plan.initPlan = NIL;
	cscan->scan.plan.extParam = NULL;
	cscan->scan.plan.allParam = NULL;

	cscan->scan.scanrelid = anns_is->scan.scanrelid;  // TODO: 直接使用PlanCustomPath函数的RelOptInfo参数中的relid进行初始化

	cscan->flags = 0;
	cscan->custom_plans = NIL;  // 同CustomPath
	cscan->custom_exprs = NIL;
	cscan->custom_private = NIL;
	cscan->custom_scan_tlist = NIL;
	cscan->custom_relids = NULL;
	cscan->methods = &hybridquery_scan_methods;

	return cscan;
}

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
	CustomScan	*cscan;
	IndexPath	*structured_ipath;
	IndexPath	*anns_ipath;
	IndexScan	*structured_is;
	IndexScan	*anns_is;

	structured_ipath = (IndexPath *) lfirst(list_head(best_path->custom_private));
	anns_ipath = (IndexPath *) lfirst(list_tail(best_path->custom_private));

	/* 
	 * 结构化索引对应的查询计划
	 */
	structured_is = (IndexScan *)create_structured_is_plan(root, structured_ipath, tlist);

	/* 
	 * 向量索引对应的查询计划
	 * NOTE:
	 * 现阶段，向量索引对应的查询计划是自定义查询计划的实际执行者，只是在执行向量索引之前，
	 * 自定义查询计划会先执行结构化索引对应的查询计划，再将其输出传给向量索引对应的查询计划，此后，
	 * 自定义查询计划的实际工作者就变成了向量索引对应的查询计划，完成查询，投影，条件过滤，排序等功能。
	 */
	anns_is = (IndexScan *)create_anns_is_plan(root, anns_ipath, tlist, clauses);

	/* 
	 * 填充CustomScan
	 * NOTE:
	 * CustomScan->scan.plan中的大部分内容从向量索引对应的查询计划得到。
	 */
	cscan = create_customscan_plan(structured_is, anns_is);

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
	hqs->css.custom_ps = NIL;
	hqs->css.pscan_len = 0;
	hqs->css.methods = &hybridquery_exec_methods;

	return (Node *)&hqs->css;
}

static IndexScanState *
init_structured_iss(IndexScan *node, EState *estate, int eflags)
{
	IndexScanState *indexstate;
	indexstate = (IndexScanState *) ExecInitNode(&(node->scan.plan), estate, eflags);
	indexstate->ss.ps.ps_ProjInfo = NULL;
	return indexstate;

	// IndexScanState *indexstate;
	// Relation	currentRelation;
	// bool		relistarget;

	// /*
	//  * create state structure
	//  */
	// indexstate = makeNode(IndexScanState);
	// indexstate->ss.ps.plan = (Plan *) node;
	// indexstate->ss.ps.state = estate;
	// indexstate->ss.ps.ExecProcNode = ExecHybridQueryStructuredScan;  // TODO:

	// /*
	//  * Miscellaneous initialization
	//  *
	//  * create expression context for node
	//  */
	// ExecAssignExprContext(estate, &indexstate->ss.ps);

	// /*
	//  * open the base relation and acquire appropriate lock on it.
	//  */
	// currentRelation = ExecOpenScanRelation(estate, node->scan.scanrelid, eflags);

	// indexstate->ss.ss_currentRelation = currentRelation;
	// indexstate->ss.ss_currentScanDesc = NULL;	/* no heap scan here */

	// // NOTE: 不会用到ss.ss_ScanTupleSlot，但是也要分配内存，ExecScanReScan函数里面会销毁它，
	// // 如果不分配内存，该函数会执行出错。
	// /*
	//  * get the scan type from the relation descriptor.
	//  */
	// ExecInitScanTupleSlot(estate, &indexstate->ss,
	// 					  RelationGetDescr(currentRelation));

	// // NOTE: 不会用到ss.ps.ps_ResultTupleSlot，但是也要分配内存，ExecEndIndexScan函数里面会销毁它，
	// // 如果不分配内存，该函数会执行出错。
	// /*
	//  * Initialize result slot, type and projection.
	//  */
	// ExecInitResultTupleSlotTL(estate, &indexstate->ss.ps);
	// // ExecAssignScanProjectionInfo(&indexstate->ss);
	// indexstate->ss.ps.ps_ProjInfo = NULL;


	// // NOTE: IndexScan中对应的字段为NIL，则ExecInitQual会返回NULL，ExecInitExprList会返回NIL。因此此处可以不用处理。
	// /*
	//  * initialize child expressions
	//  *
	//  * Note: we don't initialize all of the indexqual expression, only the
	//  * sub-parts corresponding to runtime keys (see below).  Likewise for
	//  * indexorderby, if any.  But the indexqualorig expression is always
	//  * initialized even though it will only be used in some uncommon cases ---
	//  * would be nice to improve that.  (Problem is that any SubPlans present
	//  * in the expression must be found now...)
	//  */
	// indexstate->ss.ps.qual =
	// 	ExecInitQual(node->scan.plan.qual, (PlanState *) indexstate);
	// indexstate->indexqualorig =
	// 	ExecInitQual(node->indexqualorig, (PlanState *) indexstate);
	// indexstate->indexorderbyorig =
	// 	ExecInitExprList(node->indexorderbyorig, (PlanState *) indexstate);

	// /*
	//  * If we are just doing EXPLAIN (ie, aren't going to run the plan), stop
	//  * here.  This allows an index-advisor plugin to EXPLAIN a plan containing
	//  * references to nonexistent indexes.
	//  */
	// if (eflags & EXEC_FLAG_EXPLAIN_ONLY)
	// 	return indexstate;

	// /*
	//  * Open the index relation.
	//  *
	//  * If the parent table is one of the target relations of the query, then
	//  * InitPlan already opened and write-locked the index, so we can avoid
	//  * taking another lock here.  Otherwise we need a normal reader's lock.
	//  */
	// relistarget = ExecRelationIsTargetRelation(estate, node->scan.scanrelid);
	// indexstate->iss_RelationDesc = index_open(node->indexid,
	// 										  relistarget ? NoLock : AccessShareLock);

	// /*
	//  * Initialize index-specific scan state
	//  */
	// indexstate->iss_RuntimeKeysReady = false;
	// indexstate->iss_RuntimeKeys = NULL;
	// indexstate->iss_NumRuntimeKeys = 0;

	// /*
	//  * build the index scan keys from the index qualification
	//  */
	// ExecIndexBuildScanKeys((PlanState *) indexstate,
	// 					   indexstate->iss_RelationDesc,
	// 					   node->indexqual,
	// 					   false,
	// 					   &indexstate->iss_ScanKeys,
	// 					   &indexstate->iss_NumScanKeys,
	// 					   &indexstate->iss_RuntimeKeys,
	// 					   &indexstate->iss_NumRuntimeKeys,
	// 					   NULL,	/* no ArrayKeys */
	// 					   NULL);

	// // TODO: 只需要iss_ScanKeys，不需要iss_OrderByKeys
	// /*
	//  * any ORDER BY exprs have to be turned into scankeys in the same way
	//  */
	// ExecIndexBuildScanKeys((PlanState *) indexstate,
	// 					   indexstate->iss_RelationDesc,
	// 					   node->indexorderby,
	// 					   true,
	// 					   &indexstate->iss_OrderByKeys,
	// 					   &indexstate->iss_NumOrderByKeys,
	// 					   &indexstate->iss_RuntimeKeys,
	// 					   &indexstate->iss_NumRuntimeKeys,
	// 					   NULL,	/* no ArrayKeys */
	// 					   NULL);

	// // TODO: 这里不用处理
	// /* Initialize sort support, if we need to re-check ORDER BY exprs */
	// if (indexstate->iss_NumOrderByKeys > 0)
	// {
	// 	int			numOrderByKeys = indexstate->iss_NumOrderByKeys;
	// 	int			i;
	// 	ListCell   *lco;
	// 	ListCell   *lcx;

	// 	/*
	// 	 * Prepare sort support, and look up the data type for each ORDER BY
	// 	 * expression.
	// 	 */
	// 	Assert(numOrderByKeys == list_length(node->indexorderbyops));
	// 	Assert(numOrderByKeys == list_length(node->indexorderbyorig));
	// 	indexstate->iss_SortSupport = (SortSupportData *)
	// 		palloc0(numOrderByKeys * sizeof(SortSupportData));
	// 	indexstate->iss_OrderByTypByVals = (bool *)
	// 		palloc(numOrderByKeys * sizeof(bool));
	// 	indexstate->iss_OrderByTypLens = (int16 *)
	// 		palloc(numOrderByKeys * sizeof(int16));
	// 	i = 0;
	// 	forboth(lco, node->indexorderbyops, lcx, node->indexorderbyorig)
	// 	{
	// 		Oid			orderbyop = lfirst_oid(lco);
	// 		Node	   *orderbyexpr = (Node *) lfirst(lcx);
	// 		Oid			orderbyType = exprType(orderbyexpr);
	// 		Oid			orderbyColl = exprCollation(orderbyexpr);
	// 		SortSupport orderbysort = &indexstate->iss_SortSupport[i];

	// 		/* Initialize sort support */
	// 		orderbysort->ssup_cxt = CurrentMemoryContext;
	// 		orderbysort->ssup_collation = orderbyColl;
	// 		/* See cmp_orderbyvals() comments on NULLS LAST */
	// 		orderbysort->ssup_nulls_first = false;
	// 		/* ssup_attno is unused here and elsewhere */
	// 		orderbysort->ssup_attno = 0;
	// 		/* No abbreviation */
	// 		orderbysort->abbreviate = false;
	// 		PrepareSortSupportFromOrderingOp(orderbyop, orderbysort);

	// 		get_typlenbyval(orderbyType,
	// 						&indexstate->iss_OrderByTypLens[i],
	// 						&indexstate->iss_OrderByTypByVals[i]);
	// 		i++;
	// 	}

	// 	/* allocate arrays to hold the re-calculated distances */
	// 	indexstate->iss_OrderByValues = (Datum *)
	// 		palloc(numOrderByKeys * sizeof(Datum));
	// 	indexstate->iss_OrderByNulls = (bool *)
	// 		palloc(numOrderByKeys * sizeof(bool));

	// 	/* and initialize the reorder queue */
	// 	// indexstate->iss_ReorderQueue = pairingheap_allocate(reorderqueue_cmp,
	// 	// 													indexstate);
	// 	// TODO:
	// 	indexstate->iss_ReorderQueue = NULL;
	// }

	// // TODO: 搞清楚这里
	// /*
	//  * If we have runtime keys, we need an ExprContext to evaluate them. The
	//  * node's standard context won't do because we want to reset that context
	//  * for every tuple.  So, build another context just like the other one...
	//  * -tgl 7/11/00
	//  */
	// if (indexstate->iss_NumRuntimeKeys != 0)
	// {
	// 	ExprContext *stdecontext = indexstate->ss.ps.ps_ExprContext;

	// 	ExecAssignExprContext(estate, &indexstate->ss.ps);
	// 	indexstate->iss_RuntimeContext = indexstate->ss.ps.ps_ExprContext;
	// 	indexstate->ss.ps.ps_ExprContext = stdecontext;
	// }
	// else
	// {
	// 	indexstate->iss_RuntimeContext = NULL;
	// }

	// /*
	//  * all done.
	//  */
	// return indexstate;
}

/*
 * When an ordering operator is used, tuples fetched from the index that
 * need to be reordered are queued in a pairing heap, as ReorderTuples.
 */
typedef struct
{
	pairingheap_node ph_node;
	HeapTuple	htup;
	Datum	   *orderbyvals;
	bool	   *orderbynulls;
} ReorderTuple;

static int
cmp_orderbyvals(const Datum *adist, const bool *anulls,
				const Datum *bdist, const bool *bnulls,
				IndexScanState *node)
{
	int			i;
	int			result;

	for (i = 0; i < node->iss_NumOrderByKeys; i++)
	{
		SortSupport ssup = &node->iss_SortSupport[i];

		/*
		 * Handle nulls.  We only need to support NULLS LAST ordering, because
		 * match_pathkeys_to_index() doesn't consider indexorderby
		 * implementation otherwise.
		 */
		if (anulls[i] && !bnulls[i])
			return 1;
		else if (!anulls[i] && bnulls[i])
			return -1;
		else if (anulls[i] && bnulls[i])
			return 0;

		result = ssup->comparator(adist[i], bdist[i], ssup);
		if (result != 0)
			return result;
	}

	return 0;
}

static int
reorderqueue_cmp(const pairingheap_node *a, const pairingheap_node *b,
				 void *arg)
{
	ReorderTuple *rta = (ReorderTuple *) a;
	ReorderTuple *rtb = (ReorderTuple *) b;
	IndexScanState *node = (IndexScanState *) arg;

	/* exchange argument order to invert the sort order */
	return cmp_orderbyvals(rtb->orderbyvals, rtb->orderbynulls,
						   rta->orderbyvals, rta->orderbynulls,
						   node);
}

static IndexScanState *
init_anns_iss(IndexScan *node, EState *estate, int eflags)
{
	// IndexScanState *indexstate;
	// indexstate = (IndexScanState *) ExecInitNode(&(node->scan.plan), estate, eflags);
	// indexstate->ss.ps.ps_ProjInfo = NULL;
	// return indexstate;

	/*
	 * do nothing when we get to the end of a leaf on tree.
	 */
	if (node == NULL)
		return NULL;

	/*
	 * Make sure there's enough stack available. Need to check here, in
	 * addition to ExecProcNode() (via ExecProcNodeFirst()), to ensure the
	 * stack isn't overrun while initializing the node tree.
	 */
	check_stack_depth();
	
	IndexScanState *indexstate;
	Relation	currentRelation;
	bool		relistarget;

	indexstate = makeNode(IndexScanState);
	indexstate->ss.ps.plan = (Plan *) node;
	indexstate->ss.ps.state = estate;
	// indexstate->ss.ps.ExecProcNode = ExecHybridQueryANNSScan;  // TODO:
	indexstate->ss.ps.ExecProcNode = NULL;  // TODO:

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &indexstate->ss.ps);

	/*
	 * open the base relation and acquire appropriate lock on it.
	 */
	currentRelation = ExecOpenScanRelation(estate, node->scan.scanrelid, eflags);

	indexstate->ss.ss_currentRelation = currentRelation;
	indexstate->ss.ss_currentScanDesc = NULL;	/* no heap scan here */

	// NOTE: 不会用到ss.ss_ScanTupleSlot，但是也要分配内存，ExecScanReScan函数里面会销毁它，
	// 如果不分配内存，该函数会执行出错。
	/*
	 * get the scan type from the relation descriptor.
	 */
	ExecInitScanTupleSlot(estate, &indexstate->ss,
						  RelationGetDescr(currentRelation));

	// NOTE: 不会用到ss.ps.ps_ResultTupleSlot，但是也要分配内存，ExecEndIndexScan函数里面会销毁它，
	// 如果不分配内存，该函数会执行出错。
	/*
	 * Initialize result slot, type and projection.
	 */
	ExecInitResultTupleSlotTL(estate, &indexstate->ss.ps);
	// ExecAssignScanProjectionInfo(&indexstate->ss);
	indexstate->ss.ps.ps_ProjInfo = NULL;

	// NOTE: IndexScan中对应的字段为NIL，则ExecInitQual会返回NULL，ExecInitExprList会返回NIL。因此此处可以不用处理。
	indexstate->ss.ps.qual =
		ExecInitQual(node->scan.plan.qual, (PlanState *) indexstate);
	indexstate->ss.ps.qual = NULL;
	indexstate->indexqualorig =
		ExecInitQual(node->indexqualorig, (PlanState *) indexstate);
	indexstate->indexorderbyorig =
		ExecInitExprList(node->indexorderbyorig, (PlanState *) indexstate);
	
	if (eflags & EXEC_FLAG_EXPLAIN_ONLY)
		return indexstate;
	
	relistarget = ExecRelationIsTargetRelation(estate, node->scan.scanrelid);
	indexstate->iss_RelationDesc = index_open(node->indexid,
											  relistarget ? NoLock : AccessShareLock);

	indexstate->iss_RuntimeKeysReady = false;
	indexstate->iss_RuntimeKeys = NULL;
	indexstate->iss_NumRuntimeKeys = 0;

	// TODO: 只需要iss_OrderByKeys，不需要iss_ScanKeys
	ExecIndexBuildScanKeys((PlanState *) indexstate,
						   indexstate->iss_RelationDesc,
						   node->indexqual,
						   false,
						   &indexstate->iss_ScanKeys,
						   &indexstate->iss_NumScanKeys,
						   &indexstate->iss_RuntimeKeys,
						   &indexstate->iss_NumRuntimeKeys,
						   NULL,	/* no ArrayKeys */
						   NULL);

	ExecIndexBuildScanKeys((PlanState *) indexstate,
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
		// indexstate->iss_ReorderQueue = pairingheap_allocate(reorderqueue_cmp,
		// 													indexstate);
		// TODO:
		indexstate->iss_ReorderQueue = NULL;
	}

	// TODO: 搞清楚这里
	/*
	 * If we have runtime keys, we need an ExprContext to evaluate them. The
	 * node's standard context won't do because we want to reset that context
	 * for every tuple.  So, build another context just like the other one...
	 * -tgl 7/11/00
	 */
	if (indexstate->iss_NumRuntimeKeys != 0)
	{
		ExprContext *stdecontext = indexstate->ss.ps.ps_ExprContext;

		ExecAssignExprContext(estate, &indexstate->ss.ps);
		indexstate->iss_RuntimeContext = indexstate->ss.ps.ps_ExprContext;
		indexstate->ss.ps.ps_ExprContext = stdecontext;
	}
	else
	{
		indexstate->iss_RuntimeContext = NULL;
	}

	indexstate->ss.ps.ExecProcNodeReal = NULL;

	indexstate->ss.ps.initPlan = NIL;

	/* Set up instrumentation for this node if requested */
	if (estate->es_instrument)
		indexstate->ss.ps.instrument = InstrAlloc(1, estate->es_instrument);

	/*
	 * all done.
	 */
	return indexstate;
}

/*
 * BeginHybridQueryScan
 */
static void
BeginHybridQueryScan(CustomScanState *css, EState *estate, int eflags)
{
	HybridQueryState	*hqs = (HybridQueryState *)css;
	IndexScanState		*structured_iss;
	IndexScanState		*anns_iss;

	structured_iss = init_structured_iss((IndexScan *)hqs->css.ss.ps.plan->lefttree,
										   estate, eflags);
	anns_iss = init_anns_iss((IndexScan *)hqs->css.ss.ps.plan->righttree,
							  estate, eflags);

	/* 
	 * NOTE:
	 * CustomScanState的其余成员在ExecInitCustomScan中被初始化。
	 * 注意CreateCustomScanState和BeginCustomScan这两个成员函数需要完成的功能。
	 */
	hqs->css.ss.ps.lefttree = (PlanState *)structured_iss;
	hqs->css.ss.ps.righttree = (PlanState *)anns_iss;
	
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

static void
ExecStructuredIndexScan(IndexScanState *structured_iss,
						std::vector<ItemPointerData> &output)
{
	TupleTableSlot	*structured_slot;
	int				 structured_cnt = 0;
	std::chrono::steady_clock::time_point total_start, total_end;
    double total_time;

	total_start = std::chrono::steady_clock::now();
	for (;;)
	{
		structured_slot = ExecProcNode(&structured_iss->ss.ps);
		if (TupIsNull(structured_slot))
		{
			break;
		}
		else
		{
			output.push_back(structured_slot->tts_tuple->t_self);
			structured_cnt++;
		}
	}
	total_end = std::chrono::steady_clock::now();
	total_time = std::chrono::duration_cast<std::chrono::duration<double, std::milli>>(total_end - total_start).count();
	elog(WARNING, "structured_cnt: %d, total_time: %f ms", structured_cnt, total_time);
}

/*
 * HybridQueryAccess
 */
static TupleTableSlot *
HybridQueryAccess(CustomScanState *css)
{
	HybridQueryState	*hqs = (HybridQueryState *)css;
	PlanState			*outerNode;
	PlanState			*innerNode;
	
	outerNode = outerPlanState(hqs);
	innerNode = innerPlanState(hqs);

	EState	   *estate;
	ExprContext *econtext;
	ScanDirection direction;
	IndexScanDesc scandesc;
	HeapTuple	tuple;
	TupleTableSlot *slot;

	IndexScanState *node = (IndexScanState *)innerNode;

	/*
	 * extract necessary information from index scan node
	 */
	estate = node->ss.ps.state;
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
	econtext = node->ss.ps.ps_ExprContext;
	slot = node->ss.ss_ScanTupleSlot;

	if (scandesc == NULL)
	{
		/*
		 * We reach here if the index scan is not parallel, or if we're
		 * serially executing an index scan that was planned to be parallel.
		 */
		scandesc = index_beginscan(node->ss.ss_currentRelation,
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

	/* 结构化索引扫描 */
	// TODO: 把结构化条件的结果存放在opaque中，但是需要抽象出来作为基类，这样就不依赖某种特定的向量索引了，但所有向量索引的opaque都需要继承这个基类
	std::vector<ItemPointerData> ipd_vec;
	PGIVFPQScanOpaque so = (PGIVFPQScanOpaque)scandesc->opaque;

	if (so->first_call)
	{
		ExecStructuredIndexScan((IndexScanState *) outerNode, ipd_vec);

		MemoryContext old_ctx;

		old_ctx = MemoryContextSwitchTo(so->scan_ctx);
		ItemPointerData *quals_ipds = (ItemPointerData *) palloc0(sizeof(ItemPointerData) * ipd_vec.size());
		for (int i = 0; i < ipd_vec.size(); i++)
			quals_ipds[i] = ipd_vec[i];
		
		so->quals_ipds = quals_ipds;
		so->quals_ipds_cnt = ipd_vec.size();

		MemoryContextSwitchTo(old_ctx);
	}
	
	/* 向量索引扫描 */
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

	/* 条件过滤和投影操作在ExecScan中进行 */

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

	PlanState			*outerNode;
	PlanState			*innerNode;
	
	outerNode = outerPlanState(hqs);
	innerNode = innerPlanState(hqs);

	if (hqs->css.ss.ss_currentScanDesc)
		heap_endscan(hqs->css.ss.ss_currentScanDesc);

	ExecEndNode(outerNode);
	ExecEndNode(innerNode);
}

/*
 * ReScanHybridQueryScan
 */
static void
ReScanHybridQueryScan(CustomScanState *node)
{
	HybridQueryState *hqs = (HybridQueryState *)node;

	PlanState			*outerNode;
	PlanState			*innerNode;
	
	outerNode = outerPlanState(hqs);
	innerNode = innerPlanState(hqs);

	ExecReScan(outerNode);
	ExecReScan(innerNode);
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
							 DEFAULT_CPU_OPERATOR_COST * 1000.0,
							 0,
							 disable_cost,
							 PGC_USERSET,
							 GUC_NOT_IN_SAMPLE,
							 NULL, NULL, NULL);

	// 计算索引中任意一条pq code与一个原始向量之间的距离的cost
	DefineCustomRealVariable("cost_from_two_codes",
							 "Cost of compute distance from two codes",
							 NULL,
							 &cost_from_two_codes,
							 DEFAULT_CPU_OPERATOR_COST * 2000.0,
							 0,
							 disable_cost,
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