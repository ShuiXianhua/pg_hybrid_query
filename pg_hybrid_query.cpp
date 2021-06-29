#include "postgres.h"
#include "access/relscan.h"
#include "access/sysattr.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/explain.h"
#include "executor/executor.h"
#include "executor/nodeCustom.h"
#include "fmgr.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/paths.h"
#include "optimizer/pathnode.h"
#include "optimizer/plancat.h"
#include "optimizer/planmain.h"
#include "optimizer/placeholder.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/subselect.h"
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

PG_MODULE_MAGIC;

/*
 * HybridQueryState
 */
typedef struct {
	CustomScanState	css;
} HybridQueryState;

/* static variables */
static bool		enable_hybridquery;
static set_rel_pathlist_hook_type set_rel_pathlist_next = NULL;

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
hybridquery_tryfind_annsindex(PlannerInfo *root,
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

		/* 1016409: pg_hnsw am oid */
		if (index->relam != 1016409)
			continue;

		indexOpt = index;
	}

	return indexOpt;
}

/*
 * hybridquery_estimate_costs
 i*/
static void
hybridquery_estimate_costs(PlannerInfo *root,
				  RelOptInfo *baserel,
				  CustomPath *cpath)
{
	Path	   *path = &cpath->path;
	// TODO:
	
	path->rows = 512;
	path->startup_cost = 0.0;
	path->total_cost = 0.0;
}

static Path *
create_hybridquery_path(PlannerInfo *root,
					RelOptInfo *baserel,
					IndexOptInfo *indexOpt)
{
	CustomPath	   *cpath;

	cpath = makeNode(CustomPath);
	cpath->path.pathtype = T_CustomScan;
	cpath->path.parent = baserel;
	cpath->path.pathtarget = baserel->reltarget;
	cpath->path.param_info = get_baserel_parampathinfo(root, baserel,
										   baserel->lateral_relids);
	
	hybridquery_estimate_costs(root, baserel, cpath);

	cpath->path.pathkeys = NIL;	/* unsorted results */
	cpath->flags = 0;
	cpath->custom_paths = NIL;
	cpath->custom_private = NIL;
	cpath->methods = &hybridquery_path_methods;

	return &cpath->path;
}

/*
 * set_hybridquery_path
 */
static void
set_hybridquery_path(PlannerInfo *root, RelOptInfo *baserel,
				Index rtindex, RangeTblEntry *rte)
{
	char			relkind;
	IndexOptInfo	*indexOpt;
	Path			*pathnode;

	ListCell	   *lc;
	List		   *ctid_quals = NIL;

	/* only plain relations are supported */
	if (rte->rtekind != RTE_RELATION)
		return;
	relkind = get_rel_relkind(rte->relid);
	if (relkind != RELKIND_RELATION)
		return;

	if (!enable_hybridquery)
		return;
	
	indexOpt = hybridquery_tryfind_annsindex(root, baserel);

	pathnode = create_hybridquery_path(root, baserel, indexOpt);

	add_path(baserel, pathnode);
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
	CustomScan	   *cscan = makeNode(CustomScan);

	cscan->flags = best_path->flags;
	cscan->methods = &hybridquery_scan_methods;

	/* set scanrelid */
	cscan->scan.scanrelid = rel->relid;
	/* set targetlist as is  */
	cscan->scan.plan.targetlist = tlist;
	/* reduce RestrictInfo list to bare expressions */
	cscan->scan.plan.qual = extract_actual_clauses(clauses, false);

	return &cscan->scan.plan;
}

/*
 * CreateHybridQueryScanState
 */
static Node *
CreateHybridQueryScanState(CustomScan *custom_plan)
{
	HybridQueryState  *hqs = palloc0(sizeof(HybridQueryState));

	NodeSetTag(hqs, T_CustomScanState);
	hqs->css.flags = custom_plan->flags;
	hqs->css.methods = &hybridquery_exec_methods;

	return (Node *)&ctss->css;
}

/*
 * BeginHybridQueryScan
 */
static void
BeginHybridQueryScan(CustomScanState *node, EState *estate, int eflags)
{
	// TODO:
	return;
}

/*
 * HybridQueryAccess
 */
static TupleTableSlot *
HybridQueryAccess(IndexScanState *node)
{
	EState	   *estate;
	ExprContext *econtext;
	ScanDirection direction;
	IndexScanDesc scandesc;
	HeapTuple	tuple;
	TupleTableSlot *slot;

	/*
	 * extract necessary information from index scan node
	 */
	estate = node->ss.ps.state;
	direction = estate->es_direction;
	/* flip direction if this is an overall backward scan */
	if (ScanDirectionIsBackward(((IndexScan *) node->ss.ps.plan)->indexorderdir))
	{
		if (ScanDirectionIsForward(direction))
			direction = BackwardScanDirection;
		else if (ScanDirectionIsBackward(direction))
			direction = ForwardScanDirection;
	}
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
HybridQueryRecheck(IndexScanState *node, TupleTableSlot *slot)
{
	ExprContext *econtext;

	/*
	 * extract necessary information from index scan node
	 */
	econtext = node->ss.ps.ps_ExprContext;

	/* Does the tuple meet the indexqual condition? */
	econtext->ecxt_scantuple = slot;
	return ExecQualAndReset(node->indexqualorig, econtext);
}

/*
 * ExecHybridQueryScan
 */
static TupleTableSlot *
ExecHybridQueryScan(CustomScanState *node)
{
	// TODO:
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

	if (hqs->css.ss.ss_currentScanDesc)
		heap_endscan(ctss->css.ss.ss_currentScanDesc);
	
	Relation	indexRelationDesc;
	IndexScanDesc indexScanDesc;
	Relation	relation;

	/*
	 * extract information from the node
	 */
	indexRelationDesc = hqs->css.iss_RelationDesc;
	indexScanDesc = hqs->css.iss_ScanDesc;
	relation = hqs->css.ss.ss_currentRelation;

	/*
	 * clear out tuple table slots
	 */
	ExecClearTuple(hqs->css.ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(hqs->css.ss.ss_ScanTupleSlot);

	/*
	 * close the index relation (no-op if we didn't open it)
	 */
	if (indexScanDesc)
		index_endscan(indexScanDesc);
	if (indexRelationDesc)
		index_close(indexRelationDesc, NoLock);

	/*
	 * close the heap relation.
	 */
	ExecCloseScanRelation(relation);
}

/*
 * ReScanHybridQueryScan
 */
static void
ReScanHybridQueryScan(CustomScanState *node)
{
	node
	/*
	 * If we are doing runtime key calculations (ie, any of the index key
	 * values weren't simple Consts), compute the new key values.  But first,
	 * reset the context so we don't leak memory as each outer tuple is
	 * scanned.  Note this assumes that we will recalculate *all* runtime keys
	 * on each call.
	 */
	if (node->iss_NumRuntimeKeys != 0)
	{
		ExprContext *econtext = node->iss_RuntimeContext;

		ResetExprContext(econtext);
		ExecIndexEvalRuntimeKeys(econtext,
								 node->iss_RuntimeKeys,
								 node->iss_NumRuntimeKeys);
	}
	node->iss_RuntimeKeysReady = true;

	/* flush the reorder queue */
	if (node->iss_ReorderQueue)
	{
		while (!pairingheap_is_empty(node->iss_ReorderQueue))
			reorderqueue_pop(node);
	}

	/* reset index scan */
	if (node->iss_ScanDesc)
		index_rescan(node->iss_ScanDesc,
					 node->iss_ScanKeys, node->iss_NumScanKeys,
					 node->iss_OrderByKeys, node->iss_NumOrderByKeys);
	node->iss_ReachedEnd = false;

	ExecScanReScan(&node->ss);
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

	/* registration of the hook to add alternative path */
	set_rel_pathlist_next = set_rel_pathlist_hook;
	set_rel_pathlist_hook = set_hybridquery_path;
}

void _PG_fini(void)
{
	set_rel_pathlist_hook = NULL;
}