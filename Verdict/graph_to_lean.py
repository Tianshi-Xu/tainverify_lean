"""Generate a Lean spec using denotational (mathematical) graph descriptions.

This is a *new* implementation (the old store/fuel execution based spec generator
was removed by the user).

What this generator emits:

- A denotational graph declaration for SM and PM graphs (`GraphDecl`).
- A small set of *coarse* lineage goals for observable output tensors:
  for each aligned leaf output `ts`, pick one correspondence `ts ↦ [(rank, tp_tid)]`.

Notes / design choices:

- We only generate goals for *outputs* (aligned leaves). We do NOT emit goals for
  intermediate tensors.
- “Coarse” lineage means we keep only (ts tid, per-rank tp tid) pairs.
  We deliberately avoid computing slice-maps.
- The produced Lean spec is independent of the old repeated store traversal semantics.
  Semantics is a single topological fold in `trainverify.denote.Denote`.

Run (must be in conda env verdict):

  conda run -n verdict python Verdict/graph_to_lean.py \
	--sm-pkl <single.pkl> --pm-pkl <tp.pkl> \
	--out mathlib4/trainverify/denote/GeneratedData.lean
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parent.parent

DEFAULT_SM_GRAPH = ROOT / "genmodel" / "mgeners" / "mlp_mgener_dp1_pp1_tp1_nm1_gbs128_dim128_ly1.pkl"
DEFAULT_PM_GRAPH = ROOT / "genmodel" / "mgeners" / "mlp_mgener_dp1_pp1_tp4_nm1_gbs128_dim128_ly1.pkl"
DEFAULT_OUT = ROOT / "trainverify" / "denote" / "GeneratedData.lean"


def parse_args() -> argparse.Namespace:
	p = argparse.ArgumentParser(description="Generate Lean spec (denotational) + coarse lineage goals")
	p.add_argument("--sm-pkl", default=str(DEFAULT_SM_GRAPH), help="Path to SM graph pickle")
	p.add_argument("--pm-pkl", default=str(DEFAULT_PM_GRAPH), help="Path to PM graph pickle")
	p.add_argument(
		"--out",
		default=str(DEFAULT_OUT),
		help="Output Lean file path (e.g. mathlib4/trainverify/denote/GeneratedData.lean)",
	)
	p.add_argument(
		"--module",
		default="trainverify.denote.GeneratedData",
		help="Lean module name used in the generated file header comment",
	)
	p.add_argument(
		"--emit-spec-template",
		action="store_true",
		help="Also emit a proof template file (GeneratedSpec.lean) with sorry-filled theorem stubs.",
	)
	p.add_argument(
		"--spec-out",
		default=str(ROOT / "trainverify" / "denote" / "GeneratedSpec.lean"),
		help="Output path for the spec/proof template file.",
	)
	p.add_argument(
		"--overwrite-spec",
		action="store_true",
		help="Overwrite --spec-out if it already exists.",
	)
	p.add_argument(
		"--max-goals",
		type=int,
		default=0,
		help="If >0, emit at most this many output goals (stable order by tid).",
	)
	p.add_argument(
		"--split-goals",
		action="store_true",
		help=(
			"Emit per-goal sliced graphs and local statements. "
			"Later goals can assume earlier intermediate tensors as boundary init goals."
		),
	)
	p.add_argument(
		"--goals-out-dir",
		default=str(ROOT / "trainverify" / "denote"),
		help="Output directory for per-goal Lean files when --split-goals is enabled.",
	)
	return p.parse_args()


def load_verifier(sm_path: str, pm_path: str):
	import sys

	sys.path.extend([str(ROOT), str(ROOT / "genmodel"), str(ROOT / "Verdict")])

	from verdict.config import Config  # type: ignore
	from verdict.verifier import StageParallelVerifier  # type: ignore
	from nnscaler_backend import nnScalerGraphBackend  # type: ignore
	from z3_backend import z3Backend  # type: ignore
	from analyze_graph import prepare  # type: ignore

	Config.update_from_args([])
	prepare(Config)

	return StageParallelVerifier(
		Gs_path=str(sm_path),
		Ws_path=None,
		Gp_path=str(pm_path),
		Wp_path=None,
		graph_backend=nnScalerGraphBackend,
		symbolic_backend=z3Backend,
	)


def infer_coarse_lineages_from_expanded(GsE: Any, GpE: Any) -> List[Any]:
	# Align original ops and emit Ts==Tps for each input/output.
	from nnscaler_backend import build_lineage as bl  # type: ignore

	Gs_alignable_ops = [n for n in GsE.nodes() if bl._is_original_op(GsE.node_opname(n))]
	Gp_alignable_ops = [n for n in GpE.nodes() if bl._is_original_op(GpE.node_opname(n))]
	return bl._infer_lineages_from_alignable_ops(Gs_alignable_ops, Gp_alignable_ops, GsE, GpE)


def _build_producer_index(G: Any) -> Dict[int, List[int]]:
	prod: Dict[int, List[int]] = {}
	for i, n in enumerate(G.nodes()):
		for t in G.node_outputs(n):
			prod.setdefault(int(t.tid), []).append(i)
	return prod


def _build_consumer_index(G: Any) -> Dict[int, List[int]]:
	cons: Dict[int, List[int]] = {}
	for i, n in enumerate(G.nodes()):
		for t in G.node_inputs(n):
			cons.setdefault(int(t.tid), []).append(i)
	return cons


def leaf_output_tids(G: Any) -> List[int]:
	"""Leaf/output tensors in the dataflow sense (produced but never consumed)."""
	prod = _build_producer_index(G)
	cons = _build_consumer_index(G)
	leaves = [tid for tid in prod.keys() if tid not in cons or not cons[tid]]
	return sorted(set(int(x) for x in leaves))


def backward_closure_tids(G: Any, root_tids: Iterable[int]) -> List[int]:
	prod = _build_producer_index(G)
	seen: set[int] = {int(t) for t in root_tids}
	frontier: set[int] = set(seen)
	while frontier:
		nxt: set[int] = set()
		for tid in list(frontier):
			for node_idx in prod.get(int(tid), []):
				node = G.nodes()[node_idx]
				for t_in in G.node_inputs(node):
					t_id = int(t_in.tid)
					if t_id not in seen:
						seen.add(t_id)
						nxt.add(t_id)
		frontier = nxt
	return sorted(seen)


def backward_closure_tids_until(
	G: Any, root_tids: Iterable[int], stop_tids: Iterable[int]
) -> List[int]:
	"""Backward closure, but do not expand past `stop_tids`.

	The resulting set still includes the stop tids themselves, but excludes their producers.
	"""
	prod = _build_producer_index(G)
	stop: set[int] = {int(t) for t in stop_tids}
	seen: set[int] = {int(t) for t in root_tids}
	frontier: set[int] = set(seen)
	while frontier:
		nxt: set[int] = set()
		for tid in list(frontier):
			if int(tid) in stop:
				continue
			for node_idx in prod.get(int(tid), []):
				node = G.nodes()[node_idx]
				for t_in in G.node_inputs(node):
					t_id = int(t_in.tid)
					if t_id not in seen:
						seen.add(t_id)
						nxt.add(t_id)
		frontier = nxt
	return sorted(seen)


def _safe_str_op(op: Any) -> str:
	# OpName types often have a friendly string repr.
	try:
		return str(op)
	except Exception:
		return repr(op)


def _node_rank(node: Any) -> int:
	return int(getattr(node, "rank", 0) or 0)


@dataclass(frozen=True)
class SelectedLineage:
	ts: int
	tps: List[Tuple[int, int]]  # (rank, tid)


@dataclass
class GoalDependency:
	"""Captures dependency information for a goal."""
	goal_ts: int
	# List of (intermediate_ts, lineage) pairs this goal depends on
	prereq_intermediate_goals: List[Tuple[int, "SelectedLineage"]]
	# Topological position in SM graph (lower = earlier)
	sm_position: int


@dataclass
class GoalSlice:
	"""A per-goal sliced subgraph (cut at prerequisite intermediate tensors)."""
	goal: SelectedLineage
	sm_nodes: List[Any]
	pm_nodes: List[Any]


def compute_goal_dependencies(
	G: Any,
	goals: List[SelectedLineage],
	by_ts: Dict[int, List[Any]],
	init_tids: set[int],
) -> Tuple[List[GoalDependency], Dict[int, SelectedLineage]]:
	"""Compute dependencies between goals via shared intermediate tensors.
	
	Returns:
	- List of GoalDependency for each goal
	- Dict of intermediate tensors that need their own lineage goals
	"""
	# Build producer index: tid -> node index (for non-DATALOADER nodes)
	nodes = [n for n in G.nodes() if "DATALOADER" not in _safe_str_op(G.node_opname(n))]
	tid_to_node_idx: Dict[int, int] = {}
	for i, n in enumerate(nodes):
		for t in G.node_outputs(n):
			tid_to_node_idx[int(t.tid)] = i
	
	# For each goal, compute its backward closure and position
	goal_closures: Dict[int, set[int]] = {}
	goal_positions: Dict[int, int] = {}
	for g in goals:
		closure = set(backward_closure_tids(G, [g.ts]))
		goal_closures[g.ts] = closure
		goal_positions[g.ts] = tid_to_node_idx.get(g.ts, 999)
	
	# Sort goals by topological position
	sorted_goals = sorted(goals, key=lambda g: goal_positions[g.ts])
	
	# For each goal, find intermediate tensors it shares with earlier goals
	intermediate_lineages: Dict[int, SelectedLineage] = {}
	dependencies: List[GoalDependency] = []
	
	processed_tids: set[int] = set()  # tids covered by earlier goals
	
	for g in sorted_goals:
		prereqs: List[Tuple[int, SelectedLineage]] = []
		my_closure = goal_closures[g.ts]
		
		# Find which intermediate tensors from earlier goals we depend on
		shared_intermediates = my_closure & processed_tids - init_tids
		
		for inter_ts in sorted(shared_intermediates):
			if inter_ts in intermediate_lineages:
				prereqs.append((inter_ts, intermediate_lineages[inter_ts]))
			elif inter_ts in by_ts:
				# Create intermediate lineage goal
				lin = pick_one_lineage_for_ts(by_ts.get(int(inter_ts), []), inter_ts)
				if lin is not None:
					intermediate_lineages[inter_ts] = lin
					prereqs.append((inter_ts, lin))
		
		dependencies.append(GoalDependency(
			goal_ts=g.ts,
			prereq_intermediate_goals=prereqs,
			sm_position=goal_positions[g.ts],
		))
		
		# Add this goal's closure to processed tids
		processed_tids.update(my_closure)
	
	return dependencies, intermediate_lineages


def pick_one_lineage_for_ts(lineages: Sequence[Any], ts_tid: int) -> Optional[SelectedLineage]:
	candidates: List[SelectedLineage] = []
	for l in lineages:
		Ts = getattr(l, "Ts")
		if int(Ts.tid) != int(ts_tid):
			continue
		Tps = list(getattr(l, "Tps"))
		pairs = sorted({(int(tp.rank), int(tp.tid)) for tp in Tps})
		candidates.append(SelectedLineage(ts=int(ts_tid), tps=pairs))

	if not candidates:
		return None

	# Prefer the lineage with most ranks covered; tie-break by lexicographic order.
	candidates.sort(key=lambda c: (-len(c.tps), c.tps))
	return candidates[0]


def compress_if_replicated(lineage: SelectedLineage) -> SelectedLineage:
	"""If all pieces point to the same PM tid, keep only one piece.

This avoids constructing a meaningless "allGather of identical full tensors" for replicated inputs.
"""
	if not lineage.tps:
		return lineage
	tp_tids = {int(t) for (_r, t) in lineage.tps}
	if len(tp_tids) == 1:
		(r0, t0) = sorted(lineage.tps)[0]
		return SelectedLineage(ts=lineage.ts, tps=[(int(r0), int(t0))])
	return lineage


def normalize_lineage_by_collectives(pm_graph: Any, lineage: SelectedLineage) -> SelectedLineage:
	"""Normalize lineage by collapsing collective inputs to their collective output.

	If the lineage tps match the inputs of an AllReducePrim/AllGatherPrim node and that
	node has a single output tid, replace tps with that output tid (replicated result).
	"""
	if not lineage.tps:
		return lineage

	lineage_tids = sorted(int(t) for (_r, t) in lineage.tps)
	for n in pm_graph.nodes():
		op = _safe_str_op(pm_graph.node_opname(n))
		if ("AllReducePrim" not in op) and ("AllGatherPrim" not in op):
			continue
		ins = sorted(int(t.tid) for t in pm_graph.node_inputs(n))
		outs = [int(t.tid) for t in pm_graph.node_outputs(n)]
		if ins == lineage_tids and len(outs) == 1:
			return SelectedLineage(ts=lineage.ts, tps=[(0, outs[0])])
	return lineage


def escape_lean_string(s: str) -> str:
	return s.replace("\\", "\\\\").replace('"', '\\"')


def lean_list_nat(xs: Sequence[int]) -> str:
	if not xs:
		return "[]"
	return "[" + ", ".join(str(int(x)) for x in xs) + "]"


def lean_list_pairs(pairs: Sequence[Tuple[int, int]]) -> str:
	# List (Rank × Tid)
	if not pairs:
		return "[]"
	return "[" + ", ".join(f"({int(r)}, {int(t)})" for r, t in pairs) + "]"


def _shape_init_from_graph_by_tid(G: Any, tid: int) -> Tuple[Optional[List[int]], Optional[bool]]:
	tensors = list(G.tensors())
	t_any = next((t for t in tensors if int(getattr(t, "tid", -1)) == int(tid)), None)
	if t_any is None:
		return None, None
	try:
		shp = [int(x) for x in list(G.tensor_shape(t_any))]
	except Exception:
		shp = None
	try:
		init = bool(G.is_initialized(t_any))
	except Exception:
		init = None
	return shp, init


def _validate_lineage_against_graphs(
	lineage: "SelectedLineage", sm_graph: Any, pm_graph: Any, pm_num_ranks: int
) -> List[str]:
	"""Lightweight sanity checks for a lineage goal against graph registries.

	This is not a proof; it only reports likely issues (missing shapes or rank coverage).
	"""
	issues: List[str] = []
	sh_ts, _init = _shape_init_from_graph_by_tid(sm_graph, int(lineage.ts))
	if sh_ts is None:
		issues.append(f"SM shape missing for ts={lineage.ts}")
	# Check PM tids exist and have shapes
	for (_r, tp_tid) in lineage.tps:
		sh_tp, _init_tp = _shape_init_from_graph_by_tid(pm_graph, int(tp_tid))
		if sh_tp is None:
			issues.append(f"PM shape missing for tp_tid={tp_tid} (ts={lineage.ts})")
	# Rank coverage check (only meaningful when multiple pieces are present)
	ranks = [int(r) for (r, _t) in lineage.tps]
	if len(ranks) >= 2:
		missing = [r for r in range(int(pm_num_ranks)) if r not in set(ranks)]
		if missing:
			issues.append(f"PM rank coverage missing ranks={missing} for ts={lineage.ts}")
	return issues


def _init_tids_from_kept_nodes(G: Any, kept_nodes: Sequence[Any]) -> List[int]:
	"""Infer boundary tids that must come from the initial store.

	We treat tensors as *initial* if they appear as an input to some kept node,
	but are not produced as an output by any kept node. This is intentionally
	graph-structural and does not depend on `is_initialized` (because we may drop
	DATALOADER nodes and want their outputs to become initial assumptions).
	"""
	produced: set[int] = set()
	consumed: set[int] = set()
	for n in kept_nodes:
		for t in G.node_outputs(n):
			produced.add(int(t.tid))
		for t in G.node_inputs(n):
			consumed.add(int(t.tid))
	init_tids = sorted(consumed - produced)
	return init_tids


def _emit_init_env(
	lines: List[str], *, name: str, G: Any, kept_nodes: Sequence[Any], prefer_shapes: Optional[Dict[int, List[int]]] = None
) -> None:
	init_tids = _init_tids_from_kept_nodes(G, kept_nodes)
	pairs: List[Tuple[int, List[int]]] = []
	for tid in init_tids:
		if prefer_shapes is not None and int(tid) in prefer_shapes:
			shp = list(prefer_shapes[int(tid)])
		else:
			shp, _init = _shape_init_from_graph_by_tid(G, tid)
		if shp is None:
			continue
		pairs.append((int(tid), [int(x) for x in shp]))

	lines.append(f"def {name}InitShapes : List (Tid × Shape) := [")
	for (tid, shp) in pairs:
		lines.append(f"  ({tid}, [{', '.join(str(int(x)) for x in shp)}]),")
	lines.append("]")
	lines.append("")
	lines.append(f"def {name}InitEnv : ShapeEnv := shapeEnvOfList {name}InitShapes")
	lines.append("")


def _build_sm_prefer(G: Any, kept_nodes: Sequence[Any]) -> Dict[int, List[int]]:
	"""Build a SM shape preference map from boundary tids of the kept subgraph."""
	prefer: Dict[int, List[int]] = {}
	for tid in _init_tids_from_kept_nodes(G, kept_nodes):
		shp, _init = _shape_init_from_graph_by_tid(G, tid)
		if shp is not None:
			prefer[int(tid)] = [int(x) for x in shp]
	return prefer


def emit_lean_spec(
	*,
	out_path: Path,
	spec_out_path: Optional[Path],
	emit_spec_template: bool,
	overwrite_spec: bool,
	module_name: str,
	sm_nodes: List[Any],
	pm_nodes: List[Any],
	sm_graph: Any,
	pm_graph: Any,
	init_goals: List[SelectedLineage],
	goals: List[SelectedLineage],
	goal_deps: Optional[List[GoalDependency]] = None,
	intermediate_lineages: Optional[Dict[int, SelectedLineage]] = None,
	goal_slices: Optional[List["GoalSlice"]] = None,
	goals_out_dir: Optional[Path] = None,
) -> None:
	lines: List[str] = []
	# NOTE: In Lean, `import` must come before any commands. A module doc comment
	# `/-! ... -/` counts as a command, so we use a plain block comment here.
	lines.append(f"/- Auto-generated by Verdict/graph_to_lean.py")
	lines.append(f"    Module: {module_name}")
	lines.append(f"-/")
	lines.append("import denote.Denote")
	lines.append("")
	lines.append("set_option linter.style.longLine false")
	lines.append("set_option linter.style.nativeDecide false")
	lines.append("")
	lines.append("open TrainVerify.Denote")
	lines.append("")
	lines.append("namespace TrainVerify.Denote.Generated")
	lines.append("")

	def _emit_graph(name: str, nodes: List[Any], G: Any) -> None:
		lines.append(f"def {name} : GraphDecl := by")
		# numRanks: SM is 1, PM is inferred from max rank + 1.
		if name == "sm" or name.startswith("sm_"):
			num_ranks = 1
		else:
			num_ranks = max((_node_rank(n) for n in nodes), default=0) + 1
		lines.append(f"  refine {{ numRanks := {num_ranks}, nodes := ?_ }}")
		lines.append("  exact [")
		for n in nodes:
			op = escape_lean_string(_safe_str_op(G.node_opname(n)))
			ins = [int(t.tid) for t in G.node_inputs(n)]
			outs = [int(t.tid) for t in G.node_outputs(n)]
			rank = _node_rank(n)

			def _is_consecutive(xs: List[int]) -> tuple[bool, int, int]:
				if not xs:
					return (False, 0, 0)
				for i in range(1, len(xs)):
					if xs[i] != xs[0] + i:
						return (False, 0, 0)
				return (True, xs[0], len(xs))

			def _lean_list_nat_expr(xs: List[int]) -> str:
				ok, base, n = _is_consecutive(xs)
				# Emit a symbolic range/map when it is clearly a consecutive interval.
				if ok and n >= 4:
					return f"((List.range {n}).map (fun r => {base} + r))"
				return lean_list_nat(xs)

			lines.append(
				f"    {{ rank := {rank}, op := \"{op}\", ins := {_lean_list_nat_expr(ins)}, outs := {_lean_list_nat_expr(outs)} }},"
			)
		lines.append("  ]")
		lines.append("")

	_emit_graph("sm", sm_nodes, sm_graph)
	_emit_graph("pm", pm_nodes, pm_graph)

	# When a boundary tid exists in both SM and PM, it is usually a shared input (e.g. activations,
	# labels, loss-grad). Prefer the SM shape for those tids to avoid backend-specific ambiguities
	# in the PM tensor registry.
	# This is crucial for the decidable `graphShapesCheck` gate.
	_sm_prefer: Dict[int, List[int]] = _build_sm_prefer(sm_graph, sm_nodes)

	_emit_init_env(lines, name="sm", G=sm_graph, kept_nodes=sm_nodes)
	_emit_init_env(lines, name="pm", G=pm_graph, kept_nodes=pm_nodes, prefer_shapes=_sm_prefer)

	def _emit_goal_def(def_name: str, g: SelectedLineage, *, for_init: bool) -> None:
		ts_shape = _shape_init_from_graph_by_tid(sm_graph, g.ts)[0] or []
		tp_shapes: List[List[int]] = []
		# Same preference logic as init env: if a tp tid is a shared boundary tid, prefer SM shape.
		_sm_prefer_local: Dict[int, List[int]] = {}
		for tid, shp in _sm_prefer.items():
			_sm_prefer_local[int(tid)] = list(shp)
		for (_r, tp_tid) in g.tps:
			if int(tp_tid) in _sm_prefer_local:
				tp_shapes.append(list(_sm_prefer_local[int(tp_tid)]))
			else:
				shp, _init = _shape_init_from_graph_by_tid(pm_graph, tp_tid)
				tp_shapes.append(shp or [])
		
		# Validation: check if the shapes are consistent for reconstruction
		num_pieces = len(g.tps)
		if num_pieces > 1 and ts_shape and ts_shape != [1] and tp_shapes and tp_shapes[0]:
			# For allGather-style reconstruction, expect: tp_shape = ts_shape[:-1] + [ts_shape[-1] // num_pieces]
			if len(ts_shape) >= 1:
				expected_tp_shape = list(ts_shape[:-1]) + [ts_shape[-1] // num_pieces] if ts_shape[-1] % num_pieces == 0 else None
				actual_tp_shape = tp_shapes[0]
				if expected_tp_shape and actual_tp_shape != expected_tp_shape:
					print(f"WARNING: Shape mismatch for ts={g.ts}")
					print(f"  ts_shape: {ts_shape}")
					print(f"  num_pieces: {num_pieces}")
					print(f"  expected tp_shape (for allGather): {expected_tp_shape}")
					print(f"  actual tp_shape in PM graph: {actual_tp_shape}")
					print(f"  tp_tids: {[tid for (_r, tid) in g.tps]}")
					print(f"  This may indicate: (1) lineage inference error, (2) PM graph issue, or (3) non-standard parallelization")

		# NOTE: Keep `tps` and `tpShapes` as concrete lists.
		# Reason: `reconstruct` performs `match` on the tensor list; if `tps` is symbolic
		# (e.g. `List.range.map`), Lean cannot reduce the match and simp becomes unusable.
		tps_expr = "[" + ", ".join(f"{{ rank := {r}, tid := {t} }}" for r, t in g.tps) + "]"
		tp_shapes_expr = "[" + ", ".join("[" + ", ".join(str(int(x)) for x in shp) + "]" for shp in tp_shapes) + "]"

		lines.append(f"def {def_name} : LineageGoal :=")
		lines.append(
			"  { ts := "
			+ str(g.ts)
			+ ", tsShape := "
			+ ("[" + ", ".join(str(int(x)) for x in ts_shape) + "]")
			+ ", tps := "
			+ tps_expr
			+ ", tpShapes := "
			+ tp_shapes_expr
			+ " }"
		)
		lines.append("")

	# Initial-alignment goals: boundary inputs/params that must match between SM and PM.
	init_def_names: List[str] = []
	for g in init_goals:
		def_name = f"initGoal_{g.ts}"
		init_def_names.append(def_name)
		_emit_goal_def(def_name, g, for_init=True)

	lines.append("def initGoals : List LineageGoal := [" + ", ".join(init_def_names) + "]")
	lines.append("")

	# Goals: one per observable output.
	lines.append("def obsTids : List Nat := [" + ", ".join(str(g.ts) for g in goals) + "]")
	lines.append("")
	goal_def_names: List[str] = []
	for g in goals:
		def_name = f"goal_{g.ts}"
		goal_def_names.append(def_name)
		_emit_goal_def(def_name, g, for_init=False)

	lines.append("def goals : List LineageGoal := [" + ", ".join(goal_def_names) + "]")
	lines.append("")

	# Proposition aliases (no proofs): manual proofs should live in a separate, non-generated file.
	# Also emit a *decidable* shape-level check that can be discharged automatically.
	lines.append("-- Auto shape/dimension checks (decidable, fail-fast)\n")
	lines.append("def smShapeCheck : Except String (List (Tid × Shape)) :=")
	lines.append("  TrainVerify.Denote.graphShapesCheck sm smInitShapes")
	lines.append("")
	lines.append("def pmShapeCheck : Except String (List (Tid × Shape)) :=")
	lines.append("  TrainVerify.Denote.graphShapesCheck pm pmInitShapes")
	lines.append("")
	lines.append("theorem smShapeCheck_ok : smShapeCheck.isOk := by")
	lines.append("  native_decide")
	lines.append("")
	lines.append("theorem smShapeCheck_exists : ∃ m, smShapeCheck = Except.ok m := by")
	lines.append("  exact (TrainVerify.Denote.Except.isOk_iff_exists smShapeCheck).1 smShapeCheck_ok")
	lines.append("")
	lines.append("theorem pmShapeCheck_ok : pmShapeCheck.isOk := by")
	lines.append("  native_decide")
	lines.append("")
	lines.append("theorem pmShapeCheck_exists : ∃ m, pmShapeCheck = Except.ok m := by")
	lines.append("  exact (TrainVerify.Denote.Except.isOk_iff_exists pmShapeCheck).1 pmShapeCheck_ok")
	lines.append("")

	# Small unfold lemma for SM denotation (SM graphs are typically tiny and single-rank).
	# This avoids repeatedly rewriting foldl by hand in proofs.
	if len(sm_nodes) <= 24:
		lines.append("theorem sm_denoteGraph_unfold (init : Store) :")
		lines.append("    denoteGraph sm init =")
		# Build a nested applyNode chain with the concrete node decls.
		def _node_lit(n: Any, G: Any) -> str:
			op = escape_lean_string(_safe_str_op(G.node_opname(n)))
			ins = [int(t.tid) for t in G.node_inputs(n)]
			outs = [int(t.tid) for t in G.node_outputs(n)]
			rank = _node_rank(n)
			return (
				"{ "
				+ f"rank := {rank}, op := \"{op}\", ins := {lean_list_nat(ins)}, outs := {lean_list_nat(outs)}"
				+ " }"
			)

		sm_node_lits = [_node_lit(n, sm_graph) for n in sm_nodes]
		expr = "init"
		for lit in sm_node_lits:
			expr = f"applyNode sm ({expr}) ({lit})"
		lines.append(f"      {expr} := by")
		# `simp [denoteGraph]` computes the fold over the concrete node list.
		lines.append("  simp [sm, denoteGraph]")
		lines.append("")

	# NOTE: Fully unfolding PM denotation into nested `applyNode` chains quickly becomes enormous
	# and is usually counterproductive. We only emit the full unfold lemma for very small PM graphs.
	if len(pm_nodes) <= 24:
		lines.append("theorem pm_denoteGraph_unfold (init : Store) :")
		lines.append("    denoteGraph pm init =")
		pm_node_lits = [_node_lit(n, pm_graph) for n in pm_nodes]
		expr = "init"
		for lit in pm_node_lits:
			expr = f"applyNode pm ({expr}) ({lit})"
		lines.append(f"      {expr} := by")
		lines.append("  simp [pm, denoteGraph_nodes_cons, denoteGraph_nodes_nil]")
		lines.append("")

	# For scalar-style goals (tsShape=[1]) it is useful to expose a PM *prefix* and show that
	# later nodes do not overwrite the per-rank scalar shards used by reconstruct.
	# This avoids generating / using a gigantic full-PM unfold.
	def _is_scalar_goal(g: SelectedLineage) -> bool:
		# SelectedLineage does not carry shapes; infer via SM graph registry.
		try:
			sh_ts, _ = _shape_init_from_graph_by_tid(sm_graph, int(g.ts))
			return sh_ts == [1] and len(list(getattr(g, "tps", []))) >= 2
		except Exception:
			return False

	# NOTE: Prefix/suffix split and tid preservation lemmas are disabled for large graphs
	# because simpa with graph unfolding causes timeout.
	# For large graphs, users should prove these manually using denoteGraph_nodes_append
	# and denoteGraph_tid_eq_of_forall_not_mem_outs.
	scalar_goals = [g for g in goals if _is_scalar_goal(g)]
	if scalar_goals and len(pm_nodes) <= 20:  # Only for small graphs
		g0 = scalar_goals[0]
		target_tids = {int(tid) for (_r, tid) in list(g0.tps)}
		# find the last PM node that writes any target tid
		last_idx = -1
		for i, n in enumerate(pm_nodes):
			outs_i = {int(t.tid) for t in pm_graph.node_outputs(n)}
			if outs_i.intersection(target_tids):
				last_idx = i
		if last_idx >= 0 and last_idx + 1 < len(pm_nodes):
			prefix_nodes = pm_nodes[: last_idx + 1]
			suffix_nodes = pm_nodes[last_idx + 1 :]
			prefix_name = f"pm_prefix_goal_{int(g0.ts)}"
			suffix_name = f"pm_suffix_goal_{int(g0.ts)}"
			pm_num_ranks = max((_node_rank(n) for n in pm_nodes), default=0) + 1
			# Emit explicit prefix/suffix graphs.
			lines.append(f"def {prefix_name} : GraphDecl := by")
			lines.append(f"  refine {{ numRanks := {pm_num_ranks}, nodes := ?_ }}")
			lines.append("  exact [")
			for n in prefix_nodes:
				lines.append(f"    {_node_lit(n, pm_graph)},")
			lines.append("  ]")
			lines.append("")
			lines.append(f"def {suffix_name} : GraphDecl := by")
			lines.append(f"  refine {{ numRanks := {pm_num_ranks}, nodes := ?_ }}")
			lines.append("  exact [")
			for n in suffix_nodes:
				lines.append(f"    {_node_lit(n, pm_graph)},")
			lines.append("  ]")
			lines.append("")
			# Split lemma: pm nodes = prefix ++ suffix
			lines.append(f"theorem pm_split_goal_{int(g0.ts)} (init : Store) :")
			lines.append(
				f"    denoteGraph pm init = denoteGraph {suffix_name} (denoteGraph {prefix_name} init) := by"
			)
			lines.append("  -- purely definitional fold over concatenated node lists")
			lines.append("  -- use the generic append lemma with an empty graph (same numRanks)")
			lines.append(
				f"  simpa [pm, {prefix_name}, {suffix_name}] using (denoteGraph_nodes_append"
				f"    (g := {{ numRanks := pm.numRanks, nodes := [] }})"
				f"    (xs := {prefix_name}.nodes) (ys := {suffix_name}.nodes) init)"
			)
			lines.append("")
			# Pointwise lemmas for each target tid: suffix does not overwrite it
			for tid in sorted(target_tids):
				lines.append(f"theorem pm_tid_{tid}_eq_prefix_goal_{int(g0.ts)} (init : Store) :")
				lines.append(
					f"    (denoteGraph pm init) {tid} = (denoteGraph {prefix_name} init) {tid} := by"
				)
				lines.append(f"  have hsplit := pm_split_goal_{int(g0.ts)} init")
				lines.append(f"  -- show suffix does not write tid={tid} (computable) and use preservation lemma")
				lines.append(
					f"  have hpres : (denoteGraph {suffix_name} (denoteGraph {prefix_name} init)) {tid} ="
					f"      (denoteGraph {prefix_name} init) {tid} := by"
				)
				lines.append(f"    have hno : ∀ n ∈ {suffix_name}.nodes, {tid} ∉ n.outs := by native_decide")
				lines.append(
					f"    simpa using (denoteGraph_tid_eq_of_forall_not_mem_outs {suffix_name} {suffix_name}.nodes"
					f"      (denoteGraph {prefix_name} init) {tid} hno)"
				)
				lines.append(f"  -- rewrite using the split")
				lines.append(f"  simpa [hsplit] using hpres")
				lines.append("")

	# Build dependency map for goals
	deps_by_ts: Dict[int, GoalDependency] = {}
	if goal_deps:
		for dep in goal_deps:
			deps_by_ts[dep.goal_ts] = dep
	
	# Emit intermediate lineage goal definitions (for shared intermediate tensors)
	intermediate_def_names: List[str] = []
	if intermediate_lineages:
		lines.append("-- Intermediate tensor lineage goals (shared by multiple output goals)")
		for inter_ts, inter_lin in sorted(intermediate_lineages.items()):
			def_name = f"intermediateGoal_{inter_ts}"
			intermediate_def_names.append(def_name)
			_emit_goal_def(def_name, inter_lin, for_init=False)
		lines.append(f"def intermediateGoals : List LineageGoal := [{', '.join(intermediate_def_names)}]")
		lines.append("")
		
		# Also emit stmt definitions for intermediate goals
		lines.append("-- Proof obligations (intermediate goals)")
		for def_name in intermediate_def_names:
			lines.append(f"def {def_name}_stmt : Prop :=")
			lines.append(f"  CoarseLineageHoldsWithInit sm pm {def_name} smInitEnv pmInitEnv initGoals")
			lines.append("")

	for def_name in goal_def_names:
		goal_ts = int(def_name.split("_")[1])  # Extract ts from "goal_XXX"
		dep = deps_by_ts.get(goal_ts)
		
		# Check if this goal has prerequisites
		if dep and dep.prereq_intermediate_goals:
			prereq_goal_names = [f"intermediateGoal_{inter_ts}" for (inter_ts, _) in dep.prereq_intermediate_goals]
			prereq_list = "[" + ", ".join(prereq_goal_names) + "]"
			
			lines.append(f"-- goal_{goal_ts} depends on intermediate tensors: {[ts for (ts, _) in dep.prereq_intermediate_goals]}")
			lines.append(f"def {def_name}_prereqs : List LineageGoal := {prereq_list}")
			lines.append("")
			
			# Generate incremental statement: assuming prereqs hold, prove this goal
			lines.append(f"def {def_name}_stmt_incremental : Prop :=")
			lines.append(f"  CoarseLineageHoldsWithIntermediates sm pm {def_name} smInitEnv pmInitEnv initGoals {def_name}_prereqs")
			lines.append("")
			
			# Also keep the original full statement for reference
			lines.append(f"def {def_name}_stmt : Prop :=")
			lines.append(f"  CoarseLineageHoldsWithInit sm pm {def_name} smInitEnv pmInitEnv initGoals")
			lines.append("")
		else:
			lines.append(f"def {def_name}_stmt : Prop :=")
			lines.append(f"  CoarseLineageHoldsWithInit sm pm {def_name} smInitEnv pmInitEnv initGoals")
			lines.append("")

		# One proof stub per observable lineage goal
		lines.append(f"theorem prove_{def_name} : {def_name}_stmt := by")
		lines.append("  sorry")
		lines.append("")

	lines.append("def all_goals_stmt : Prop :=")
	lines.append("  ∀ g ∈ goals, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals")
	lines.append("")
	
	# ===========================================================================
	# Auto-generate SM tid computation lemmas
	# ===========================================================================
	
	sm_goal_tids: set[int] = set()
	for g in goals:
		sm_goal_tids.add(int(g.ts))
	
	# Also add intermediate tensor tids
	sm_intermediate_tids: set[int] = set()
	for n in sm_nodes:
		for t in sm_graph.node_outputs(n):
			tid = int(t.tid)
			if tid not in sm_goal_tids:
				sm_intermediate_tids.add(tid)
	
	# Build SM node index
	sm_tid_to_node_idx: Dict[int, int] = {}
	sm_tid_to_node: Dict[int, Any] = {}
	for i, n in enumerate(sm_nodes):
		for t in sm_graph.node_outputs(n):
			sm_tid_to_node_idx[int(t.tid)] = i
			sm_tid_to_node[int(t.tid)] = n
	
	if (sm_goal_tids or sm_intermediate_tids) and len(sm_nodes) <= 24:
		lines.append("/-!")
		lines.append("## Auto-generated SM tid computation lemmas")
		lines.append("")
		lines.append("These lemmas show what each SM tid computes in terms of the init store.")
		lines.append("-/")
		lines.append("")
		
		for tid in sorted(sm_goal_tids | sm_intermediate_tids):
			if tid not in sm_tid_to_node_idx:
				continue
			
			node = sm_tid_to_node[tid]
			op = _safe_str_op(sm_graph.node_opname(node))
			ins = [int(t.tid) for t in sm_graph.node_inputs(node)]
			outs = [int(t.tid) for t in sm_graph.node_outputs(node)]
			out_idx = outs.index(tid) if tid in outs else 0
			
			lines.append(f"theorem sm_tid_{tid}_eq (init : Store) :")
			
			# Build expression using init store for inputs that are init tids
			sm_init_tids_set = set(_init_tids_from_kept_nodes(sm_graph, sm_nodes))
			
			def _expr_for_tid(t: int) -> str:
				if t in sm_init_tids_set:
					return f"init {t}"
				else:
					return f"denoteGraph sm init {t}"
			
			if "FW_linear" in op:
				if len(ins) >= 2:
					lines.append(f"    (denoteGraph sm init) {tid} = fw_linear ({_expr_for_tid(ins[0])}) ({_expr_for_tid(ins[1])}) := by")
			elif "FW_sum" in op:
				if len(ins) >= 1:
					lines.append(f"    (denoteGraph sm init) {tid} = fw_sum ({_expr_for_tid(ins[0])}) := by")
			elif "BW_sum" in op:
				if len(ins) >= 2:
					lines.append(f"    (denoteGraph sm init) {tid} = bw_sum ({_expr_for_tid(ins[0])}) ({_expr_for_tid(ins[1])}) := by")
			elif "BW_linear" in op:
				if len(ins) >= 3:
					if out_idx == 0:
						lines.append(f"    (denoteGraph sm init) {tid} = (bw_linear ({_expr_for_tid(ins[0])}) ({_expr_for_tid(ins[1])}) ({_expr_for_tid(ins[2])})).1 := by")
					else:
						lines.append(f"    (denoteGraph sm init) {tid} = (bw_linear ({_expr_for_tid(ins[0])}) ({_expr_for_tid(ins[1])}) ({_expr_for_tid(ins[2])})).2 := by")
			else:
				lines.append(f"    True := by  -- op: {op}")
				lines.append("  trivial")
				lines.append("")
				continue
			
			lines.append("  simp only [sm_denoteGraph_unfold, applyNode, evalOp, storeSet, List.map, List.zip]")
			lines.append("  rfl")
			lines.append("")
	
	# NOTE: PM init tid preservation lemmas are expensive to prove automatically.
	# Instead, users can prove them manually using denoteGraph_tid_eq_of_forall_not_mem_outs.
	pm_init_tids = set(_init_tids_from_kept_nodes(pm_graph, pm_nodes))
	if pm_init_tids:
		lines.append("/-!")
		lines.append("## PM init tids")
		lines.append("")
		lines.append(f"The following tids are PM init tids (not written by any PM node): {sorted(pm_init_tids)}")
		lines.append("")
		lines.append("To prove `(denoteGraph pm init) tid = init tid` for an init tid,")
		lines.append("use `denoteGraph_tid_eq_of_forall_not_mem_outs` with `native_decide`")
		lines.append("to show no node outputs that tid.")
		lines.append("-/")
		lines.append("")
	
	# Emit composition theorems showing how to use incremental proofs
	if goal_deps and intermediate_lineages:
		lines.append("/-!")
		lines.append("## Incremental Proof Strategy")
		lines.append("")
		lines.append("The goals have the following dependency structure:")
		for dep in goal_deps:
			if dep.prereq_intermediate_goals:
				prereq_tids = [ts for (ts, _) in dep.prereq_intermediate_goals]
				lines.append(f"- goal_{dep.goal_ts} depends on intermediate tensors: {prereq_tids}")
			else:
				lines.append(f"- goal_{dep.goal_ts} has no prerequisites (base case)")
		lines.append("")
		lines.append("To prove `goal_X_stmt` from `goal_X_stmt_incremental`, use")
		lines.append("`CoarseLineageHoldsWithInit_of_incremental` with proofs of the prerequisite")
		lines.append("intermediate goals.")
		lines.append("-/")
		lines.append("")
		
		# Generate composition theorems for each goal with prerequisites
		for dep in goal_deps:
			if dep.prereq_intermediate_goals:
				goal_ts = dep.goal_ts
				prereq_goal_names = [f"intermediateGoal_{inter_ts}" for (inter_ts, _) in dep.prereq_intermediate_goals]
				
				lines.append(f"theorem goal_{goal_ts}_of_incremental")
				lines.append(f"    (hincr : goal_{goal_ts}_stmt_incremental)")
				for pg in prereq_goal_names:
					lines.append(f"    (h{pg} : {pg}_stmt)")
				lines.append(f"    : goal_{goal_ts}_stmt := by")
				lines.append(f"  unfold goal_{goal_ts}_stmt goal_{goal_ts}_stmt_incremental at *")
				lines.append(f"  apply CoarseLineageHoldsWithInit_of_incremental")
				lines.append(f"  · exact hincr")
				lines.append(f"  · intro g hg")
				lines.append(f"    simp only [goal_{goal_ts}_prereqs, List.mem_cons, List.mem_nil_iff] at hg")
				
				# Generate pattern match for each prerequisite
				if len(prereq_goal_names) == 1:
					lines.append(f"    cases hg with")
					lines.append(f"    | inl h => subst h; exact h{prereq_goal_names[0]}")
					lines.append(f"    | inr h => exact False.elim h")
				else:
					for i, pg in enumerate(prereq_goal_names):
						if i == 0:
							lines.append(f"    cases hg with")
							lines.append(f"    | inl h => subst h; exact h{pg}")
							lines.append(f"    | inr hg =>")
						elif i == len(prereq_goal_names) - 1:
							lines.append(f"      cases hg with")
							lines.append(f"      | inl h => subst h; exact h{pg}")
							lines.append(f"      | inr h => exact False.elim h")
						else:
							lines.append(f"      cases hg with")
							lines.append(f"      | inl h => subst h; exact h{pg}")
							lines.append(f"      | inr hg =>")
				lines.append("")

	# Goal-sliced graphs are emitted into per-goal files (if requested).
	if goal_slices and goals_out_dir is not None:
		goals_out_dir.mkdir(parents=True, exist_ok=True)
		deps_by_ts: Dict[int, GoalDependency] = {}
		if goal_deps:
			for dep in goal_deps:
				deps_by_ts[dep.goal_ts] = dep

		for sl in goal_slices:
			goal_ts = int(sl.goal.ts)
			dep = deps_by_ts.get(goal_ts)
			file_path = goals_out_dir / f"Goal_{goal_ts}.lean"
			goal_lines: List[str] = []
			goal_lines.append("/- Auto-generated by Verdict/graph_to_lean.py")
			goal_lines.append(f"    Goal: {goal_ts}")
			goal_lines.append("-/")
			goal_lines.append("import denote.GeneratedData")
			goal_lines.append("")
			goal_lines.append("open TrainVerify.Denote")
			goal_lines.append("open TrainVerify.Denote.Generated")
			goal_lines.append("")
			goal_lines.append("namespace TrainVerify.Denote.GeneratedGoals")
			goal_lines.append("")

			sm_name = f"sm_goal_{goal_ts}"
			pm_name = f"pm_goal_{goal_ts}"

			# Emit sliced graphs
			def _emit_graph_local(name: str, nodes: List[Any], G: Any) -> None:
				goal_lines.append(f"def {name} : GraphDecl := by")
				if name.startswith("sm_"):
					num_ranks = 1
				else:
					num_ranks = max((_node_rank(n) for n in nodes), default=0) + 1
				goal_lines.append(f"  refine {{ numRanks := {num_ranks}, nodes := ?_ }}")
				goal_lines.append("  exact [")
				for n in nodes:
					op = escape_lean_string(_safe_str_op(G.node_opname(n)))
					ins = [int(t.tid) for t in G.node_inputs(n)]
					outs = [int(t.tid) for t in G.node_outputs(n)]
					rank = _node_rank(n)
					goal_lines.append(
						f"    {{ rank := {rank}, op := \"{op}\", ins := {lean_list_nat(ins)}, outs := {lean_list_nat(outs)} }},"
					)
				goal_lines.append("  ]")
				goal_lines.append("")

			_emit_graph_local(sm_name, sl.sm_nodes, sm_graph)
			_emit_graph_local(pm_name, sl.pm_nodes, pm_graph)

			# Local init envs (boundary tids of the sliced subgraphs)
			_sm_prefer_local = _build_sm_prefer(sm_graph, sl.sm_nodes)
			_emit_init_env(goal_lines, name=sm_name, G=sm_graph, kept_nodes=sl.sm_nodes)
			_emit_init_env(goal_lines, name=pm_name, G=pm_graph, kept_nodes=sl.pm_nodes, prefer_shapes=_sm_prefer_local)

			# Local init goals: base initGoals plus prerequisite intermediate goals.
			if dep and dep.prereq_intermediate_goals:
				goal_lines.append(
					f"def goal_{goal_ts}_cut_initGoals : List LineageGoal := initGoals ++ goal_{goal_ts}_prereqs"
				)
			else:
				goal_lines.append(f"def goal_{goal_ts}_cut_initGoals : List LineageGoal := initGoals")
			goal_lines.append("")

			goal_lines.append(f"def goal_{goal_ts}_stmt_cut : Prop :=")
			goal_lines.append(
				f"  CoarseLineageHoldsWithInit {sm_name} {pm_name} goal_{goal_ts}"
				f" {sm_name}InitEnv {pm_name}InitEnv goal_{goal_ts}_cut_initGoals"
			)
			goal_lines.append("")
			goal_lines.append("end TrainVerify.Denote.GeneratedGoals")
			goal_lines.append("")

			file_path.write_text("\n".join(goal_lines) + "\n", encoding="utf-8")

	lines.append("end TrainVerify.Denote.Generated")
	lines.append("")

	out_path.parent.mkdir(parents=True, exist_ok=True)
	out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

	if emit_spec_template and spec_out_path is not None:
		if spec_out_path.exists() and not overwrite_spec:
			print(f"Spec template exists, not overwriting: {spec_out_path}")
			return

		# Proof template lives in a separate namespace/module, and intentionally uses `sorry`.
		spec_lines: List[str] = []
		spec_lines.append("/-")
		spec_lines.append("Auto-generated proof template for the denotational spec.")
		spec_lines.append("")
		spec_lines.append("- This file is meant to be edited by humans.")
		spec_lines.append("- It is generated only when --emit-spec-template is passed.")
		spec_lines.append("- Proofs are left as `sorry` stubs initially.")
		spec_lines.append("-/")
		spec_lines.append("import denote.GeneratedData")
		spec_lines.append("")
		spec_lines.append("open TrainVerify.Denote")
		spec_lines.append("open TrainVerify.Denote.Generated")
		spec_lines.append("")
		spec_lines.append("namespace TrainVerify.Denote.GeneratedSpec")
		spec_lines.append("")
		spec_lines.append("/-!\n## Proof stubs\n\nFill these in manually. No axioms are introduced here.\n-/")
		spec_lines.append("")
		# One theorem stub per goal.
		for g in goals:
			name = f"prove_goal_{g.ts}"
			spec_lines.append(f"theorem {name} : goal_{g.ts}_stmt := by")
			spec_lines.append("  -- TODO: fill in the proof")
			spec_lines.append("  sorry")
			spec_lines.append("")

		spec_lines.append("theorem prove_all_goals : all_goals_stmt := by")
		spec_lines.append("  -- TODO: finish after prove_goal_* are done")
		spec_lines.append("  sorry")
		spec_lines.append("")
		spec_lines.append("end TrainVerify.Denote.GeneratedSpec")
		spec_lines.append("")

		spec_out_path.parent.mkdir(parents=True, exist_ok=True)
		spec_out_path.write_text("\n".join(spec_lines) + "\n", encoding="utf-8")


def main() -> None:
	args = parse_args()
	out_path = Path(args.out)
	spec_out_path = Path(args.spec_out)

	v = load_verifier(args.sm_pkl, args.pm_pkl)
	GsE, GpE = v.get_graph()  # expanded
	GsC, _GpC = v.get_graph_compact()  # compact (stable for leaf detection)

	coarse = infer_coarse_lineages_from_expanded(GsE, GpE)
	by_ts: Dict[int, List[Any]] = {}
	for l in coarse:
		Ts = getattr(l, "Ts")
		by_ts.setdefault(int(Ts.tid), []).append(l)

	# Observable outputs: aligned leaves by default.
	candidates = leaf_output_tids(GsC)
	obs_tids = [tid for tid in candidates if tid in by_ts]
	if args.max_goals and args.max_goals > 0:
		obs_tids = obs_tids[: int(args.max_goals)]

	selected: List[SelectedLineage] = []
	for ts in obs_tids:
		chosen = pick_one_lineage_for_ts(by_ts.get(int(ts), []), ts)
		if chosen is not None:
			chosen = normalize_lineage_by_collectives(GpE, chosen)
			chosen = compress_if_replicated(chosen)
			selected.append(chosen)

	selected.sort(key=lambda g: g.ts)

	# Restrict graph declarations to the subgraph needed for the selected goals.
	sm_needed_tids = backward_closure_tids(GsC, [g.ts for g in selected])
	pm_roots = [tp_tid for g in selected for (_, tp_tid) in g.tps]
	pm_needed_tids = backward_closure_tids(GpE, pm_roots)

	def _filter_nodes(G: Any, needed_tids: set[int], stop_tids: Optional[set[int]] = None) -> List[Any]:
		kept: List[Any] = []
		for n in G.nodes():
			outs = [int(t.tid) for t in G.node_outputs(n)]
			# Skip DATALOADER in denotational semantics: treat those tensors as coming from init store.
			opname = _safe_str_op(G.node_opname(n))
			if "DATALOADER" in opname:
				continue
			if stop_tids is None:
				if any(tid in needed_tids for tid in outs):
					kept.append(n)
				continue
			# For sliced graphs: drop nodes that only produce stop-tids.
			if any((tid in needed_tids) and (tid not in stop_tids) for tid in outs):
				kept.append(n)
		return kept

	def _dedup_shared_collectives(G: Any, nodes: List[Any]) -> List[Any]:
		"""Drop redundant per-rank copies of shared-output collectives.

		Many backends represent AllReduce/AllGather as one node per rank, but with the same
		(output) tid because the result is identical across ranks. In our denotational store
		model (keyed only by tid), keeping all of them would introduce multiple writes to the
		same tid and complicate proofs.

		We keep a single representative (lowest rank) for each collective identified by
		(op, inputs, outputs).
		"""
		groups: Dict[tuple[str, tuple[int, ...], tuple[int, ...]], List[Any]] = {}
		for n in nodes:
			op = _safe_str_op(G.node_opname(n))
			if ("AllReducePrim" not in op) and ("AllGatherPrim" not in op):
				continue
			ins = tuple(int(t.tid) for t in G.node_inputs(n))
			outs = tuple(int(t.tid) for t in G.node_outputs(n))
			groups.setdefault((op, ins, outs), []).append(n)

		chosen: set[Any] = set()
		for (_k, ns) in groups.items():
			# Prefer the smallest rank.
			rep = min(ns, key=_node_rank)
			chosen.add(rep)

		out: List[Any] = []
		for n in nodes:
			op = _safe_str_op(G.node_opname(n))
			if ("AllReducePrim" in op) or ("AllGatherPrim" in op):
				if n in chosen:
					out.append(n)
			else:
				out.append(n)
		return out

	def _toposort_nodes(G: Any, nodes: List[Any]) -> List[Any]:
		"""Stable topo-sort of nodes across ranks by tid dependencies."""
		if len(nodes) <= 1:
			return nodes

		# Map tid -> producing node indices (can be >1 in imperfect graphs).
		producers: Dict[int, List[int]] = {}
		for i, n in enumerate(nodes):
			for t in G.node_outputs(n):
				producers.setdefault(int(t.tid), []).append(i)

		deps: List[set[int]] = [set() for _ in nodes]
		for i, n in enumerate(nodes):
			for t in G.node_inputs(n):
				for j in producers.get(int(t.tid), []):
					if j != i:
						deps[i].add(j)

		indeg = [len(deps_i) for deps_i in deps]
		# Stable queue: pick nodes with indeg=0 in original order.
		queue: List[int] = [i for i, d in enumerate(indeg) if d == 0]
		out_idx: List[int] = []
		while queue:
			i = queue.pop(0)
			out_idx.append(i)
			for k in range(len(nodes)):
				if i in deps[k]:
					deps[k].remove(i)
					indeg[k] -= 1
					if indeg[k] == 0:
						queue.append(k)

		# If cycle/unknown deps remain, fall back to original order.
		if len(out_idx) != len(nodes):
			return nodes
		return [nodes[i] for i in out_idx]

	sm_nodes = _filter_nodes(GsE, set(sm_needed_tids))
	pm_nodes = _filter_nodes(GpE, set(pm_needed_tids))

	# Ensure the denotational fold is a true topological fold across ranks.
	sm_nodes = _toposort_nodes(GsE, sm_nodes)
	pm_nodes = _toposort_nodes(GpE, _dedup_shared_collectives(GpE, pm_nodes))

	# Init/boundary tids for the kept subgraph (SM side). We'll generate init-alignment goals
	# only for those that the aligner can match.
	sm_init_tids = _init_tids_from_kept_nodes(GsE, sm_nodes)

	init_selected: List[SelectedLineage] = []
	for tid in sm_init_tids:
		chosen = pick_one_lineage_for_ts(by_ts.get(int(tid), []), int(tid))
		if chosen is None:
			continue
		chosen = normalize_lineage_by_collectives(GpE, chosen)
		init_selected.append(compress_if_replicated(chosen))
	init_selected.sort(key=lambda g: g.ts)

	# Compute goal dependencies to enable incremental proofs
	init_tid_set = set(sm_init_tids)
	goal_deps, intermediate_lineages = compute_goal_dependencies(
		GsC, selected, by_ts, init_tid_set
	)
	if intermediate_lineages:
		for k, lin in list(intermediate_lineages.items()):
			lin = normalize_lineage_by_collectives(GpE, lin)
			lin = compress_if_replicated(lin)
			intermediate_lineages[k] = lin

	# Light sanity checks for intermediate lineages used as prerequisites
	pm_num_ranks = max((_node_rank(n) for n in GpE.nodes()), default=0) + 1
	for dep in goal_deps:
		for (inter_ts, lin) in dep.prereq_intermediate_goals:
			issues = _validate_lineage_against_graphs(lin, GsE, GpE, pm_num_ranks)
			if issues:
				print(f"WARNING: lineage sanity check issues for intermediate ts={inter_ts}:")
				for msg in issues:
					print(f"  - {msg}")

	# Optional: build per-goal sliced graphs (cut at prerequisite intermediate tensors).
	goal_slices: Optional[List[GoalSlice]] = None
	if args.split_goals:
		deps_by_ts: Dict[int, GoalDependency] = {d.goal_ts: d for d in goal_deps}
		goal_slices = []
		for g in selected:
			dep = deps_by_ts.get(int(g.ts))
			prereq_lineages: List[SelectedLineage] = []
			if dep and dep.prereq_intermediate_goals:
				prereq_lineages = [lin for (_ts, lin) in dep.prereq_intermediate_goals]

			stop_sm_tids = set(sm_init_tids) | {int(lin.ts) for lin in prereq_lineages}
			needed_sm = backward_closure_tids_until(GsC, [int(g.ts)], stop_sm_tids)
			sm_nodes_goal = _filter_nodes(GsE, set(needed_sm), stop_tids=set(stop_sm_tids))
			sm_nodes_goal = _toposort_nodes(GsE, sm_nodes_goal)

			stop_pm_tids: set[int] = set()
			for lin in prereq_lineages:
				for (_r, tp_tid) in lin.tps:
					stop_pm_tids.add(int(tp_tid))
			pm_roots_goal = [int(tp_tid) for (_r, tp_tid) in g.tps]
			needed_pm = backward_closure_tids_until(GpE, pm_roots_goal, stop_pm_tids)
			pm_nodes_goal = _filter_nodes(GpE, set(needed_pm), stop_tids=set(stop_pm_tids))
			pm_nodes_goal = _dedup_shared_collectives(GpE, pm_nodes_goal)
			pm_nodes_goal = _toposort_nodes(GpE, pm_nodes_goal)

			goal_slices.append(GoalSlice(goal=g, sm_nodes=sm_nodes_goal, pm_nodes=pm_nodes_goal))
	
	# Print dependency info
	print("Goal dependencies (for incremental proofs):")
	for dep in goal_deps:
		if dep.prereq_intermediate_goals:
			prereq_tids = [ts for (ts, _) in dep.prereq_intermediate_goals]
			print(f"  goal_{dep.goal_ts} depends on intermediate tensors: {prereq_tids}")
		else:
			print(f"  goal_{dep.goal_ts} has no prerequisites")
	
	if intermediate_lineages:
		print(f"Intermediate lineage goals: {sorted(intermediate_lineages.keys())}")

	emit_lean_spec(
		out_path=out_path,
		spec_out_path=spec_out_path,
		emit_spec_template=bool(args.emit_spec_template),
		overwrite_spec=bool(args.overwrite_spec),
		module_name=str(args.module),
		sm_nodes=sm_nodes,
		pm_nodes=pm_nodes,
		sm_graph=GsE,
		pm_graph=GpE,
		init_goals=init_selected,
		goals=selected,
		goal_deps=goal_deps,
		intermediate_lineages=intermediate_lineages,
		goal_slices=goal_slices,
		goals_out_dir=Path(args.goals_out_dir) if args.split_goals else None,
	)

	print(f"Wrote Lean spec to: {out_path}")
	print(f"#goals: {len(selected)}  (obs tids: {', '.join(str(g.ts) for g in selected)})")
	print(f"#init-goals: {len(init_selected)}  (matched init tids: {', '.join(str(g.ts) for g in init_selected)})")

	# Lightweight check: report SM-side boundary tids and whether backend marks them initialized.
	print("Init tid report (SM kept-subgraph boundary):")
	for tid in sm_init_tids:
		shp, init_flag = _shape_init_from_graph_by_tid(GsE, int(tid))
		cons_ops = []
		for n in sm_nodes:
			try:
				ins = [int(t.tid) for t in GsE.node_inputs(n)]
			except Exception:
				ins = []
			if int(tid) in ins:
				cons_ops.append(_safe_str_op(GsE.node_opname(n)))
		print(f"  tid={tid} shape={shp} is_initialized={init_flag} consumers={cons_ops}")


if __name__ == "__main__":
	main()

