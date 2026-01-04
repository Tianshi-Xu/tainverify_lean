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
DEFAULT_PM_GRAPH = ROOT / "genmodel" / "mgeners" / "mlp_mgener_dp1_pp1_tp8_nm1_gbs128_dim128_ly1.pkl"
DEFAULT_OUT = ROOT / "mathlib4" / "trainverify" / "denote" / "GeneratedData.lean"


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
		default=str(ROOT / "mathlib4" / "trainverify" / "denote" / "GeneratedSpec.lean"),
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
) -> None:
	lines: List[str] = []
	# NOTE: In Lean, `import` must come before any commands. A module doc comment
	# `/-! ... -/` counts as a command, so we use a plain block comment here.
	lines.append(f"/- Auto-generated by Verdict/graph_to_lean.py")
	lines.append(f"    Module: {module_name}")
	lines.append(f"-/")
	lines.append("import trainverify.denote.Denote")
	lines.append("")
	lines.append("open TrainVerify.Denote")
	lines.append("")
	lines.append("namespace TrainVerify.Denote.Generated")
	lines.append("")

	def _emit_graph(name: str, nodes: List[Any], G: Any) -> None:
		lines.append(f"def {name} : GraphDecl := by")
		# numRanks: SM is 1, PM is inferred from max rank + 1.
		if name == "sm":
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
	_sm_prefer: Dict[int, List[int]] = {}
	# We derive the preference map from the SM-side inferred boundary tids.
	for tid in _init_tids_from_kept_nodes(sm_graph, sm_nodes):
		shp, _init = _shape_init_from_graph_by_tid(sm_graph, tid)
		if shp is not None:
			_sm_prefer[int(tid)] = [int(x) for x in shp]

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

	scalar_goals = [g for g in goals if _is_scalar_goal(g)]
	if scalar_goals:
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

	for def_name in goal_def_names:
		lines.append(f"def {def_name}_stmt : Prop :=")
		lines.append(f"  CoarseLineageHoldsWithInit sm pm {def_name} smInitEnv pmInitEnv initGoals")
		lines.append("")

	lines.append("def all_goals_stmt : Prop :=")
	lines.append("  ∀ g ∈ goals, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals")
	lines.append("")

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
		spec_lines.append("import trainverify.denote.GeneratedData")
		spec_lines.append("")
		spec_lines.append("open TrainVerify.Denote")
		spec_lines.append("open TrainVerify.Denote.Generated")
		spec_lines.append("")
		spec_lines.append("namespace TrainVerify.Denote.GeneratedSpec")
		spec_lines.append("")
		spec_lines.append("/-!\n## Shape gate\n\nThese are computable checks (proved by native_decide in GeneratedData).\n-/")
		spec_lines.append("theorem sm_shape_ok : smShapeCheck.isOk := by")
		spec_lines.append("  simpa using smShapeCheck_ok")
		spec_lines.append("")
		spec_lines.append("theorem pm_shape_ok : pmShapeCheck.isOk := by")
		spec_lines.append("  simpa using pmShapeCheck_ok")
		spec_lines.append("")

		# One theorem stub per goal.
		for g in goals:
			name = f"prove_goal_{g.ts}"
			spec_lines.append(f"theorem {name} : goal_{g.ts}_stmt := by")
			spec_lines.append("  classical")
			spec_lines.append("  -- Shape gate (computable, proved in GeneratedData via native_decide):")
			spec_lines.append("  have _hSm : smShapeCheck.isOk := sm_shape_ok")
			spec_lines.append("  have _hPm : pmShapeCheck.isOk := pm_shape_ok")
			spec_lines.append("")
			spec_lines.append("  -- Expand the statement into concrete obligations.")
			spec_lines.append(f"  unfold goal_{g.ts}_stmt CoarseLineageHoldsWithInit")
			spec_lines.append("  intro initSM initPM hSmInitShapes hPmInitShapes hInitGoals")
			spec_lines.append("")
			spec_lines.append("  -- Common next steps (uncomment as needed):")
			spec_lines.append("  -- simp [InitGoalsHold, InitGoalHolds] at hInitGoals")
			spec_lines.append("  -- simp [denoteGraph_nodes_cons, denoteGraph_nodes_nil]")
			spec_lines.append("  -- simp [valAt_of_fin]")
			spec_lines.append("  -- simp [applyNode, storeSet]  -- or use storeSet_eq_of_find?_some/none")
			spec_lines.append("  sorry")
			spec_lines.append("")

		spec_lines.append("theorem prove_all_goals : all_goals_stmt := by")
		spec_lines.append("  -- After proving each prove_goal_*, you can finish by cases on membership in goals.")
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
			selected.append(chosen)

	selected.sort(key=lambda g: g.ts)

	# Restrict graph declarations to the subgraph needed for the selected goals.
	sm_needed_tids = backward_closure_tids(GsC, [g.ts for g in selected])
	pm_roots = [tp_tid for g in selected for (_, tp_tid) in g.tps]
	pm_needed_tids = backward_closure_tids(GpE, pm_roots)

	def _filter_nodes(G: Any, needed_tids: set[int]) -> List[Any]:
		kept: List[Any] = []
		for n in G.nodes():
			outs = [int(t.tid) for t in G.node_outputs(n)]
			# Skip DATALOADER in denotational semantics: treat those tensors as coming from init store.
			opname = _safe_str_op(G.node_opname(n))
			if "DATALOADER" in opname:
				continue
			if any(tid in needed_tids for tid in outs):
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
		init_selected.append(compress_if_replicated(chosen))
	init_selected.sort(key=lambda g: g.ts)

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

