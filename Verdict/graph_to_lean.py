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
	--out trainverify/denote/gpt_ly4_regen/GeneratedData.lean \
	--module denote.gpt_ly4_regen.GeneratedData

Both --out and --module are required; pick the active model's emit dir
(e.g. `gpt_ly4_regen/`, `yoco_goals/`) so you don't overwrite another
model's snapshot.
"""

from __future__ import annotations

import argparse
from collections import deque
import hashlib
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parent.parent

DEFAULT_SM_GRAPH = ROOT / "genmodel" / "mgeners" / "attn_mgener_dp1_pp1_tp1_nm1_gbs16_dim128_seq64_nh8_ly1.pkl"
DEFAULT_PM_GRAPH = ROOT / "genmodel" / "mgeners" / "attn_mgener_dp1_pp1_tp4_nm1_gbs16_dim128_seq64_nh8_ly1.pkl"
# DO NOT add a DEFAULT_OUT. The previous default (`trainverify/denote/GeneratedData.lean`)
# silently overwrote the ly1 GeneratedData snapshot (now in `_archive/ly1/`), which made it
# easy to clobber the active model's generated graph by accident. Callers must pass --out.


def parse_args() -> argparse.Namespace:
	p = argparse.ArgumentParser(description="Generate Lean spec (denotational) + coarse lineage goals")
	p.add_argument("--sm-pkl", default=str(DEFAULT_SM_GRAPH), help="Path to SM graph pickle")
	p.add_argument("--pm-pkl", default=str(DEFAULT_PM_GRAPH), help="Path to PM graph pickle")
	p.add_argument(
		"--out",
		required=True,
		help="REQUIRED. Output Lean file path (e.g. trainverify/denote/gpt_ly4_regen/GeneratedData.lean).",
	)
	p.add_argument(
		"--module",
		required=True,
		help="REQUIRED. Lean module name used in the generated file header comment (must match --out path).",
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
		"--include-intermediate-goals",
		action="store_true",
		help=(
			"Also treat intermediate tensors (not just leaf outputs) as separate goals. "
			"This produces smaller per-goal graphs but more goals overall."
		),
	)
	p.add_argument(
		"--use-tid-goal-ids",
		action="store_true",
		help=(
			"Use tensor IDs for Goal file names instead of sequential IDs (1, 2, 3, ...). "
			"By default, sequential numbering is used for readability."
		),
	)
	p.add_argument(
		"--goals-out-dir",
		default=str(ROOT / "trainverify" / "denote"),
		help="Output directory for per-goal Lean files when --split-goals is enabled.",
	)
	p.add_argument(
		"--emit-segment-patterns",
		action="store_true",
		help=(
			"When --split-goals is enabled, also emit higher-level repeated segment "
			"patterns over concrete goal statements. This preserves all per-goal graph "
			"files and only adds reusable proof packages on top."
		),
	)
	p.add_argument(
		"--segment-max-goals",
		type=int,
		default=8,
		help="Maximum number of concrete goals in one segment proof obligation.",
	)
	p.add_argument(
		"--segment-min-repeats",
		type=int,
		default=2,
		help="Minimum number of repeated segment instances required before emitting a segment pattern.",
	)
	p.add_argument(
		"--segment-max-period",
		type=int,
		default=80,
		help="Maximum repeated period, measured in concrete goals, for segment detection.",
	)
	p.add_argument("--manifest-out", help="Write an immutable deterministic provenance manifest.")
	p.add_argument("--model", default="YOCO-MoE-A0.4B", help="Model identity recorded in the manifest.")
	p.add_argument("--metadata-json", action="append", default=[], help="Authority metadata JSON (repeatable).")
	p.add_argument("--llm-train-repo", help="Pinned llm-train git checkout used to create the authority artifacts.")
	p.add_argument("--nnscaler-repo", help="Pinned nnScaler git checkout used to create the authority artifacts.")
	p.add_argument("--llm-train-revision", help="Expected full llm-train commit; rejects a checkout mismatch.")
	p.add_argument("--nnscaler-revision", help="Expected full nnScaler commit; rejects a checkout mismatch.")
	p.add_argument("--sm-pkl-sha256", help="Expected SM pickle SHA-256; rejects an artifact mismatch.")
	p.add_argument("--pm-pkl-sha256", help="Expected PM pickle SHA-256; rejects an artifact mismatch.")
	p.add_argument(
		"--metadata-sha256", action="append", default=[], metavar="NAME=SHA256",
		help="Expected authority metadata hash (repeatable).",
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
	from verdict.graph import Lineage  # type: ignore

	Gs_alignable_ops = [n for n in GsE.nodes() if bl._is_original_op(GsE.node_opname(n))]
	Gp_alignable_ops = [n for n in GpE.nodes() if bl._is_original_op(GpE.node_opname(n))]
	print(
		f"[graph_to_lean] alignable ops: SM={len(Gs_alignable_ops)} PM={len(Gp_alignable_ops)}",
		flush=True,
	)
	Gp_grid = bl._reorganize_Gp_nodes(Gp_alignable_ops, GpE)
	lineages: List[Any] = []
	for node_ptr, snode in enumerate(Gs_alignable_ops):
		pnodes = [
			Gp_grid[dp][tp][mb][node_ptr]
			for dp in range(GpE.W.num_dp)
			for tp in range(GpE.W.num_tp)
			for mb in range(GpE.W.num_mb)
		]
		for input_ptr, Ts in enumerate(GsE.node_inputs(snode)):
			Tps = [GpE.node_inputs(pnode)[input_ptr] for pnode in pnodes]
			lineages.append(Lineage(Ts, Tps))
		for output_ptr, Ts in enumerate(GsE.node_outputs(snode)):
			Tps = [GpE.node_outputs(pnode)[output_ptr] for pnode in pnodes]
			lineages.append(Lineage(Ts, Tps))
	return lineages


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


def _infer_chunk_dim(in_shape: List[int], out_shape: List[int], num_parts: int) -> Optional[int]:
	"""Infer which dimension was chunked by comparing input/output shapes."""
	if len(in_shape) != len(out_shape):
		return None
	candidates = []
	for i, (si, so) in enumerate(zip(in_shape, out_shape)):
		if si != so:
			if num_parts > 0 and si == so * num_parts:
				candidates.append(i)
			else:
				return None
	return candidates[0] if len(candidates) == 1 else None


def _infer_gather_dim(shard_shape: List[int], full_shape: List[int], num_parts: int) -> Optional[int]:
	"""Infer which dimension was gathered by comparing shard/full shapes."""
	if len(shard_shape) != len(full_shape):
		return None
	candidates = []
	for i, (ss, sf) in enumerate(zip(shard_shape, full_shape)):
		if ss != sf:
			if num_parts > 0 and sf == ss * num_parts:
				candidates.append(i)
			else:
				return None
	return candidates[0] if len(candidates) == 1 else None


def _get_node_params(G: Any, n: Any, num_parts: int = 0) -> Optional[List[int]]:
	"""Extract Lean params for ops that need them.

	Supported ops and their params encoding:
	  - FW_view / BW_view: target shape (list of dims)
	  - FW_transpose / BW_transpose: [dim0, dim1]
	  - FW_div / BW_div: [divisor_int] from __consts (integer part)
	  - AllToAllPrim: [idim, odim] (shape-validated; backward nodes get [odim, idim])
	  - FW_multiref: [num_outputs]
	  - ChunkPrim: [chunk_dim]
	  - AllGatherPrim: [gather_dim]
	"""
	op = _safe_str_op(G.node_opname(n))
	if "FW_view" in op or "BW_view" in op:
		outs = G.node_outputs(n)
		if outs:
			return list(int(d) for d in G.tensor_shape(outs[0]))
	elif "FW_reshape" in op or "BW_reshape" in op:
		# Emit target output shape as params, so Denote can build a faithful reshape.
		# Historically FW_reshape params were empty and Denote modelled it as identity;
		# that's only valid when target shape == input shape (Pattern_1/2/4). Pattern_3
		# uses shape-changing reshape (e.g. attn output [seq, head, dim] -> [seq, head*dim])
		# so we need target shape. Same treatment as FW_view above.
		outs = G.node_outputs(n)
		if outs:
			return list(int(d) for d in G.tensor_shape(outs[0]))
	elif "FW_transpose" in op or "BW_transpose" in op:
		kwargs = G.node_kwargs(n)
		if "dim0" in kwargs and "dim1" in kwargs:
			d0, d1 = int(kwargs["dim0"]), int(kwargs["dim1"])
			ins = G.node_inputs(n)
			if ins:
				ndim = len(list(G.tensor_shape(ins[0])))
				if d0 < 0:
					d0 = ndim + d0
				if d1 < 0:
					d1 = ndim + d1
			return [d0, d1]
	elif "FW_div" in op or "BW_div" in op:
		kwargs = G.node_kwargs(n)
		consts = kwargs.get("__consts", [])
		if consts:
			return [int(consts[0])]
	elif "AllToAllPrim" in op:
		kwargs = G.node_kwargs(n)
		if "idim" in kwargs and "odim" in kwargs:
			idim, odim = int(kwargs["idim"]), int(kwargs["odim"])
			ins = G.node_inputs(n)
			outs = G.node_outputs(n)
			if ins:
				ndim = len(list(G.tensor_shape(ins[0])))
				if idim < 0:
					idim = ndim + idim
				if odim < 0:
					odim = ndim + odim
			# The Lean denotation `allToAllPrimWithDims xs idim odim` computes
			# `chunkPrimDimN odim (allGatherPrimDimN idim xs)`: it gathers the input
			# shards along `idim` (dim grows x numParts) and then chunks the result
			# along `odim` (dim shrinks / numParts). This matches nnscaler's forward
			# all_to_all (collectives.py: chunk input along odim, concat output along
			# idim). nnscaler's BACKWARD all_to_all (nn.py: `all_to_all(grad, odim,
			# idim)`) runs with idim/odim SWAPPED, but the traced node still reports
			# the forward kwargs. So for a backward node, emitting the raw
			# [idim, odim] makes the Lean def compute the wrong (often shape-invalid)
			# tensor. Pick the ordering whose Lean-def output shape matches the
			# node's recorded output shape; this selects [idim, odim] for forward
			# nodes and [odim, idim] for backward nodes, with no fw/bw heuristic.
			if ins and outs and num_parts > 0:
				in_shape = list(int(d) for d in G.tensor_shape(ins[0]))
				out_shape = list(int(d) for d in G.tensor_shape(outs[0]))

				def _a2a_out_shape(
					shard: List[int], gather_dim: int, chunk_dim: int
				) -> Optional[List[int]]:
					# Mirror `chunkPrimDimN chunk_dim (allGatherPrimDimN gather_dim shard)`.
					if not (
						0 <= gather_dim < len(shard) and 0 <= chunk_dim < len(shard)
					):
						return None
					gathered = list(shard)
					gathered[gather_dim] = gathered[gather_dim] * num_parts
					if gathered[chunk_dim] % num_parts != 0:
						return None
					gathered[chunk_dim] = gathered[chunk_dim] // num_parts
					return gathered

				direct = _a2a_out_shape(in_shape, idim, odim)
				swapped = _a2a_out_shape(in_shape, odim, idim)
				if direct == out_shape:
					return [idim, odim]
				if swapped == out_shape:
					# Backward all_to_all: emit swapped dims so the Lean def
					# (gather idim, chunk odim) reproduces the backward tensor.
					return [odim, idim]
				# Neither matched exactly (shape ambiguity / scalar dims): fall back
				# to the raw kwargs order to preserve prior behavior.
			return [idim, odim]
	elif "FW_multiref" in op:
		outs = G.node_outputs(n)
		return [len(outs)]
	elif "ChunkPrim" in op:
		ins = G.node_inputs(n)
		outs = G.node_outputs(n)
		if ins and outs and num_parts > 0:
			in_shape = list(int(d) for d in G.tensor_shape(ins[0]))
			out_shape = list(int(d) for d in G.tensor_shape(outs[0]))
			dim = _infer_chunk_dim(in_shape, out_shape, num_parts)
			if dim is not None:
				return [dim]
	elif "AllGatherPrim" in op:
		ins = G.node_inputs(n)
		outs = G.node_outputs(n)
		if ins and outs and num_parts > 0:
			shard_shape = list(int(d) for d in G.tensor_shape(ins[0]))
			full_shape = list(int(d) for d in G.tensor_shape(outs[0]))
			dim = _infer_gather_dim(shard_shape, full_shape, num_parts)
			if dim is not None:
				return [dim]
	# ── YOCO-MoE-A0.4B novel ops (added 2026-06-30) ──
	elif "FW_rotary_embedding" in op or "BW_rotary_embedding" in op:
		# params: [qh, kh] (#query heads, #key heads, supports GQA).
		# Inputs (FW): [csCache, positions, q, k] — q.shape = [..., qh, d]
		ins = G.node_inputs(n)
		if len(ins) >= 4:
			q_shape = list(int(d) for d in G.tensor_shape(ins[2]))
			k_shape = list(int(d) for d in G.tensor_shape(ins[3]))
			if len(q_shape) >= 2 and len(k_shape) >= 2:
				qh = q_shape[-2]
				kh = k_shape[-2]
				return [qh, kh]
	elif "FW_maybe_shuffle" in op or "BW_maybe_shuffle" in op \
		or "FW_maybe_unshuffle" in op or "BW_maybe_unshuffle" in op:
		# params: [cpSize, cpRank]. cpSize = num_parts (CP world size at this rank).
		cp_size = max(num_parts, 1)
		cp_rank = _node_rank(n) % cp_size
		return [cp_size, cp_rank]
	elif "FW_attn_sliding_window" in op or "BW_attn_sliding_window" in op:
		# params: [qh, kvh, d, vd, causal(1), windowLeft]
		# Inputs: q, k, v, cuQ, cuK; q.shape = [L, qh, d], v.shape = [L, kvh, vd]
		ins = G.node_inputs(n)
		kwargs = G.node_kwargs(n)
		if len(ins) >= 3:
			q_shape = list(int(d) for d in G.tensor_shape(ins[0]))
			k_shape = list(int(d) for d in G.tensor_shape(ins[1]))
			v_shape = list(int(d) for d in G.tensor_shape(ins[2]))
			if len(q_shape) >= 3 and len(k_shape) >= 3 and len(v_shape) >= 3:
				qh = q_shape[-2]
				kvh = k_shape[-2]
				d_ = q_shape[-1]
				vd = v_shape[-1]
				# sliding_window_attn_func: causal=True, window=(W, 0)
				causal_nat = 1 if kwargs.get("causal", True) else 0
				window = kwargs.get("window_size", (-1, 0))
				try:
					window_left = int(window[0]) if window[0] > 0 else 0
				except (IndexError, TypeError):
					window_left = 0
				return [qh, kvh, d_, vd, causal_nat, window_left]
	elif "FW_attn_zigzag" in op or "BW_attn_zigzag" in op:
		# params: same as above. zigzag uses windowLeft=0 (no sliding window).
		ins = G.node_inputs(n)
		kwargs = G.node_kwargs(n)
		if len(ins) >= 3:
			q_shape = list(int(d) for d in G.tensor_shape(ins[0]))
			k_shape = list(int(d) for d in G.tensor_shape(ins[1]))
			v_shape = list(int(d) for d in G.tensor_shape(ins[2]))
			if len(q_shape) >= 3 and len(k_shape) >= 3 and len(v_shape) >= 3:
				qh = q_shape[-2]
				kvh = k_shape[-2]
				d_ = q_shape[-1]
				vd = v_shape[-1]
				causal_nat = 1 if kwargs.get("causal", True) else 0
				# zigzag passes window=(-1,-1) → no window
				return [qh, kvh, d_, vd, causal_nat, 0]
	elif "FW_per_head_mix_precision_linear" in op or "BW_per_head_mix_precision_linear" in op:
		# Same params as FW_linear (no special encoding needed); leave empty
		# unless the Lean def requires shape hints.
		return None
	elif "FW_norm_linear" in op or "BW_norm_linear" in op:
		return None
	elif "FW_mix_precision_linear" in op or "BW_mix_precision_linear" in op:
		return None
	elif "FW_topk_routing" in op or "BW_topk_routing" in op:
		# params: [top_k, num_experts]
		# num_experts must match the logits' expert dimension (logits.shape[-1]).
		# Otherwise the Denote-side `fw_topk_routing`'s output shape [lDim, numExperts]
		# won't align with `topkScoresAt` reading `valAt scores (l * numExperts + e)`
		# from `softmax(logits) : [lDim, logits.shape[-1]]`, and the sharding-commute
		# axiom becomes inconsistent (values from wrong rows are read on LHS vs RHS).
		# Regression fix 2026-07-03 (Iroha): previously only [top_k] was emitted, so
		# `numExperts` defaulted to 1 via `params.getD 1 1`, making the axiom vacuous.
		kwargs = G.node_kwargs(n)
		top_k = int(kwargs.get("top_k", 1))
		num_experts = int(kwargs.get("num_experts", 1))
		# Derive num_experts from logits shape when not present in kwargs (safer fallback).
		if "num_experts" not in kwargs:
			ins = list(G.node_ins(n)) if hasattr(G, "node_ins") else []
			if ins:
				logits_tid = ins[0]
				logits_shape = G.tid_shape(logits_tid) if hasattr(G, "tid_shape") else None
				if logits_shape and len(logits_shape) >= 1:
					num_experts = int(logits_shape[-1])
		return [top_k, num_experts]
	elif "FW_all2all_moe_gmm" in op or "BW_all2all_moe_gmm" in op:
		# params: [num_experts, local_expert_start, local_expert_end, topk]
		kwargs = G.node_kwargs(n)
		num_experts = int(kwargs.get("num_experts", 1))
		local_start = int(kwargs.get("local_expert_start", 0))
		local_end = int(kwargs.get("local_expert_end", num_experts))
		topk = int(kwargs.get("topk", 1))
		return [num_experts, local_start, local_end, topk]
	elif "FW_inner_chunk_ce" in op or "BW_inner_chunk_ce" in op:
		# params: [chunk_size]
		kwargs = G.node_kwargs(n)
		chunk_size = int(kwargs.get("chunk_size", 1024))
		return [chunk_size]
	return None


def _embedding_offset_params_by_node(
	G: Any, nodes: Sequence[Any], num_parts: int = 0
) -> Dict[int, List[int]]:
	"""Infer offset params for row/vocab-sharded embedding nodes.

	There are two embedding patterns in GPT graphs:
	- row/vocab-sharded embedding: each rank has a different row shard and the
	  per-rank lookup outputs are summed with AllReducePrim. This needs
	  offset = rank * shard_rows.
	- hidden-sharded embedding: each rank has all rows but only a hidden slice and
	  the lookup outputs are gathered. This must not get an offset.
	"""
	if num_parts <= 1:
		return {}

	consumers: Dict[int, List[Any]] = {}
	for n in nodes:
		for t in G.node_inputs(n):
			consumers.setdefault(int(t.tid), []).append(n)

	def _fw_outputs_feed_allreduce(ns: Sequence[Any]) -> bool:
		out_tids = sorted(int(G.node_outputs(n)[0].tid) for n in ns if G.node_outputs(n))
		if len(out_tids) != num_parts:
			return False
		for c in consumers.get(out_tids[0], []):
			if "AllReducePrim" not in _safe_str_op(G.node_opname(c)):
				continue
			c_ins = sorted(int(t.tid) for t in G.node_inputs(c))
			if c_ins == out_tids:
				return True
		return False

	groups: Dict[Tuple[Any, ...], List[Any]] = {}
	for n in nodes:
		op = _safe_str_op(G.node_opname(n))
		ins = [int(t.tid) for t in G.node_inputs(n)]
		if "FW_embedding" in op and len(ins) == 2:
			key = ("FW_embedding", ins[0])
		elif "BW_embedding" in op and len(ins) == 3:
			key = ("BW_embedding", ins[0], ins[1])
		else:
			continue
		groups.setdefault(key, []).append(n)

	out: Dict[int, List[int]] = {}
	for key, ns in groups.items():
		if len(ns) != num_parts:
			continue
		ranks = sorted(_node_rank(n) for n in ns)
		if ranks != list(range(num_parts)):
			continue
		if key and key[0] == "FW_embedding" and not _fw_outputs_feed_allreduce(ns):
			continue
		weight_tids = [int(G.node_inputs(n)[-1].tid) for n in ns]
		if len(set(weight_tids)) != num_parts:
			continue
		try:
			weight_shapes = [
				[int(d) for d in G.tensor_shape(G.node_inputs(n)[-1])] for n in ns
			]
		except Exception:
			continue
		if not weight_shapes or any(sh != weight_shapes[0] for sh in weight_shapes):
			continue
		shard_rows = weight_shapes[0][0] if weight_shapes[0] else 0
		if shard_rows <= 0:
			continue
		for n in ns:
			out[id(n)] = [_node_rank(n) * shard_rows]
	return out


@dataclass(frozen=True)
class SelectedLineage:
	ts: int
	tps: List[Tuple[int, int]]  # (rank, tid)


def canonicalize_init_lineage_multiref(
	pm_graph: Any, lineage: SelectedLineage
) -> SelectedLineage:
	"""Follow only shape-preserving ``FW_multiref`` aliases to source leaves.

	Rank is preserved. Malformed or cyclic alias chains are rejected, and no
	other operation (including reshape, linear, and collectives) is traversed.
	"""
	producers: Dict[Tuple[int, int], List[Tuple[Any, Any]]] = {}
	for node in pm_graph.nodes():
		node_rank = int(_node_rank(node))
		for output in pm_graph.node_outputs(node):
			producers.setdefault((node_rank, int(output.tid)), []).append((node, output))

	canonical: List[Tuple[int, int]] = []
	for rank, original_tid in lineage.tps:
		rank = int(rank)
		tid = int(original_tid)
		seen: set[int] = set()
		while (rank, tid) in producers:
			if tid in seen:
				raise ValueError(f"FW_multiref alias cycle at PM rank {rank} tid {tid}")
			seen.add(tid)
			producer_entries = producers[(rank, tid)]
			if len(producer_entries) != 1:
				raise ValueError(
					f"multiple producers for init-lineage PM rank {rank} tid {tid}"
				)
			node, output = producer_entries[0]
			op = _safe_str_op(pm_graph.node_opname(node)).split(".")[-1]
			if op != "FW_multiref":
				break
			inputs = list(pm_graph.node_inputs(node))
			if len(inputs) != 1:
				raise ValueError(f"FW_multiref producing PM tid {tid} must have one input")
			if _node_rank(node) != int(rank):
				raise ValueError(f"FW_multiref rank mismatch for PM tid {tid}")
			source = inputs[0]
			if list(pm_graph.tensor_shape(source)) != list(pm_graph.tensor_shape(output)):
				raise ValueError(f"FW_multiref shape mismatch for PM tid {tid}")
			tid = int(source.tid)
		canonical.append((int(rank), tid))
	return SelectedLineage(ts=int(lineage.ts), tps=sorted(set(canonical)))


def deduplicate_intermediate_lineages(
	final_goals: Sequence[SelectedLineage],
	intermediate_lineages: Dict[int, SelectedLineage],
) -> Tuple[Dict[int, SelectedLineage], List[int]]:
	"""Apply the explicit policy that final goals win over intermediates."""
	final_tids = {int(goal.ts) for goal in final_goals}
	deduplicated = sorted(int(tid) for tid in intermediate_lineages if int(tid) in final_tids)
	kept = {
		int(tid): lineage
		for tid, lineage in intermediate_lineages.items()
		if int(tid) not in final_tids
	}
	return kept, deduplicated


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
	# Also drop FW_pyfunc / BW_pyfunc — these are nnscaler Python helper ops
	# (getitem on a sample dict, etc.) which are dataloader-side and should be
	# treated like DATALOADER: their outputs become initial assumptions, not
	# things to be proven.
	def _is_dataloader_like(opname: Any) -> bool:
		s = _safe_str_op(opname)
		return ("DATALOADER" in s) or ("pyfunc" in s.lower())
	nodes = [n for n in G.nodes() if not _is_dataloader_like(G.node_opname(n))]
	tid_to_node_idx: Dict[int, int] = {}
	for i, n in enumerate(nodes):
		for t in G.node_outputs(n):
			tid_to_node_idx[int(t.tid)] = i
	
	prod: Dict[int, Any] = {}
	for n in nodes:
		for t in G.node_outputs(n):
			prod[int(t.tid)] = n

	closure_cache: Dict[int, set[int]] = {}

	def _closure(tid: int) -> set[int]:
		tid = int(tid)
		if tid in closure_cache:
			return closure_cache[tid]
		out = {tid}
		node = prod.get(tid)
		if node is not None:
			for t_in in G.node_inputs(node):
				out |= _closure(int(t_in.tid))
		closure_cache[tid] = out
		return out

	# For each goal, compute its backward closure and position
	goal_closures: Dict[int, set[int]] = {}
	goal_positions: Dict[int, int] = {}
	for g in goals:
		closure = _closure(int(g.ts))
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
		if ("AllReducePrim" not in op) and ("AllGatherPrim" not in op) and ("CROSS_DP_WRED" not in op):
			continue
		ins = sorted(int(t.tid) for t in pm_graph.node_inputs(n))
		outs = [int(t.tid) for t in pm_graph.node_outputs(n)]
		if ins == lineage_tids and len(outs) == 1:
			return SelectedLineage(ts=lineage.ts, tps=[(0, outs[0])])
	return lineage


def make_collective_lineage_normalizer(pm_graph: Any):
	"""Build an indexed lineage normalizer for repeated lookups on the same PM graph."""
	collective_outputs_by_inputs: Dict[Tuple[int, ...], int] = {}
	for n in pm_graph.nodes():
		op = _safe_str_op(pm_graph.node_opname(n))
		if ("AllReducePrim" not in op) and ("AllGatherPrim" not in op) and ("CROSS_DP_WRED" not in op):
			continue
		ins = tuple(sorted(int(t.tid) for t in pm_graph.node_inputs(n)))
		outs = [int(t.tid) for t in pm_graph.node_outputs(n)]
		if len(outs) == 1:
			collective_outputs_by_inputs.setdefault(ins, outs[0])

	def normalize(lineage: SelectedLineage) -> SelectedLineage:
		if not lineage.tps:
			return lineage
		lineage_tids = tuple(sorted(int(t) for (_r, t) in lineage.tps))
		out_tid = collective_outputs_by_inputs.get(lineage_tids)
		if out_tid is None:
			return lineage
		return SelectedLineage(ts=lineage.ts, tps=[(0, out_tid)])

	return normalize


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


def _all_tensor_shapes_from_graph(G: Any) -> Dict[int, List[int]]:
	"""Get shapes for ALL tensors in the graph (not just initial ones)."""
	shapes: Dict[int, List[int]] = {}
	for t in G.tensors():
		tid = getattr(t, "tid", None)
		if tid is None:
			continue
		try:
			shp = [int(x) for x in list(G.tensor_shape(t))]
			shapes[int(tid)] = shp
		except Exception:
			pass
	return shapes


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
	lines: List[str], *, name: str, G: Any, kept_nodes: Sequence[Any], prefer_shapes: Optional[Dict[int, List[int]]] = None,
	emit_all_shapes: bool = False
) -> None:
	"""Emit initial tensor shapes for shape checking.
	
	If emit_all_shapes is True, emit shapes for ALL tensors (not just initial ones).
	This is needed for operations like view/reshape where output shape cannot be
	inferred from input shape alone.
	"""
	if emit_all_shapes:
		# Get all tensor shapes from the graph
		all_shapes = _all_tensor_shapes_from_graph(G)
		pairs: List[Tuple[int, List[int]]] = sorted(all_shapes.items())
	else:
		init_tids = _init_tids_from_kept_nodes(G, kept_nodes)
		pairs = []
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


def _emit_cut_to_full(
	*,
	gid: str,
	sl: "GoalSlice",
	dep: Optional["GoalDependency"],
	sm_graph: Any,
	pm_graph: Any,
	module_name: str,
	goals_module_prefix: str,  # e.g. "denote.yoco_goals" or "denote.gpt_ly4_regen"
	goal_id_fn: Any,
	emit_nodup_inline: bool = True,  # emit sm/pm_nodes_nodup inline; set False if a shared GraphFacts.lean already has them
) -> List[str]:
	"""Emit Goal_{gid}_CutToFull.lean using denoteGraph_slice_agrees.

	Design doc: iroha-tasks/trainverify-bw/yoco-patterns/2026-07-02_cut_to_full_emitter_design.md
	POC file : trainverify/denote/yoco_goals/Goal_5_CutToFull_POC.lean
	"""
	sm_name = f"sm_goal_{gid}"
	pm_name = f"pm_goal_{gid}"
	goal_name = f"goal_{gid}"
	goal_ts = int(sl.goal.ts)
	# Collect the tid witnesses we'll need for graphWrites proofs.
	# sm-side: the node in sl.sm_nodes that outputs goal_ts.
	sm_writer_node = None
	for n in sl.sm_nodes:
		outs = [int(t.tid) for t in sm_graph.node_outputs(n)]
		if goal_ts in outs:
			sm_writer_node = n
			break
	# pm-side: for each tp in goal.tps, the node in sl.pm_nodes that outputs tp.tid.
	pm_writer_nodes: List[Tuple[int, Any]] = []
	for tp in sl.goal.tps:
		# tp is (rank, tid) tuple per LineageGoal.tps typing (line 603).
		tp_tid = int(tp[1]) if isinstance(tp, tuple) else int(tp.tid)
		for n in sl.pm_nodes:
			outs = [int(t.tid) for t in pm_graph.node_outputs(n)]
			if tp_tid in outs:
				pm_writer_nodes.append((tp_tid, n))
				break

	def _node_literal(n: Any, G: Any, num_ranks: int) -> str:
		"""Reconstruct a NodeDecl literal string matching how the emitter writes graph nodes."""
		op = escape_lean_string(_safe_str_op(G.node_opname(n)))
		ins = [int(t.tid) for t in G.node_inputs(n)]
		outs = [int(t.tid) for t in G.node_outputs(n)]
		rank = _node_rank(n)
		embedding_params = _embedding_offset_params_by_node(G, [n], num_parts=num_ranks)
		node_params = embedding_params.get(id(n)) or _get_node_params(G, n, num_parts=num_ranks)
		params_str = f", params := {lean_list_nat(node_params)}" if node_params else ""
		return (
			f"{{ rank := {rank}, op := \"{op}\", "
			f"ins := {lean_list_nat(ins)}, outs := {lean_list_nat(outs)}{params_str} }}"
		)

	sm_num_ranks = 1
	pm_num_ranks = max((_node_rank(n) for n in sl.pm_nodes), default=0) + 1

	# graphTids sets: union of ins ∪ outs across all slice nodes.
	def _tid_set(nodes: Sequence[Any], G: Any) -> List[int]:
		s: set = set()
		for n in nodes:
			s.update(int(t.tid) for t in G.node_inputs(n))
			s.update(int(t.tid) for t in G.node_outputs(n))
		return sorted(s)

	sm_tids = _tid_set(sl.sm_nodes, sm_graph)
	pm_tids = _tid_set(sl.pm_nodes, pm_graph)

	# ---- Emit ----
	lines: List[str] = []
	lines.append("/- Auto-generated by Verdict/graph_to_lean.py --split-goals")
	lines.append(f"    Goal: {gid} (tensor id: {goal_ts}) cut_to_full bridge.")
	lines.append("    Uses denoteGraph_slice_agrees (op-generic) — zero op-specific handwriting.")
	lines.append("-/")
	lines.append(f"import {goals_module_prefix}.Goal_{gid}")
	lines.append("import denote.GraphSlicing")
	# For non-base goals, import the intermediate-goal proofs of every prereq.
	if dep and dep.prereq_intermediate_goals:
		prereq_gids: List[str] = []
		for (ts, _) in dep.prereq_intermediate_goals:
			prereq_gid = goal_id_fn(int(ts))
			prereq_gids.append(prereq_gid)
			lines.append(f"import {goals_module_prefix}.Goal_{prereq_gid}_CutToFull")
	else:
		prereq_gids = []
	lines.append("")
	lines.append("set_option linter.style.longLine false")
	lines.append("set_option maxRecDepth 100000")
	lines.append("set_option maxHeartbeats 1600000")
	lines.append("")
	lines.append("namespace TrainVerify.Denote.GeneratedGoals")
	lines.append("open TrainVerify.Denote TrainVerify.Denote.Generated")
	lines.append("")

	# --- Global-graph facts (inline if not shared) ---
	if emit_nodup_inline:
		lines.append("-- Inline nodup facts (per-file; a future GraphFacts.lean can dedupe these).")
		lines.append(f"private theorem local_sm_nodes_nodup_{gid} : sm.nodes.Nodup := by native_decide")
		lines.append(f"private theorem local_pm_nodes_nodup_{gid} : pm.nodes.Nodup := by native_decide")
		nodup_sm = f"local_sm_nodes_nodup_{gid}"
		nodup_pm = f"local_pm_nodes_nodup_{gid}"
	else:
		nodup_sm = "sm_nodes_nodup"
		nodup_pm = "pm_nodes_nodup"
	lines.append("")

	# --- Sublist + numRanks facts ---
	lines.append(f"theorem {sm_name}_sublist : List.Sublist {sm_name}.nodes sm.nodes := by decide")
	lines.append(f"theorem {pm_name}_sublist : List.Sublist {pm_name}.nodes pm.nodes := by decide")
	lines.append(f"theorem {sm_name}_numRanks_eq : sm.numRanks = {sm_name}.numRanks := by native_decide")
	lines.append(f"theorem {pm_name}_numRanks_eq : pm.numRanks = {pm_name}.numRanks := by native_decide")
	lines.append("")

	# --- NoInterference facts ---
	def _emit_no_interference(side: str, name: str, tids: List[int], slice_nodes: Sequence[Any], G: Any) -> None:
		lines.append(f"def {name}_tid_set : List Tid := {lean_list_nat(tids)}")
		lines.append("")
		# graphTids ⊆ tid_set proof.
		lines.append(f"theorem graphTids_{name}_subset :")
		lines.append(f"    ∀ tid, graphTids {name} tid → tid ∈ {name}_tid_set := by")
		lines.append("  intro tid htid")
		lines.append("  rcases htid with ⟨n', hmem, hins⟩ | ⟨n', hmem, houts⟩")
		# For each side of rcases, unfold the singleton or list of nodes.
		n_slice = len(slice_nodes)
		lines.append(f"  · simp only [{name}, List.mem_cons, List.not_mem_nil, or_false] at hmem")
		if n_slice == 1:
			lines.append("    subst hmem")
			lines.append("    simp only [List.mem_cons, List.not_mem_nil, or_false] at hins")
			# tid ∈ node.ins, need to prove tid ∈ tid_set
			ins_count = len([int(t.tid) for t in G.node_inputs(slice_nodes[0])])
			if ins_count == 0:
				lines.append("    exact absurd hins (by simp)")
			elif ins_count == 1:
				lines.append("    subst hins")
				lines.append(f"    simp [{name}_tid_set]")
			else:
				pats = " | ".join(["rfl"] * ins_count)
				lines.append(f"    rcases hins with {pats}")
				lines.append(f"    all_goals simp [{name}_tid_set]")
		else:
			pats = " | ".join(["rfl"] * n_slice)
			lines.append(f"    rcases hmem with {pats}")
			lines.append("    all_goals")
			lines.append("      simp only [List.mem_cons, List.not_mem_nil, or_false] at hins")
			# For each node, ins_count varies; use decide as catch-all.
			# Try tauto if lists differ.
			lines.append(f"      simp [{name}_tid_set] at *")
			lines.append("      tauto")
		lines.append(f"  · simp only [{name}, List.mem_cons, List.not_mem_nil, or_false] at hmem")
		if n_slice == 1:
			lines.append("    subst hmem")
			lines.append("    simp only [List.mem_cons, List.not_mem_nil, or_false] at houts")
			outs_count = len([int(t.tid) for t in G.node_outputs(slice_nodes[0])])
			if outs_count == 0:
				lines.append("    exact absurd houts (by simp)")
			elif outs_count == 1:
				lines.append("    subst houts")
				lines.append(f"    simp [{name}_tid_set]")
			else:
				pats = " | ".join(["rfl"] * outs_count)
				lines.append(f"    rcases houts with {pats}")
				lines.append(f"    all_goals simp [{name}_tid_set]")
		else:
			pats = " | ".join(["rfl"] * n_slice)
			lines.append(f"    rcases hmem with {pats}")
			lines.append("    all_goals")
			lines.append("      simp only [List.mem_cons, List.not_mem_nil, or_false] at houts")
			lines.append(f"      simp [{name}_tid_set] at *")
			lines.append("      tauto")
		lines.append("")
		# no_interference via decide + subset.
		lines.append(f"theorem {name}_no_interference :")
		lines.append(f"    ∀ n ∈ {side}.nodes, n ∉ {name}.nodes →")
		lines.append(f"      ∀ tid, graphTids {name} tid → tid ∉ n.outs := by")
		lines.append(f"  have hkey : ∀ n ∈ {side}.nodes, n ∉ {name}.nodes →")
		lines.append(f"      ∀ tid, tid ∈ {name}_tid_set → tid ∉ n.outs := by")
		lines.append(f"    unfold {name}_tid_set")
		lines.append("    native_decide")
		lines.append("  intro n hn hn_notlocal tid htid")
		lines.append(f"  exact hkey n hn hn_notlocal tid (graphTids_{name}_subset tid htid)")
		lines.append("")

	_emit_no_interference("sm", sm_name, sm_tids, sl.sm_nodes, sm_graph)
	_emit_no_interference("pm", pm_name, pm_tids, sl.pm_nodes, pm_graph)

	# --- Main theorem ---
	if prereq_gids:
		# NON-BASE case (has prereqs from earlier goals). The auto-generated
		# cut_to_full requires a `denoteGraph_slice_self_agrees` lemma that
		# isn't yet proven (needs a fixed-point induction on g.nodes not
		# covered by denoteGraph_slice_agrees). Skip emitting the theorem;
		# users must hand-write it via sm_frame_*_self / pm_frame_*_self
		# helpers (see denote/gpt_ly4_regen/Goal*Bridge.lean examples).
		lines.append("/-")
		lines.append(
			f"NON-BASE goal (has {len(prereq_gids)} prereqs). Auto-generation of"
		)
		lines.append(
			"`goal_{gid}_cut_to_full` is not yet supported for non-base goals;"
		)
		lines.append(
			"it requires the `denoteGraph_slice_self_agrees` lemma which needs"
		)
		lines.append(
			"an unproven fixed-point-on-writes property of `denoteGraph g`."
		)
		lines.append("")
		lines.append(
			"See `denote/GraphSlicing.lean` (Non-base cut_to_full note) for the"
		)
		lines.append("open sub-lemma statement.")
		lines.append("")
		lines.append(
			"To finish this goal manually, write per-goal `sm_frame_*_self` /"
		)
		lines.append(
			"`pm_frame_*_self` helpers (see gpt_ly4_regen Goal*Bridge.lean for"
		)
		lines.append("examples), then assemble cut_to_full using them + the "
		            "sublist/nodup/no-interference facts already emitted above.")
		lines.append("-/")
		lines.append("")
		lines.append("end TrainVerify.Denote.GeneratedGoals")
		return lines
	# BASE case: emit the full auto-generated cut_to_full theorem.
	lines.append(f"theorem goal_{gid}_cut_to_full (h : goal_{gid}_stmt_cut) : goal_{gid}_stmt := by")
	lines.append("  intro initSM initPM hSM hPM hInit")
	# StoreShapesHold for local envs.
	def _emit_store_shapes_hold(side: str, name: str, init_shapes: List[Tuple[int, List[int]]]) -> None:
		lines.append(f"  have h{side}cut : StoreShapesHold init{side.upper()} {name}InitEnv := by")
		lines.append("    intro tid sh hsh")
		lines.append(f"    rw [{name}InitEnv] at hsh")
		lines.append("    have hmem := mem_of_shapeEnvOfList_eq_some hsh")
		lines.append(
			f"    simp only [{name}InitShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem"
		)
		n = len(init_shapes)
		if n == 0:
			lines.append("    exact absurd hmem (by simp)")
			return
		pats = " | ".join(["⟨rfl, rfl⟩"] * n)
		lines.append(f"    rcases hmem with {pats}")
		for (tid, sh) in init_shapes:
			lines.append(f"    · exact h{side.upper()} {tid} {lean_list_nat(sh)} (by native_decide)")

	# Derive init_shapes from _emit_init_env logic (init tids kept from sm_slice / pm_slice).
	sm_init_shapes: List[Tuple[int, List[int]]] = []
	for tid in _init_tids_from_kept_nodes(sm_graph, sl.sm_nodes):
		shp, _ = _shape_init_from_graph_by_tid(sm_graph, tid)
		if shp is not None:
			sm_init_shapes.append((int(tid), [int(x) for x in shp]))
	pm_init_shapes: List[Tuple[int, List[int]]] = []
	_sm_prefer_local = _build_sm_prefer(sm_graph, sl.sm_nodes)
	for tid in _init_tids_from_kept_nodes(pm_graph, sl.pm_nodes):
		if int(tid) in _sm_prefer_local:
			shp = _sm_prefer_local[int(tid)]
		else:
			shp_opt, _ = _shape_init_from_graph_by_tid(pm_graph, tid)
			if shp_opt is None:
				continue
			shp = [int(x) for x in shp_opt]
		pm_init_shapes.append((int(tid), shp))

	_emit_store_shapes_hold("SM", sm_name, sm_init_shapes)
	_emit_store_shapes_hold("PM", pm_name, pm_init_shapes)

	# InitGoalsHold for cut initGoals.
	lines.append(
		f"  have hInitCut : InitGoalsHold {pm_name}.numRanks goal_{gid}_cut_initGoals initSM initPM := by"
	)
	lines.append(f"    simp only [goal_{gid}_cut_initGoals]")
	lines.append(f"    have hnr : {pm_name}.numRanks = pm.numRanks := {pm_name}_numRanks_eq.symm")
	lines.append("    rw [hnr]")
	if prereq_gids:
		# initGoals ++ goal_gid_prereqs — this branch is DEAD (we early-return
		# above for non-base goals). Kept as a placeholder for future re-enable
		# once denoteGraph_slice_self_agrees is proven.
		lines.append("    apply InitGoalsHold_append")
		lines.append("    · exact hInit")
		lines.append(f"    · simp only [goal_{gid}_prereqs, InitGoalsHold]")
		lines.append("      intro g hg")
		lines.append(
			"      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg"
		)
		n_prereq = len(prereq_gids)
		if n_prereq == 1:
			pgid = prereq_gids[0]
			lines.append("      subst hg")
			lines.append(f"      exact goal_{pgid}_intermediate initSM initPM hSM hPM hInit")
		else:
			pats = " | ".join(["rfl"] * n_prereq)
			lines.append(f"      rcases hg with {pats}")
			for pgid in prereq_gids:
				lines.append(f"      · exact goal_{pgid}_intermediate initSM initPM hSM hPM hInit")
	else:
		lines.append("    exact hInit")
	# Apply cut hypothesis.
	lines.append("  have hcut := h initSM initPM hSMcut hPMcut hInitCut")
	# Slice-agrees for sm side (single ts).
	lines.append(
		f"  have h_agree_sm : StoreAgreesOn initSM initSM (graphTids {sm_name}) := fun _ _ => rfl"
	)
	lines.append(
		f"  have h_agree_pm : StoreAgreesOn initPM initPM (graphTids {pm_name}) := fun _ _ => rfl"
	)
	# sm slice at ts.
	if sm_writer_node is not None:
		sm_writer_lit = _node_literal(sm_writer_node, sm_graph, sm_num_ranks)
		lines.append(
			f"  have h_sm_slice : denoteGraph {sm_name} initSM {goal_ts} = denoteGraph sm initSM {goal_ts} := by"
		)
		lines.append(
			f"    apply denoteGraph_slice_agrees sm {sm_name} {sm_name}_numRanks_eq {sm_name}_sublist"
		)
		lines.append(
			f"      {nodup_sm} initSM initSM h_agree_sm {sm_name}_no_interference {goal_ts}"
		)
		lines.append(f"    refine ⟨{sm_writer_lit}, ?_, ?_⟩")
		lines.append(f"    · simp [{sm_name}]")
		lines.append("    · simp")
	# pm slice(s) at each tp.
	slice_pm_lemma_names: List[str] = []
	for (tp_tid, pm_writer_node) in pm_writer_nodes:
		pm_writer_lit = _node_literal(pm_writer_node, pm_graph, pm_num_ranks)
		slice_name = f"h_pm_slice_{tp_tid}"
		slice_pm_lemma_names.append(slice_name)
		lines.append(
			f"  have {slice_name} : denoteGraph {pm_name} initPM {tp_tid} = denoteGraph pm initPM {tp_tid} := by"
		)
		lines.append(
			f"    apply denoteGraph_slice_agrees pm {pm_name} {pm_name}_numRanks_eq {pm_name}_sublist"
		)
		lines.append(
			f"      {nodup_pm} initPM initPM h_agree_pm {pm_name}_no_interference {tp_tid}"
		)
		lines.append(f"    refine ⟨{pm_writer_lit}, ?_, ?_⟩")
		lines.append(f"    · simp [{pm_name}]")
		lines.append("    · simp")
	# Rewrite hcut → goal.
	lines.append(f"  simp only [{goal_name}, CoarseLineageHoldsWithInit] at hcut")
	lines.append(f"  simp only [List.map, {goal_name}] at hcut")
	rw_list = ["h_sm_slice"] + slice_pm_lemma_names
	lines.append(f"  rw [{', '.join(rw_list)}] at hcut")
	lines.append("  simp only [List.map]")
	lines.append("  exact hcut")
	lines.append("")

	# Emit the intermediate helper (for downstream goals that reference this
	# goal via its prereq_intermediate_goals list). Requires the caller to
	# provide `prove_goal_{gid}_cut : goal_{gid}_stmt_cut` — a separate proof
	# artefact typically produced by the pattern-hand-prove workflow. If the
	# pattern isn't yet proven, this file compiles fine but downstream imports
	# will fail with "unknown identifier prove_goal_{gid}_cut".
	lines.append("-- If prove_goal_{gid}_cut is available, uncomment `goal_{gid}_intermediate`:")
	lines.append("/-")
	lines.append(
		f"theorem goal_{gid}_intermediate (initSM initPM : Store)"
	)
	lines.append(
		"    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)"
	)
	lines.append(
		"    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :"
	)
	lines.append(
		f"    InitGoalHolds pm.numRanks goal_{gid} (denoteGraph sm initSM) (denoteGraph pm initPM) := by"
	)
	lines.append(f"  have hfull : goal_{gid}_stmt := goal_{gid}_cut_to_full prove_goal_{gid}_cut")
	lines.append("  have := hfull initSM initPM hSM hPM hInit")
	lines.append("  unfold InitGoalHolds")
	lines.append(f"  simp only [{goal_name}]")
	lines.append("  exact this")
	lines.append("-/")
	lines.append("")
	lines.append("end TrainVerify.Denote.GeneratedGoals")
	return lines


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
	use_tid_goal_ids: bool = False,
	emit_segment_patterns: bool = False,
	segment_max_goals: int = 8,
	segment_min_repeats: int = 2,
	segment_max_period: int = 80,
	manifest_name: Optional[str] = None,
) -> None:
	# Build mapping from goal ts to sequential id (1-based) by default
	goal_ts_to_seq_id: Dict[int, int] = {}
	if not use_tid_goal_ids:
		for i, g in enumerate(goals, start=1):
			goal_ts_to_seq_id[int(g.ts)] = i
	
	def _goal_id(ts: int) -> str:
		"""Return goal identifier: sequential id by default, else tensor id."""
		if (not use_tid_goal_ids) and ts in goal_ts_to_seq_id:
			return str(goal_ts_to_seq_id[ts])
		return str(ts)
	
	lines: List[str] = []
	# NOTE: In Lean, `import` must come before any commands. A module doc comment
	# `/-! ... -/` counts as a command, so we use a plain block comment here.
	lines.append(f"/- Auto-generated by Verdict/graph_to_lean.py")
	lines.append(f"    Module: {module_name}")
	if manifest_name:
		lines.append(f"    Provenance: {manifest_name}")
	lines.append(f"-/")
	lines.append("import denote.Denote")
	lines.append("")
	lines.append("set_option linter.style.longLine false")
	lines.append("set_option linter.style.nativeDecide false")
	lines.append("set_option maxRecDepth 100000")
	lines.append("")
	lines.append("open TrainVerify.Denote")
	lines.append("")
	lines.append("namespace TrainVerify.Denote.Generated")
	lines.append("")

	def _emit_graph(name: str, nodes: List[Any], G: Any, num_parts: int = 1) -> None:
		"""Emit a GraphDecl definition.
		
		Special handling for CROSS_DP_WRED: since this is an inplace reduction where
		all ranks share the same inputs and each outputs one of those inputs,
		we emit a single node with all inputs and all outputs.
		"""
		embedding_params = _embedding_offset_params_by_node(G, nodes, num_parts=num_parts)
		# Build mapping for CROSS_DP_WRED: group by sorted inputs
		wred_groups: Dict[tuple[int, ...], List[Any]] = {}
		for n in nodes:
			op = _safe_str_op(G.node_opname(n))
			if "CROSS_DP_WRED" not in op:
				continue
			ins = tuple(sorted(int(t.tid) for t in G.node_inputs(n)))
			wred_groups.setdefault(ins, []).append(n)
		
		# Collect all outputs for each WRED group
		wred_all_outs: Dict[tuple[int, ...], List[int]] = {}
		for ins, ns in wred_groups.items():
			all_outs = []
			for n in ns:
				all_outs.extend(int(t.tid) for t in G.node_outputs(n))
			wred_all_outs[ins] = sorted(set(all_outs))
		
		lines.append(f"def {name} : GraphDecl := by")
		# numRanks: SM is 1, PM is inferred from max rank + 1.
		if name == "sm" or name.startswith("sm_"):
			num_ranks = 1
		else:
			num_ranks = max((_node_rank(n) for n in nodes), default=0) + 1
		lines.append(f"  refine {{ numRanks := {num_ranks}, nodes := ?_ }}")
		lines.append("  exact [")
		
		seen_wred: set[tuple[int, ...]] = set()
		for n in nodes:
			op_str = _safe_str_op(G.node_opname(n))
			op = escape_lean_string(op_str)
			ins = [int(t.tid) for t in G.node_inputs(n)]
			outs = [int(t.tid) for t in G.node_outputs(n)]
			rank = _node_rank(n)
			
			# Special handling for CROSS_DP_WRED
			if "CROSS_DP_WRED" in op_str:
				ins_key = tuple(sorted(ins))
				if ins_key in seen_wred:
					continue  # Skip duplicate WRED nodes
				seen_wred.add(ins_key)
				# Use all outputs from all ranks
				outs = wred_all_outs.get(ins_key, outs)

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

			node_params = embedding_params.get(id(n)) or _get_node_params(G, n, num_parts=num_parts)
			params_str = f", params := {lean_list_nat(node_params)}" if node_params else ""
			lines.append(
				f"    {{ rank := {rank}, op := \"{op}\", ins := {_lean_list_nat_expr(ins)}, outs := {_lean_list_nat_expr(outs)}{params_str} }},"
			)
		lines.append("  ]")
		lines.append("")

	pm_num_ranks = max((_node_rank(n) for n in pm_nodes), default=0) + 1

	_emit_graph("sm", sm_nodes, sm_graph, num_parts=1)
	_emit_graph("pm", pm_nodes, pm_graph, num_parts=pm_num_ranks)

	# When a boundary tid exists in both SM and PM, it is usually a shared input (e.g. activations,
	# labels, loss-grad). Prefer the SM shape for those tids to avoid backend-specific ambiguities
	# in the PM tensor registry.
	# This is crucial for the decidable `graphShapesCheck` gate.
	_sm_prefer: Dict[int, List[int]] = _build_sm_prefer(sm_graph, sm_nodes)

	# emit_all_shapes=True: Output shapes for ALL tensors, not just initial ones.
	# This is needed because operations like view/reshape have output shapes that
	# cannot be inferred from input shapes alone.
	_emit_init_env(lines, name="sm", G=sm_graph, kept_nodes=sm_nodes, emit_all_shapes=True)
	_emit_init_env(lines, name="pm", G=pm_graph, kept_nodes=pm_nodes, prefer_shapes=_sm_prefer, emit_all_shapes=True)

	def _infer_gather_dim(ts_shape: List[int], tp_shape: List[int], num_pieces: int) -> int:
		"""Infer which dimension was split by comparing SM and PM shard shapes.
		
		Returns the dimension index where ts_shape[dim] == tp_shape[dim] * num_pieces
		and all other dimensions match. Defaults to 0 if no match is found.
		"""
		if len(ts_shape) != len(tp_shape):
			return 0
		for dim in range(len(ts_shape)):
			if tp_shape[dim] * num_pieces == ts_shape[dim]:
				# Check all other dimensions match
				if all(ts_shape[d] == tp_shape[d] for d in range(len(ts_shape)) if d != dim):
					return dim
		return 0

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
		
		# Infer gather dimension and validate shapes
		num_pieces = len(g.tps)
		gather_dim = 0
		# Detect replicated tensor: all shards have shape == ts_shape (per-rank full copy).
		# This arises from FW_multiref of replicated tensors — nnscaler semantics is "pick one",
		# not allGather. Emit `replicated := true` so Denote's reconstructForGoal takes the head.
		replicated = (
			num_pieces > 1
			and ts_shape
			and all(tp_shape == ts_shape for tp_shape in tp_shapes if tp_shape)
		)
		if num_pieces > 1 and ts_shape and ts_shape != [1] and tp_shapes and tp_shapes[0] and not replicated:
			actual_tp_shape = tp_shapes[0]
			gather_dim = _infer_gather_dim(ts_shape, actual_tp_shape, num_pieces)
			# Validate: check that the inferred dimension is consistent
			if len(ts_shape) == len(actual_tp_shape):
				expected_tp = list(ts_shape)
				if gather_dim < len(expected_tp) and expected_tp[gather_dim] % num_pieces == 0:
					expected_tp[gather_dim] = expected_tp[gather_dim] // num_pieces
				if actual_tp_shape != expected_tp:
					print(f"WARNING: Shape mismatch for ts={g.ts}")
					print(f"  ts_shape: {ts_shape}")
					print(f"  num_pieces: {num_pieces}")
					print(f"  inferred gatherDim: {gather_dim}")
					print(f"  expected tp_shape: {expected_tp}")
					print(f"  actual tp_shape in PM graph: {actual_tp_shape}")
					print(f"  tp_tids: {[tid for (_r, tid) in g.tps]}")

		# NOTE: Keep `tps` and `tpShapes` as concrete lists.
		# Reason: `reconstruct` performs `match` on the tensor list; if `tps` is symbolic
		# (e.g. `List.range.map`), Lean cannot reduce the match and simp becomes unusable.
		tps_expr = "[" + ", ".join(f"{{ rank := {r}, tid := {t} }}" for r, t in g.tps) + "]"
		tp_shapes_expr = "[" + ", ".join("[" + ", ".join(str(int(x)) for x in shp) + "]" for shp in tp_shapes) + "]"

		# Only emit gatherDim when it's non-default (non-zero) to keep output clean
		gather_dim_expr = f", gatherDim := {gather_dim}" if gather_dim != 0 else ""
		# Emit replicated only when true (default is false, keeps default cases clean)
		replicated_expr = ", replicated := true" if replicated else ""

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
			+ gather_dim_expr
			+ replicated_expr
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
		gid = _goal_id(g.ts)
		def_name = f"goal_{gid}"
		goal_def_names.append(def_name)
		_emit_goal_def(def_name, g, for_init=False)

	goal_chunk_size = 8
	goal_chunk_names: List[str] = []
	for chunk_idx, start in enumerate(range(0, len(goal_def_names), goal_chunk_size), start=1):
		chunk_names = goal_def_names[start : start + goal_chunk_size]
		chunk_def = f"goalChunk_{chunk_idx}"
		goal_chunk_names.append(chunk_def)
		lines.append(f"def {chunk_def} : List LineageGoal := [" + ", ".join(chunk_names) + "]")
	if goal_chunk_names:
		goals_expr = goal_chunk_names[-1]
		for chunk_def in reversed(goal_chunk_names[:-1]):
			goals_expr = f"{chunk_def} ++ ({goals_expr})"
		lines.append("def goals : List LineageGoal := " + goals_expr)
	else:
		lines.append("def goals : List LineageGoal := []")
	lines.append("")

	# Proposition aliases (no proofs): manual proofs should live in a separate, non-generated file.
	# Also emit a *decidable* shape-level check for smaller graphs. Large GPT graphs can make
	# native_decide and IR compilation dominate build time; the concrete shape environments are
	# still emitted above, but the generated module skips the automatic check.
	if len(sm_nodes) + len(pm_nodes) <= 1500:
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
	else:
		lines.append("-- Auto shape/dimension checks skipped for this large generated graph.")
		lines.append("")

	# Small unfold lemma for SM denotation (SM graphs are typically tiny and single-rank).
	# This avoids repeatedly rewriting foldl by hand in proofs.
	if len(sm_nodes) <= 24:
		lines.append("theorem sm_denoteGraph_unfold (init : Store) :")
		lines.append("    denoteGraph sm init =")
		# Build a nested applyNode chain with the concrete node decls.
		def _node_lit(n: Any, G: Any, num_parts: int = 1) -> str:
			op = escape_lean_string(_safe_str_op(G.node_opname(n)))
			ins = [int(t.tid) for t in G.node_inputs(n)]
			outs = [int(t.tid) for t in G.node_outputs(n)]
			rank = _node_rank(n)
			node_params = _get_node_params(G, n, num_parts=num_parts)
			params_str = f", params := {lean_list_nat(node_params)}" if node_params else ""
			return (
				"{ "
				+ f"rank := {rank}, op := \"{op}\", ins := {lean_list_nat(ins)}, outs := {lean_list_nat(outs)}{params_str}"
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
	
	# Build set of goal tids for dedup with intermediates
	goal_tid_set: set[int] = {int(g.ts) for g in goals}

	# Helper: resolve a prereq tid to its Lean definition name.
	# If the tid is already a goal, reference goal_X; otherwise intermediateGoal_tid.
	def _prereq_def_name(inter_ts: int) -> str:
		if inter_ts in goal_tid_set:
			return f"goal_{_goal_id(inter_ts)}"
		return f"intermediateGoal_{inter_ts}"

	def _prereq_list_expr(dep: GoalDependency) -> str:
		prereq_names = [_prereq_def_name(int(inter_ts)) for (inter_ts, _) in dep.prereq_intermediate_goals]
		return "[" + ", ".join(prereq_names) + "]"

	# Emit intermediate lineage goal definitions ONLY for tids not already goals
	intermediate_def_names: List[str] = []
	if intermediate_lineages:
		non_goal_intermediates = {ts: lin for ts, lin in intermediate_lineages.items()
		                         if int(ts) not in goal_tid_set}
		if non_goal_intermediates:
			lines.append("-- Intermediate tensor lineage goals (not already regular goals)")
			for inter_ts, inter_lin in sorted(non_goal_intermediates.items()):
				def_name = f"intermediateGoal_{inter_ts}"
				intermediate_def_names.append(def_name)
				_emit_goal_def(def_name, inter_lin, for_init=False)
			lines.append("")
			lines.append("-- Proof obligations (intermediate goals)")
			for def_name in intermediate_def_names:
				lines.append(f"def {def_name}_stmt : Prop :=")
				lines.append(f"  CoarseLineageHoldsWithInit sm pm {def_name} smInitEnv pmInitEnv initGoals")
				lines.append("")

	for i, g in enumerate(goals):
		goal_ts = int(g.ts)
		gid = _goal_id(goal_ts)
		def_name = f"goal_{gid}"
		dep = deps_by_ts.get(goal_ts)
		
		if dep and dep.prereq_intermediate_goals:
			if goal_slices is None:
				lines.append(f"-- goal_{gid} (tid={goal_ts}) depends on: {[ts for (ts, _) in dep.prereq_intermediate_goals]}")
				lines.append(f"def {def_name}_prereqs : List LineageGoal := {_prereq_list_expr(dep)}")
				lines.append("")
			
			lines.append(f"def {def_name}_stmt : Prop :=")
			lines.append(f"  CoarseLineageHoldsWithInit sm pm {def_name} smInitEnv pmInitEnv initGoals")
			lines.append("")
		else:
			lines.append(f"def {def_name}_stmt : Prop :=")
			lines.append(f"  CoarseLineageHoldsWithInit sm pm {def_name} smInitEnv pmInitEnv initGoals")
			lines.append("")

		if goal_slices is None:
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
	
	# Emit dependency structure documentation
	if goal_deps:
		lines.append("/-!")
		lines.append("## Goal Dependency Structure")
		lines.append("")
		for dep in goal_deps:
			gid = _goal_id(dep.goal_ts)
			if dep.prereq_intermediate_goals:
				prereq_ids = [_goal_id(int(ts)) for (ts, _) in dep.prereq_intermediate_goals
				              if int(ts) in goal_tid_set]
				if prereq_ids:
					lines.append(f"- goal_{gid} (tid={dep.goal_ts}) depends on goals: [{', '.join(prereq_ids)}]")
				else:
					prereq_tids = [ts for (ts, _) in dep.prereq_intermediate_goals]
					lines.append(f"- goal_{gid} (tid={dep.goal_ts}) depends on: {prereq_tids}")
			else:
				lines.append(f"- goal_{gid} (tid={dep.goal_ts}) has no prerequisites (base case)")
		lines.append("-/")
		lines.append("")

	# Goal-sliced graphs are emitted into per-goal files (if requested).
	if goal_slices and goals_out_dir is not None:
		goals_out_dir.mkdir(parents=True, exist_ok=True)
		deps_by_ts: Dict[int, GoalDependency] = {}
		if goal_deps:
			for dep in goal_deps:
				deps_by_ts[dep.goal_ts] = dep

		for i, sl in enumerate(goal_slices):
			goal_ts = int(sl.goal.ts)
			gid = _goal_id(goal_ts)
			dep = deps_by_ts.get(goal_ts)
			file_path = goals_out_dir / f"Goal_{gid}.lean"
			goal_lines: List[str] = []
			goal_lines.append("/- Auto-generated by Verdict/graph_to_lean.py")
			goal_lines.append(f"    Goal: {gid} (tensor id: {goal_ts})")
			goal_lines.append("-/")
			goal_lines.append(f"import {module_name}")
			goal_lines.append("")
			goal_lines.append("open TrainVerify.Denote")
			goal_lines.append("open TrainVerify.Denote.Generated")
			goal_lines.append("")
			goal_lines.append("namespace TrainVerify.Denote.GeneratedGoals")
			goal_lines.append("")

			sm_name = f"sm_goal_{gid}"
			pm_name = f"pm_goal_{gid}"

			# Emit sliced graphs
			def _emit_graph_local(name: str, nodes: List[Any], G: Any) -> None:
				goal_lines.append(f"def {name} : GraphDecl := by")
				if name.startswith("sm_"):
					num_ranks = 1
				else:
					num_ranks = max((_node_rank(n) for n in nodes), default=0) + 1
				local_num_parts = num_ranks
				embedding_params = _embedding_offset_params_by_node(G, nodes, num_parts=local_num_parts)
				goal_lines.append(f"  refine {{ numRanks := {num_ranks}, nodes := ?_ }}")
				goal_lines.append("  exact [")
				for n in nodes:
					op = escape_lean_string(_safe_str_op(G.node_opname(n)))
					ins = [int(t.tid) for t in G.node_inputs(n)]
					outs = [int(t.tid) for t in G.node_outputs(n)]
					rank = _node_rank(n)
					node_params = embedding_params.get(id(n)) or _get_node_params(G, n, num_parts=local_num_parts)
					params_str = f", params := {lean_list_nat(node_params)}" if node_params else ""
					goal_lines.append(
						f"    {{ rank := {rank}, op := \"{op}\", ins := {lean_list_nat(ins)}, outs := {lean_list_nat(outs)}{params_str} }},"
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
					f"def goal_{gid}_prereqs : List LineageGoal := {_prereq_list_expr(dep)}"
				)
				goal_lines.append(
					f"def goal_{gid}_cut_initGoals : List LineageGoal := initGoals ++ goal_{gid}_prereqs"
				)
			else:
				goal_lines.append(f"def goal_{gid}_cut_initGoals : List LineageGoal := initGoals")
			goal_lines.append("")

			goal_lines.append(f"def goal_{gid}_stmt_cut : Prop :=")
			goal_lines.append(
				f"  CoarseLineageHoldsWithInit {sm_name} {pm_name} goal_{gid}"
				f" {sm_name}InitEnv {pm_name}InitEnv goal_{gid}_cut_initGoals"
			)
			goal_lines.append("")

			goal_lines.append("end TrainVerify.Denote.GeneratedGoals")
			goal_lines.append("")

			file_path.write_text("\n".join(goal_lines) + "\n", encoding="utf-8")

			# ------------------------------------------------------------------
			# Emit Goal_{gid}_CutToFull.lean — the cut_to_full bridge that uses
			# denoteGraph_slice_agrees to lift the local `goal_N_stmt_cut` to
			# the global `goal_N_stmt`. Op-generic; zero op-specific handwriting.
			# See iroha-tasks/trainverify-bw/yoco-patterns/2026-07-02_cut_to_full_emitter_design.md
			# for the design walkthrough.
			# ------------------------------------------------------------------
			ctf_path = goals_out_dir / f"Goal_{gid}_CutToFull.lean"
			# Derive goals_module_prefix from goals_out_dir (e.g. "yoco_goals" → "denote.yoco_goals").
			goals_dir_name = goals_out_dir.name
			ctf_lines = _emit_cut_to_full(
				gid=gid,
				sl=sl,
				dep=dep,
				sm_graph=sm_graph,
				pm_graph=pm_graph,
				module_name=module_name,
				goals_module_prefix=f"denote.{goals_dir_name}",
				goal_id_fn=_goal_id,
			)
			ctf_path.write_text("\n".join(ctf_lines) + "\n", encoding="utf-8")

		# ------------------------------------------------------------------
		# Pattern/instance/main skeletons
		# ------------------------------------------------------------------
		def _module_parent(mod : str) -> str:
			parts = mod.split(".")
			return ".".join(parts[:-1]) if len(parts) > 1 else mod

		parent_module = _module_parent(module_name)

		def _canonical_nodes(nodes: List[Any], G: Any, *, num_parts: int) -> Tuple[Tuple[Any, ...], ...]:
			tid_to_sym: Dict[int, str] = {}
			embedding_params = _embedding_offset_params_by_node(G, nodes, num_parts=num_parts)

			def sym(tid: int) -> str:
				if tid not in tid_to_sym:
					tid_to_sym[tid] = f"v{len(tid_to_sym)}"
				return tid_to_sym[tid]

			out: List[Tuple[Any, ...]] = []
			for n in nodes:
				op = _safe_str_op(G.node_opname(n))
				rank = _node_rank(n)
				params = tuple(embedding_params.get(id(n)) or _get_node_params(G, n, num_parts=num_parts) or [])
				ins = tuple(sym(int(t.tid)) for t in G.node_inputs(n))
				outs = tuple(sym(int(t.tid)) for t in G.node_outputs(n))
				out.append((rank, op, params, ins, outs))
			return tuple(out)

		def _pattern_key(sl: GoalSlice) -> Tuple[Tuple[Any, ...], Tuple[Any, ...]]:
			pm_ranks = max((_node_rank(n) for n in sl.pm_nodes), default=0) + 1
			return (
				_canonical_nodes(sl.sm_nodes, sm_graph, num_parts=1),
				_canonical_nodes(sl.pm_nodes, pm_graph, num_parts=pm_ranks),
			)

		pattern_by_key: Dict[Tuple[Tuple[Any, ...], Tuple[Any, ...]], int] = {}
		pattern_members: Dict[int, List[str]] = {}
		pattern_hashes: Dict[int, str] = {}
		for sl in goal_slices:
			gid = _goal_id(int(sl.goal.ts))
			key = _pattern_key(sl)
			if key not in pattern_by_key:
				pid = len(pattern_by_key) + 1
				pattern_by_key[key] = pid
				pattern_hashes[pid] = hashlib.sha256(repr(key).encode("utf-8")).hexdigest()[:16]
				pattern_members[pid] = []
			pattern_members[pattern_by_key[key]].append(gid)

		for pid in sorted(pattern_members):
			members = pattern_members[pid]
			pattern_file_lines: List[str] = []
			pattern_file_lines.append("/- Auto-generated pattern proof file.")
			pattern_file_lines.append(f"   Pattern: {pid}")
			pattern_file_lines.append(f"   Hash: {pattern_hashes[pid]}")
			pattern_file_lines.append(f"   Goals: {', '.join(members)}")
			pattern_file_lines.append("-/")
			pattern_file_lines.append(f"import {module_name}")
			pattern_file_lines.append("")
			pattern_file_lines.append("open TrainVerify.Denote")
			pattern_file_lines.append("open TrainVerify.Denote.Generated")
			pattern_file_lines.append("")
			pattern_file_lines.append("namespace TrainVerify.Denote.GeneratedPatterns")
			pattern_file_lines.append("")
			pattern_file_lines.append(f"def pattern_{pid}_goalIds : List Nat := [{', '.join(members)}]")
			pattern_file_lines.append(f"inductive pattern_{pid}_target : Prop → Prop")
			for gid in members:
				pattern_file_lines.append(f"  | goal_{gid} : pattern_{pid}_target goal_{gid}_stmt_cut")
			pattern_file_lines.append("")
			pattern_file_lines.append(f"def pattern_{pid}_stmt : Prop :=")
			pattern_file_lines.append(f"  ∀ {{target : Prop}}, pattern_{pid}_target target → target")
			pattern_file_lines.append(f"theorem prove_pattern_{pid} : pattern_{pid}_stmt := by")
			pattern_file_lines.append("  -- TODO: prove this alpha-equivalence pattern once; all member goals instantiate it automatically.")
			pattern_file_lines.append("  sorry")
			pattern_file_lines.append("")
			pattern_file_lines.append("end TrainVerify.Denote.GeneratedPatterns")
			pattern_file_lines.append("")
			(goals_out_dir / f"Pattern_{pid}.lean").write_text(
				"\n".join(pattern_file_lines) + "\n", encoding="utf-8"
			)

		pattern_lines: List[str] = []
		pattern_lines.append("/- Auto-generated pattern index.")
		pattern_lines.append("   Individual proof obligations live in Pattern_N.lean files.")
		pattern_lines.append("-/")
		for pid in sorted(pattern_members):
			pattern_lines.append(f"import {parent_module}.Pattern_{pid}")
		pattern_lines.append("")
		pattern_lines.append("open TrainVerify.Denote")
		pattern_lines.append("open TrainVerify.Denote.Generated")
		pattern_lines.append("open TrainVerify.Denote.GeneratedPatterns")
		pattern_lines.append("")
		pattern_lines.append("namespace TrainVerify.Denote.GeneratedPatterns")
		pattern_lines.append("")
		pattern_lines.append(f"def numPatterns : Nat := {len(pattern_members)}")
		pattern_lines.append("")
		for pid in sorted(pattern_members):
			members = pattern_members[pid]
			pattern_lines.append(f"/-- pattern {pid}, hash {pattern_hashes[pid]}, goals: {', '.join(members)} -/")
			pattern_lines.append(f"def pattern_{pid}_summary : List Nat := pattern_{pid}_goalIds")
			pattern_lines.append("")
		pattern_lines.append("end TrainVerify.Denote.GeneratedPatterns")
		pattern_lines.append("")
		(goals_out_dir / "Patterns.lean").write_text("\n".join(pattern_lines) + "\n", encoding="utf-8")

		instance_lines: List[str] = []
		instance_lines.append("/- Auto-generated pattern instances.")
		instance_lines.append("   These theorems instantiate reusable Pattern_N proofs to concrete goals.")
		instance_lines.append("   They intentionally avoid importing Goal_N cut-proof files; the all-goals")
		instance_lines.append("   theorem is meant to depend on reusable pattern proofs only.")
		instance_lines.append("-/")
		for pid in sorted(pattern_members):
			instance_lines.append(f"import {parent_module}.Pattern_{pid}")
		instance_lines.append("")
		instance_lines.append("open TrainVerify.Denote")
		instance_lines.append("open TrainVerify.Denote.Generated")
		instance_lines.append("open TrainVerify.Denote.GeneratedPatterns")
		instance_lines.append("")
		instance_lines.append("namespace TrainVerify.Denote.GeneratedPatternInstances")
		instance_lines.append("")
		for sl in goal_slices:
			gid = _goal_id(int(sl.goal.ts))
			pid = pattern_by_key[_pattern_key(sl)]
			instance_lines.append(f"theorem prove_goal_{gid}_from_pattern_{pid} : goal_{gid}_stmt_cut := by")
			instance_lines.append(f"  exact prove_pattern_{pid} pattern_{pid}_target.goal_{gid}")
			instance_lines.append("")
		instance_lines.append("end TrainVerify.Denote.GeneratedPatternInstances")
		instance_lines.append("")
		(goals_out_dir / "Instances.lean").write_text("\n".join(instance_lines) + "\n", encoding="utf-8")

		# ------------------------------------------------------------------
		# Higher-level segment patterns.
		#
		# These are deliberately an extra layer on top of the concrete goals:
		# Goal_N files remain the faithful per-slice graph reflection.  Segment
		# patterns only package small repeated runs of goal statements so a human
		# can prove one bounded conjunction and instantiate it at multiple layers.
		# ------------------------------------------------------------------
		def _goal_primary_signature(sl: GoalSlice) -> Tuple[str, ...]:
			def first_op(nodes: List[Any], G: Any) -> str:
				if not nodes:
					return ""
				return _safe_str_op(G.node_opname(nodes[0]))

			# Use the SM-side primary op to detect layer-level repetitions.
			# The concrete segment theorem still mentions exact per-goal statements,
			# including all TP-side graph structure, so this does not simplify the
			# computation graph being proved.
			return (first_op(sl.sm_nodes, sm_graph),)

		def _detect_repeated_runs(signatures: List[Tuple[str, ...]]) -> List[Tuple[int, int, int]]:
			n = len(signatures)
			min_repeats = max(2, int(segment_min_repeats))
			max_period = max(2, min(int(segment_max_period), max(2, n // min_repeats)))
			candidates: List[Tuple[int, int, int, int]] = []
			for period in range(2, max_period + 1):
				start = 0
				while start + period * min_repeats <= n:
					repeats = 1
					while (
						start + period * (repeats + 1) <= n
						and signatures[start : start + period]
						== signatures[start + period * repeats : start + period * (repeats + 1)]
					):
						repeats += 1
					if repeats >= min_repeats:
						candidates.append((period * repeats, start, period, repeats))
						start += period * repeats
					else:
						start += 1

			candidates.sort(key=lambda x: (-x[0], x[1], x[2]))
			used = [False] * n
			out: List[Tuple[int, int, int]] = []
			for total, start, period, repeats in candidates:
				if any(used[i] for i in range(start, start + total)):
					continue
				for i in range(start, start + total):
					used[i] = True
				out.append((start, period, repeats))
			out.sort()
			return out

		def _conj_expr(props: List[str]) -> str:
			if not props:
				return "True"
			if len(props) == 1:
				return props[0]
			return f"{props[0]} ∧ ({_conj_expr(props[1:])})"

		def _conj_projection(base: str, idx: int, n: int) -> str:
			if n <= 1:
				return base
			if idx == 0:
				return f"{base}.left"
			return _conj_projection(f"{base}.right", idx - 1, n - 1)

		segment_goal_sources: Dict[str, str] = {}
		segment_pattern_count = 0
		segment_pattern_stats: Dict[int, str] = {}
		goal_slice_by_id: Dict[str, GoalSlice] = {
			_goal_id(int(sl.goal.ts)): sl for sl in goal_slices
		}

		def _op_summary_for_goal_ids(goal_ids_for_summary: List[str]) -> Tuple[int, int, str]:
			sm_count = 0
			pm_count = 0
			ops: List[str] = []
			for gid in goal_ids_for_summary:
				sl = goal_slice_by_id.get(gid)
				if sl is None:
					continue
				sm_count += len(sl.sm_nodes)
				pm_count += len(sl.pm_nodes)
				for n in sl.sm_nodes:
					op = _safe_str_op(sm_graph.node_opname(n))
					if op and op not in ops:
						ops.append(op)
				for n in sl.pm_nodes:
					op = _safe_str_op(pm_graph.node_opname(n))
					if op and op not in ops:
						ops.append(op)
			op_text = ", ".join(ops[:8])
			if len(ops) > 8:
				op_text += ", ..."
			return sm_count, pm_count, op_text

		if emit_segment_patterns and goal_slices:
			for old in goals_out_dir.glob("SegmentPattern_*.lean"):
				old.unlink()
			for old_name in ["SegmentPatterns.lean", "SegmentInstances.lean"]:
				old = goals_out_dir / old_name
				if old.exists():
					old.unlink()

			segment_max = max(2, int(segment_max_goals))
			goal_ids = [_goal_id(int(sl.goal.ts)) for sl in goal_slices]
			repeated_runs = _detect_repeated_runs([_goal_primary_signature(sl) for sl in goal_slices])
			segment_patterns: List[List[List[str]]] = []
			for start, period, repeats in repeated_runs:
				for offset in range(0, period, segment_max):
					size = min(segment_max, period - offset)
					if size < 2:
						continue
					instances: List[List[str]] = []
					for rep in range(repeats):
						i0 = start + rep * period + offset
						instance = goal_ids[i0 : i0 + size]
						if len(instance) == size:
							instances.append(instance)
					if len(instances) >= max(2, int(segment_min_repeats)):
						segment_patterns.append(instances)

			for sid, instances in enumerate(segment_patterns, start=1):
				segment_pattern_count += 1
				sm_ops, pm_ops, op_text = _op_summary_for_goal_ids(instances[0])
				segment_pattern_stats[sid] = (
					f"instances={len(instances)}, goals/instance={len(instances[0])}, "
					f"ops/instance: SM={sm_ops}, PM={pm_ops}, ops=[{op_text}]"
				)
				sp_lines: List[str] = []
				sp_lines.append("/- Auto-generated segment pattern proof file.")
				sp_lines.append(f"   Segment pattern: {sid}")
				sp_lines.append(f"   Goals per instance: {len(instances[0])}")
				sp_lines.append(f"   Instances: {len(instances)}")
				sp_lines.append(f"   Representative op scale: {segment_pattern_stats[sid]}")
				sp_lines.append("-/")
				sp_lines.append(f"import {module_name}")
				sp_lines.append("")
				sp_lines.append("open TrainVerify.Denote")
				sp_lines.append("open TrainVerify.Denote.Generated")
				sp_lines.append("")
				sp_lines.append("namespace TrainVerify.Denote.GeneratedSegmentPatterns")
				sp_lines.append("")
				for iid, instance in enumerate(instances, start=1):
					sp_lines.append(
						f"def segment_pattern_{sid}_instance_{iid}_goalIds : List Nat := [{', '.join(instance)}]"
					)
					sp_lines.append(f"def segment_pattern_{sid}_instance_{iid}_stmt : Prop :=")
					sp_lines.append("  " + _conj_expr([f"goal_{gid}_stmt" for gid in instance]))
					sp_lines.append("")
				sp_lines.append(f"inductive segment_pattern_{sid}_target : Prop → Prop")
				for iid in range(1, len(instances) + 1):
					sp_lines.append(
						f"  | inst_{iid} : segment_pattern_{sid}_target segment_pattern_{sid}_instance_{iid}_stmt"
					)
				sp_lines.append("")
				sp_lines.append(f"def segment_pattern_{sid}_stmt : Prop :=")
				sp_lines.append(f"  ∀ {{target : Prop}}, segment_pattern_{sid}_target target → target")
				sp_lines.append(f"theorem prove_segment_pattern_{sid} : segment_pattern_{sid}_stmt := by")
				sp_lines.append("  -- TODO: prove this bounded repeated segment once; each instance is a concrete conjunction.")
				sp_lines.append("  sorry")
				sp_lines.append("")
				sp_lines.append("end TrainVerify.Denote.GeneratedSegmentPatterns")
				sp_lines.append("")
				(goals_out_dir / f"SegmentPattern_{sid}.lean").write_text(
					"\n".join(sp_lines) + "\n", encoding="utf-8"
				)

			if segment_patterns:
				seg_index_lines: List[str] = []
				seg_index_lines.append("/- Auto-generated segment pattern index.")
				seg_index_lines.append("   These patterns package small repeated concrete goal runs.")
				seg_index_lines.append("-/")
				for sid in range(1, len(segment_patterns) + 1):
					seg_index_lines.append(f"import {parent_module}.SegmentPattern_{sid}")
				seg_index_lines.append("")
				seg_index_lines.append("open TrainVerify.Denote")
				seg_index_lines.append("open TrainVerify.Denote.Generated")
				seg_index_lines.append("open TrainVerify.Denote.GeneratedSegmentPatterns")
				seg_index_lines.append("")
				seg_index_lines.append("namespace TrainVerify.Denote.GeneratedSegmentPatterns")
				seg_index_lines.append("")
				seg_index_lines.append(f"def numSegmentPatterns : Nat := {len(segment_patterns)}")
				seg_index_lines.append("")
				seg_index_lines.append("end TrainVerify.Denote.GeneratedSegmentPatterns")
				seg_index_lines.append("")
				(goals_out_dir / "SegmentPatterns.lean").write_text(
					"\n".join(seg_index_lines) + "\n", encoding="utf-8"
				)

				seg_inst_lines: List[str] = []
				seg_inst_lines.append("/- Auto-generated segment pattern instances.")
				seg_inst_lines.append("   Each theorem projects one concrete goal from a segment conjunction.")
				seg_inst_lines.append("   This optional layer is not used by MainTheorem's pattern-to-all_goals path.")
				seg_inst_lines.append("-/")
				for sid in range(1, len(segment_patterns) + 1):
					seg_inst_lines.append(f"import {parent_module}.SegmentPattern_{sid}")
				seg_inst_lines.append("")
				seg_inst_lines.append("open TrainVerify.Denote")
				seg_inst_lines.append("open TrainVerify.Denote.Generated")
				seg_inst_lines.append("open TrainVerify.Denote.GeneratedSegmentPatterns")
				seg_inst_lines.append("")
				seg_inst_lines.append("namespace TrainVerify.Denote.GeneratedSegmentInstances")
				seg_inst_lines.append("")
				for sid, instances in enumerate(segment_patterns, start=1):
					for iid, instance in enumerate(instances, start=1):
						for idx, gid in enumerate(instance):
							if gid in segment_goal_sources:
								continue
							thm = f"prove_goal_{gid}_from_segment_{sid}_{iid}"
							segment_goal_sources[gid] = thm
							seg_inst_lines.append(f"theorem {thm} : goal_{gid}_stmt := by")
							seg_inst_lines.append(
								f"  have h := prove_segment_pattern_{sid} segment_pattern_{sid}_target.inst_{iid}"
							)
							seg_inst_lines.append(f"  exact {_conj_projection('h', idx, len(instance))}")
							seg_inst_lines.append("")
				seg_inst_lines.append("end TrainVerify.Denote.GeneratedSegmentInstances")
				seg_inst_lines.append("")
				(goals_out_dir / "SegmentInstances.lean").write_text(
					"\n".join(seg_inst_lines) + "\n", encoding="utf-8"
				)

		main_patterns: Dict[int, List[str]] = {}
		if goal_slices:
			for sl in goal_slices:
				gid = _goal_id(int(sl.goal.ts))
				pid = pattern_by_key[_pattern_key(sl)]
				main_patterns.setdefault(pid, []).append(gid)

		obligation_lines: List[str] = []
		obligation_lines.append("/- Auto-generated human proof obligation index.")
		obligation_lines.append("")
		obligation_lines.append("This is the intended entry point for human proof work.")
		obligation_lines.append("Files imported here contain the reusable theorems whose bodies still need proofs.")
		obligation_lines.append("`Instances.lean` projects Pattern_N proofs to concrete goals, and")
		obligation_lines.append("`MainTheorem.lean` composes those projections into `all_goals_stmt`.")
		obligation_lines.append("")
		if segment_pattern_count > 0:
			obligation_lines.append("Optional segment proof packages, not needed for all_goals_stmt:")
			for sid in range(1, segment_pattern_count + 1):
				stats = segment_pattern_stats.get(sid, "")
				obligation_lines.append(
					f"  - SegmentPattern_{sid}.lean: prove_segment_pattern_{sid}"
					+ (f"  -- {stats}" if stats else "")
				)
		else:
			obligation_lines.append("Optional segment proof packages: none")
		obligation_lines.append("")
		if main_patterns:
			obligation_lines.append("Pattern proof obligations for all_goals_stmt:")
			for pid in sorted(main_patterns):
				members = ", ".join(main_patterns[pid])
				sm_ops, pm_ops, op_text = _op_summary_for_goal_ids([main_patterns[pid][0]])
				stats = (
					f"instances={len(main_patterns[pid])}, "
					f"ops/instance: SM={sm_ops}, PM={pm_ops}, ops=[{op_text}]"
				)
				obligation_lines.append(
					f"  - Pattern_{pid}.lean: prove_pattern_{pid}"
					f"  -- {stats}; concrete goals: {members}"
				)
		else:
			obligation_lines.append("Pattern proof obligations for all_goals_stmt: none")
		obligation_lines.append("-/")
		for pid in sorted(main_patterns):
			obligation_lines.append(f"import {parent_module}.Pattern_{pid}")
		obligation_lines.append("")
		obligation_lines.append("namespace TrainVerify.Denote.GeneratedProofObligations")
		obligation_lines.append("")
		obligation_lines.append(f"def optionalSegmentProofPackageCount : Nat := {segment_pattern_count}")
		obligation_lines.append(f"def humanPatternProofCount : Nat := {len(main_patterns)}")
		obligation_lines.append(f"def humanProofObligationCount : Nat := {len(main_patterns)}")
		obligation_lines.append("")
		obligation_lines.append("end TrainVerify.Denote.GeneratedProofObligations")
		obligation_lines.append("")
		(goals_out_dir / "ProofObligations.lean").write_text(
			"\n".join(obligation_lines) + "\n", encoding="utf-8"
		)

		main_lines: List[str] = []
		main_lines.append("/- Auto-generated main composition skeleton.")
		main_lines.append("   This file composes reusable pattern proofs into all_goals_stmt.")
		main_lines.append("-/")
		main_lines.append(f"import {parent_module}.Instances")
		main_lines.append("")
		main_lines.append("set_option maxRecDepth 100000")
		main_lines.append("set_option linter.style.emptyLine false")
		main_lines.append("")
		main_lines.append("open TrainVerify.Denote")
		main_lines.append("open TrainVerify.Denote.Generated")
		main_lines.append("open TrainVerify.Denote.GeneratedPatternInstances")
		main_lines.append("")
		main_lines.append("namespace TrainVerify.Denote.GeneratedMain")
		main_lines.append("")
		main_lines.append("def fullGraphSegment : SegmentDecl :=")
		main_lines.append("  { name := \"full\", sm := sm, pm := pm, goals := goals }")
		main_lines.append("")
		main_lines.append("def graphSegments : List SegmentDecl := [fullGraphSegment]")
		main_lines.append("")
		main_lines.append("theorem graphSegments_cover : GraphCoverage sm pm graphSegments := by")
		main_lines.append("  unfold GraphCoverage concatSMGraph concatPMGraph graphSegments fullGraphSegment")
		main_lines.append("  refine ⟨rfl, rfl⟩")
		main_lines.append("")
		main_lines.append("theorem forall_mem_append_goal {xs ys : List LineageGoal}")
		main_lines.append("    (hx : ∀ g ∈ xs, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals)")
		main_lines.append("    (hy : ∀ g ∈ ys, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals) :")
		main_lines.append("    ∀ g ∈ xs ++ ys, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by")
		main_lines.append("  intro g hg")
		main_lines.append("  have h := List.mem_append.mp hg")
		main_lines.append("  cases h with")
		main_lines.append("  | inl h => exact hx g h")
		main_lines.append("  | inr h => exact hy g h")
		main_lines.append("")
		main_lines.append("/-- Main generated composition theorem.")
		main_lines.append("")
		main_lines.append("Assuming every reusable Pattern_N proof is complete, this file instantiates")
		main_lines.append("those proofs for every concrete goal and composes them into `all_goals_stmt`.")
		main_lines.append("It deliberately stops at the lineage-goal layer rather than claiming a")
		main_lines.append("stronger full-graph equivalence theorem.")
		main_lines.append("-/")
		if goal_slices:
			chunk_size = 8
			chunked_slices = [
				goal_slices[i : i + chunk_size] for i in range(0, len(goal_slices), chunk_size)
			]
			for cid, chunk in enumerate(chunked_slices, start=1):
				main_lines.append("")
				main_lines.append(
					f"theorem gpt_goal_chunk_{cid}_all : ∀ g ∈ goalChunk_{cid}, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by"
				)
				main_lines.append("  intro g hg")
				main_lines.append(f"  unfold goalChunk_{cid} at hg")
				indent = "  "
				for idx, sl in enumerate(chunk):
					gid = _goal_id(int(sl.goal.ts))
					pid = pattern_by_key[_pattern_key(sl)]
					main_lines.append(f"{indent}cases hg with")
					main_lines.append(f"{indent}| head =>")
					main_lines.append(f"{indent}  exact prove_goal_{gid}_from_pattern_{pid}")
					main_lines.append(f"{indent}| tail _ hg =>")
					if idx == len(chunk) - 1:
						main_lines.append(f"{indent}  cases hg")
					else:
						indent += "  "
			main_lines.append("")
			main_lines.append("theorem gpt_main_all_goals : all_goals_stmt := by")
			main_lines.append("  unfold all_goals_stmt goals")
			append_expr = f"gpt_goal_chunk_{len(chunked_slices)}_all"
			for cid in range(len(chunked_slices) - 1, 0, -1):
				append_expr = f"(forall_mem_append_goal gpt_goal_chunk_{cid}_all {append_expr})"
			main_lines.append(f"  exact {append_expr}")
		else:
			main_lines.append("theorem gpt_main_all_goals : all_goals_stmt := by")
			main_lines.append("  intro g hg")
			main_lines.append("  contradiction")
		main_lines.append("")
		main_lines.append("end TrainVerify.Denote.GeneratedMain")
		main_lines.append("")
		(goals_out_dir / "MainTheorem.lean").write_text("\n".join(main_lines) + "\n", encoding="utf-8")

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

	t0 = time.perf_counter()
	coarse = infer_coarse_lineages_from_expanded(GsE, GpE)
	print(f"[graph_to_lean] inferred {len(coarse)} coarse lineages in {time.perf_counter() - t0:.2f}s", flush=True)
	by_ts: Dict[int, List[Any]] = {}
	for l in coarse:
		Ts = getattr(l, "Ts")
		by_ts.setdefault(int(Ts.tid), []).append(l)

	# Compute init tids early so we can exclude them from goals
	# (init tids are assumptions, not things to prove)
	# We need sm_nodes first, so we do a preliminary backward closure from all by_ts keys
	all_lineage_tids = sorted(by_ts.keys())
	t0 = time.perf_counter()
	_preliminary_sm_needed = backward_closure_tids(GsC, all_lineage_tids)
	_preliminary_sm_needed_set = set(_preliminary_sm_needed)
	_preliminary_sm_nodes = [n for n in GsE.nodes() if any(
		int(t.tid) in _preliminary_sm_needed_set for t in GsE.node_outputs(n)
	) and "DATALOADER" not in _safe_str_op(GsE.node_opname(n))
	   and "pyfunc" not in _safe_str_op(GsE.node_opname(n)).lower()]
	sm_init_tids_preliminary = set(_init_tids_from_kept_nodes(GsE, _preliminary_sm_nodes))
	print(f"[graph_to_lean] computed preliminary SM boundary in {time.perf_counter() - t0:.2f}s", flush=True)

	# Observable outputs: aligned leaves by default.
	# If --include-intermediate-goals or --split-goals, include all intermediate tensors
	# with lineages (not just leaf outputs), excluding init tids.
	# --split-goals implies intermediate goals because we need fine-grained subgraph cuts.
	if args.include_intermediate_goals or args.split_goals:
		candidates = sorted([tid for tid in by_ts.keys() if tid not in sm_init_tids_preliminary])
	else:
		candidates = leaf_output_tids(GsC)
	obs_tids = [tid for tid in candidates if tid in by_ts]
	if args.max_goals and args.max_goals > 0:
		obs_tids = obs_tids[: int(args.max_goals)]

	normalize_pm_lineage = make_collective_lineage_normalizer(GpE)

	t0 = time.perf_counter()
	selected: List[SelectedLineage] = []
	for ts in obs_tids:
		chosen = pick_one_lineage_for_ts(by_ts.get(int(ts), []), ts)
		if chosen is not None:
			chosen = normalize_pm_lineage(chosen)
			chosen = compress_if_replicated(chosen)
			selected.append(chosen)

	selected.sort(key=lambda g: g.ts)
	print(f"[graph_to_lean] selected {len(selected)} goals in {time.perf_counter() - t0:.2f}s", flush=True)

	# Restrict graph declarations to the subgraph needed for the selected goals.
	t0 = time.perf_counter()
	sm_needed_tids = backward_closure_tids(GsC, [g.ts for g in selected])
	pm_roots = [tp_tid for g in selected for (_, tp_tid) in g.tps]
	pm_needed_tids = backward_closure_tids(GpE, pm_roots)
	print(f"[graph_to_lean] computed full graph closures in {time.perf_counter() - t0:.2f}s", flush=True)

	def _filter_nodes(G: Any, needed_tids: set[int], stop_tids: Optional[set[int]] = None) -> List[Any]:
		kept: List[Any] = []
		for n in G.nodes():
			outs = [int(t.tid) for t in G.node_outputs(n)]
			# Skip DATALOADER / pyfunc in denotational semantics: treat those
			# tensors as coming from init store.
			opname = _safe_str_op(G.node_opname(n))
			if "DATALOADER" in opname or "pyfunc" in opname.lower():
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
		
		CROSS_DP_WRED is a special case: all ranks share the same inputs but each outputs
		a different tid. We group by (op, sorted(inputs)) and keep only rank 0's node,
		but modify its outputs to include all tids from all ranks.
		"""
		def _is_collective(op: str) -> bool:
			return ("AllReducePrim" in op) or ("AllGatherPrim" in op)
		
		def _is_cross_dp_wred(op: str) -> bool:
			return "CROSS_DP_WRED" in op
		
		# Standard collectives: group by (op, ins, outs)
		groups: Dict[tuple[str, tuple[int, ...], tuple[int, ...]], List[Any]] = {}
		for n in nodes:
			op = _safe_str_op(G.node_opname(n))
			if not _is_collective(op):
				continue
			ins = tuple(int(t.tid) for t in G.node_inputs(n))
			outs = tuple(int(t.tid) for t in G.node_outputs(n))
			groups.setdefault((op, ins, outs), []).append(n)

		chosen: set[Any] = set()
		for (_k, ns) in groups.items():
			rep = min(ns, key=_node_rank)
			chosen.add(rep)

		# CROSS_DP_WRED: group by (op, sorted(ins)), keep rank 0
		wred_groups: Dict[tuple[str, tuple[int, ...]], List[Any]] = {}
		for n in nodes:
			op = _safe_str_op(G.node_opname(n))
			if not _is_cross_dp_wred(op):
				continue
			ins = tuple(sorted(int(t.tid) for t in G.node_inputs(n)))
			wred_groups.setdefault((op, ins), []).append(n)
		
		wred_chosen: set[Any] = set()
		for (_k, ns) in wred_groups.items():
			rep = min(ns, key=_node_rank)
			wred_chosen.add(rep)

		out: List[Any] = []
		for n in nodes:
			op = _safe_str_op(G.node_opname(n))
			if _is_collective(op):
				if n in chosen:
					out.append(n)
			elif _is_cross_dp_wred(op):
				if n in wred_chosen:
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
		users: List[List[int]] = [[] for _ in nodes]
		for i, n in enumerate(nodes):
			for t in G.node_inputs(n):
				for j in producers.get(int(t.tid), []):
					if j != i:
						if j not in deps[i]:
							deps[i].add(j)
							users[j].append(i)

		indeg = [len(deps_i) for deps_i in deps]
		# Stable queue: pick nodes with indeg=0 in original order.
		queue = deque(i for i, d in enumerate(indeg) if d == 0)
		out_idx: List[int] = []
		while queue:
			i = queue.popleft()
			out_idx.append(i)
			for k in users[i]:
				indeg[k] -= 1
				if indeg[k] == 0:
					queue.append(k)

		# If cycle/unknown deps remain, fall back to original order.
		if len(out_idx) != len(nodes):
			return nodes
		return [nodes[i] for i in out_idx]

	t0 = time.perf_counter()
	sm_nodes = _filter_nodes(GsE, set(sm_needed_tids))
	pm_nodes = _filter_nodes(GpE, set(pm_needed_tids))

	# Ensure the denotational fold is a true topological fold across ranks.
	sm_nodes = _toposort_nodes(GsE, sm_nodes)
	pm_nodes = _toposort_nodes(GpE, _dedup_shared_collectives(GpE, pm_nodes))
	print(f"[graph_to_lean] filtered/toposorted graph nodes in {time.perf_counter() - t0:.2f}s", flush=True)

	def _filter_ordered_nodes(
		G: Any, ordered_nodes: List[Any], needed_tids: set[int], stop_tids: Optional[set[int]] = None
	) -> List[Any]:
		"""Filter an already-toposorted node list; any subsequence remains topologically ordered."""
		kept: List[Any] = []
		for n in ordered_nodes:
			outs = [int(t.tid) for t in G.node_outputs(n)]
			if stop_tids is None:
				if any(tid in needed_tids for tid in outs):
					kept.append(n)
				continue
			if any((tid in needed_tids) and (tid not in stop_tids) for tid in outs):
				kept.append(n)
		return kept

	def _make_ordered_node_filter(G: Any, ordered_nodes: List[Any]):
		order = {n: i for i, n in enumerate(ordered_nodes)}
		by_out_tid: Dict[int, List[Any]] = {}
		outs_by_node: Dict[Any, List[int]] = {}
		for n in ordered_nodes:
			outs = [int(t.tid) for t in G.node_outputs(n)]
			outs_by_node[n] = outs
			for tid in outs:
				by_out_tid.setdefault(tid, []).append(n)

		def filter_nodes(needed_tids: set[int], stop_tids: Optional[set[int]] = None) -> List[Any]:
			candidates: set[Any] = set()
			for tid in needed_tids:
				for n in by_out_tid.get(int(tid), []):
					candidates.add(n)
			if stop_tids is not None:
				stop = set(stop_tids)
				candidates = {
					n
					for n in candidates
					if any((tid in needed_tids) and (tid not in stop) for tid in outs_by_node[n])
				}
			return sorted(candidates, key=lambda n: order[n])

		return filter_nodes

	def _make_backward_closure_until(G: Any):
		prod_inputs: Dict[int, List[List[int]]] = {}
		for n in G.nodes():
			_op = _safe_str_op(G.node_opname(n))
			if "DATALOADER" in _op or "pyfunc" in _op.lower():
				continue
			input_tids = [int(t.tid) for t in G.node_inputs(n)]
			for t in G.node_outputs(n):
				prod_inputs.setdefault(int(t.tid), []).append(input_tids)
		cache: Dict[Tuple[Tuple[int, ...], Tuple[int, ...]], List[int]] = {}

		def closure(root_tids: Iterable[int], stop_tids: Iterable[int]) -> List[int]:
			roots = tuple(sorted(int(t) for t in root_tids))
			stop = tuple(sorted(int(t) for t in stop_tids))
			key = (roots, stop)
			if key in cache:
				return cache[key]
			stop_set = set(stop)
			seen: set[int] = set(roots)
			frontier: set[int] = set(seen)
			while frontier:
				nxt: set[int] = set()
				for tid in list(frontier):
					if int(tid) in stop_set:
						continue
					for input_tids in prod_inputs.get(int(tid), []):
						for t_id in input_tids:
							if t_id not in seen:
								seen.add(t_id)
								nxt.add(t_id)
				frontier = nxt
			out = sorted(seen)
			cache[key] = out
			return out

		return closure

	sm_backward_until = _make_backward_closure_until(GsC)
	pm_backward_until = _make_backward_closure_until(GpE)
	filter_sm_goal_nodes = _make_ordered_node_filter(GsE, sm_nodes)
	filter_pm_goal_nodes = _make_ordered_node_filter(GpE, pm_nodes)

	# Init/boundary tids for the kept subgraph (SM side). We'll generate init-alignment goals
	# only for those that the aligner can match.
	sm_init_tids = _init_tids_from_kept_nodes(GsE, sm_nodes)

	init_selected: List[SelectedLineage] = []
	for tid in sm_init_tids:
		chosen = pick_one_lineage_for_ts(by_ts.get(int(tid), []), int(tid))
		if chosen is None:
			continue
		chosen = normalize_pm_lineage(chosen)
		chosen = canonicalize_init_lineage_multiref(GpE, chosen)
		init_selected.append(compress_if_replicated(chosen))
	init_selected.sort(key=lambda g: g.ts)

	# Compute goal dependencies to enable incremental proofs
	init_tid_set = set(sm_init_tids)
	t0 = time.perf_counter()
	goal_deps, intermediate_lineages = compute_goal_dependencies(
		GsC, selected, by_ts, init_tid_set
	)
	print(f"[graph_to_lean] computed goal dependencies in {time.perf_counter() - t0:.2f}s", flush=True)
	if intermediate_lineages:
		for k, lin in list(intermediate_lineages.items()):
			lin = normalize_pm_lineage(lin)
			lin = compress_if_replicated(lin)
			intermediate_lineages[k] = lin

	# Final output goals take precedence over dependency/intermediate goals. This
	# is an explicit set policy (YOCO A0.4B deduplicates tid 4680), not a naming
	# side effect in the Lean emitter.
	intermediate_lineages, deduplicated_intermediate_tids = deduplicate_intermediate_lineages(
		selected, intermediate_lineages
	)
	print(
		f"[graph_to_lean] deduplicated final/intermediate tids: {deduplicated_intermediate_tids}",
		flush=True,
	)

	# Light sanity checks for intermediate lineages used as prerequisites
	pm_num_ranks = max((_node_rank(n) for n in GpE.nodes()), default=0) + 1
	validated_intermediate_tids: set[int] = set()
	for dep in goal_deps:
		for (inter_ts, lin) in dep.prereq_intermediate_goals:
			if int(inter_ts) in validated_intermediate_tids:
				continue
			validated_intermediate_tids.add(int(inter_ts))
			issues = _validate_lineage_against_graphs(lin, GsE, GpE, pm_num_ranks)
			if issues:
				print(f"WARNING: lineage sanity check issues for intermediate ts={inter_ts}:")
				for msg in issues:
					print(f"  - {msg}")

	# Optional: build per-goal sliced graphs (cut at prerequisite intermediate tensors).
	goal_slices: Optional[List[GoalSlice]] = None
	if args.split_goals:
		t0 = time.perf_counter()
		deps_by_ts: Dict[int, GoalDependency] = {d.goal_ts: d for d in goal_deps}
		goal_slices = []
		for g in selected:
			dep = deps_by_ts.get(int(g.ts))
			prereq_lineages: List[SelectedLineage] = []
			if dep and dep.prereq_intermediate_goals:
				# IMPORTANT: use the SAME (normalized) lineage that is emitted as the
				# goal_N prerequisite LineageGoal. compute_goal_dependencies() records the
				# RAW lineage (collective shard tps), but the emitted goal_<ts> def and its
				# InitGoalHolds use the collective-normalized form (e.g. an AllReduce output
				# collapsed to a single replicated tid). If we slice the PM subgraph against
				# the raw shard tps while the init goal only constrains the normalized tid,
				# the cut PM graph re-derives the collective from unconstrained shard inits
				# and the goal becomes unprovable. Prefer the normalized intermediate_lineages
				# entry so the cut boundary == the constrained init tensor.
				for (_ts, lin) in dep.prereq_intermediate_goals:
					norm = intermediate_lineages.get(int(_ts))
					if norm is None:
						norm = compress_if_replicated(normalize_pm_lineage(lin))
					prereq_lineages.append(norm)

			stop_sm_tids = set(sm_init_tids) | {int(lin.ts) for lin in prereq_lineages}
			needed_sm = sm_backward_until([int(g.ts)], stop_sm_tids)
			sm_nodes_goal = filter_sm_goal_nodes(set(needed_sm), stop_tids=set(stop_sm_tids))

			stop_pm_tids: set[int] = set()
			for lin in prereq_lineages:
				for (_r, tp_tid) in lin.tps:
					stop_pm_tids.add(int(tp_tid))
			pm_roots_goal = [int(tp_tid) for (_r, tp_tid) in g.tps]
			needed_pm = pm_backward_until(pm_roots_goal, stop_pm_tids)
			pm_nodes_goal = filter_pm_goal_nodes(set(needed_pm), stop_tids=set(stop_pm_tids))

			goal_slices.append(GoalSlice(goal=g, sm_nodes=sm_nodes_goal, pm_nodes=pm_nodes_goal))
			if len(goal_slices) % 100 == 0:
				print(f"[graph_to_lean] sliced {len(goal_slices)} / {len(selected)} goals", flush=True)
		print(f"[graph_to_lean] built {len(goal_slices)} goal slices in {time.perf_counter() - t0:.2f}s", flush=True)
	
	# Print dependency info
	print("Goal dependencies (for incremental proofs):")
	if len(goal_deps) > 100:
		num_with_prereqs = sum(1 for dep in goal_deps if dep.prereq_intermediate_goals)
		max_prereqs = max((len(dep.prereq_intermediate_goals) for dep in goal_deps), default=0)
		print(
			f"  {len(goal_deps)} goals; {num_with_prereqs} have prerequisites; max prereqs={max_prereqs}"
		)
	else:
		for dep in goal_deps:
			if dep.prereq_intermediate_goals:
				prereq_tids = [ts for (ts, _) in dep.prereq_intermediate_goals]
				print(f"  goal_{dep.goal_ts} depends on intermediate tensors: {prereq_tids}")
			else:
				print(f"  goal_{dep.goal_ts} has no prerequisites")
	
	if intermediate_lineages:
		if len(intermediate_lineages) > 100:
			keys = sorted(intermediate_lineages.keys())
			print(f"Intermediate lineage goals: {len(keys)} tids, range={keys[0]}..{keys[-1]}")
		else:
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
		use_tid_goal_ids=bool(args.use_tid_goal_ids),
		emit_segment_patterns=bool(args.emit_segment_patterns),
		segment_max_goals=int(args.segment_max_goals),
		segment_min_repeats=int(args.segment_min_repeats),
		segment_max_period=int(args.segment_max_period),
		manifest_name=Path(args.manifest_out).name if args.manifest_out else None,
	)

	if args.manifest_out:
		from Verdict.provenance import (
			ProvenanceError, build_manifest, git_revision,
			installed_package_versions, write_manifest,
		)
		if not args.llm_train_repo or not args.nnscaler_repo or not args.metadata_json:
			raise ProvenanceError(
				"--manifest-out requires --llm-train-repo, --nnscaler-repo, and --metadata-json"
			)
		llm_revision = git_revision(args.llm_train_repo)
		nnscaler_revision = git_revision(args.nnscaler_repo)
		if args.llm_train_revision and args.llm_train_revision.lower() != llm_revision:
			raise ProvenanceError("llm-train checkout does not match --llm-train-revision")
		if args.nnscaler_revision and args.nnscaler_revision.lower() != nnscaler_revision:
			raise ProvenanceError("nnScaler checkout does not match --nnscaler-revision")
		expected_hashes: Dict[str, str] = {}
		if args.sm_pkl_sha256:
			expected_hashes["sm_pkl_sha256"] = args.sm_pkl_sha256
		if args.pm_pkl_sha256:
			expected_hashes["pm_pkl_sha256"] = args.pm_pkl_sha256
		for item in args.metadata_sha256:
			if "=" not in item:
				raise ProvenanceError("--metadata-sha256 must be NAME=SHA256")
			name, digest = item.split("=", 1)
			expected_hashes[f"metadata_sha256.{name}"] = digest
		manifest = build_manifest(
			model=args.model, sm_pkl=args.sm_pkl, pm_pkl=args.pm_pkl,
			metadata_files=args.metadata_json, llm_train_commit=llm_revision,
			nnscaler_commit=nnscaler_revision, emitter=Path(__file__),
			generated_lean=out_path, command=sys.argv,
			packages=installed_package_versions(["torch", "nnscaler", "dill"]),
			deduplicated_intermediate_tids=deduplicated_intermediate_tids,
			final_goal_tids=[g.ts for g in selected],
			intermediate_goal_tids=sorted(intermediate_lineages),
			expected_hashes=expected_hashes,
		)
		write_manifest(args.manifest_out, manifest)
		print(f"Wrote provenance manifest to: {args.manifest_out}")

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
