#!/usr/bin/env python3
"""Bridge emitter — UNIVERSAL renderer (per-node, covers all topologies).

Design (style-1, validated against Goal30/Goal44/Goal6/Goal9/Goal28/Goal3):
  * exactly ONE sm node.
  * PM mini-graph = linear node list. mid nodes (outs are intermediate) -> pm_full_<out>;
    final nodes (outs in lineage.tps) -> denote_pm + pm_frame.
  * denote_pm_goal_N_<final> RHS = fully-nested expr, literal K=4, `s` accessor.
  * pm_frame_<final>_self : denoteGraph pm initPM final = same nested expr with
    `denoteGraph pm initPM` accessor; proven by pm_val + applyNode + pm_prefix +
    rw all pm_full (reverse-topo) + (if collective present) convert pm.numRanks=4.
  * Assembly (cut_to_full / hInitCut / shapes) reused from renderer.py.
"""
import os, sys
from dataclasses import dataclass

sys.path.insert(0, os.path.dirname(__file__))
import renderer as R   # reuse proven assembly blocks
from renderer import InputSource

# ---------------- operator metadata ----------------
# pointwise op -> (denote_fn, applyNode_lemma, arity, has_params, params_before_ins)
# arg rendering: params (if params_before_ins) then ins, each input as `(acc tid)`.
POINTWISE = {
    "FW_layernorm": ("fw_layernorm", "applyNode_fw_layernorm_out", None, False, False),
    "FW_gelu":      ("fw_gelu",      "applyNode_fw_gelu_out",      None, False, False),
    "FW_linear":    ("fw_linear",    "applyNode_fw_linear_out",    None, False, False),
    "FW_matmul":    ("fw_matmul",    "applyNode_fw_matmul_out",    None, False, False),
    "FW_embedding": ("fw_embedding", "applyNode_fw_embedding_out", None, False, False),
    "FW_sum":       ("fw_sum",       "applyNode_fw_sum_out",       None, False, False),
    "FW_add":       ("elemwiseAdd",  "applyNode_fw_add2_out",      None, False, False),
    "FW_view":      ("fw_view",      "applyNode_fw_view_out",      None, True,  True),
    "FW_transpose": ("transposeAxes","applyNode_fw_transposeAxes_out", None, True, True),
    # Family D pointwise ops. Only per-goal `_gNNN`-suffixed lemmas exist in the
    # INVIOLABLE Denote.lean; but those lemmas are fully goal-agnostic (universally
    # quantified g/s/rank/tids/params, evalOp by rfl). So we emit PRIVATE local
    # copies (`_loc`) at the top of each bridge and point the table at them — never
    # touching Denote.lean. fw_div carries a scalar param `params.head?.getD 1`.
    "FW_softmax":    ("fw_softmax",    "applyNode_fw_softmax_out_loc",    None, False, False),
    "FW_contiguous": ("fw_contiguous", "applyNode_fw_contiguous_out_loc", None, False, False),
    "FW_div":        ("fw_div",        "applyNode_fw_div_out_loc",        None, True,  True),
    # ---- Backward-pass SINGLE-OUTPUT pointwise ops --------------------------
    # ins = [gTid, xTid, ...]; FIRST input is the gradient. The output depends on
    # `s gTid` (+ params); trailing inputs are present only for the applyNode lemma
    # signature and are dropped from the RHS. Rendering handled by the BW branch in
    # `_pointwise_expr` (keyed off the op name starting with "BW_"). Generic (goal-
    # agnostic) applyNode lemmas already live in the INVIOLABLE Denote.lean (axiom or
    # theorem); ops with only `_gNNN` versions get a private `_loc` copy per-bridge.
    # 5-tuple kept for consumer compatibility: (fn, lemma, arity, has_params, pbefore)
    "BW_sum":        ("bw_sum",        "applyNode_bw_sum_out",            None, False, False),
    "BW_gelu":       ("bw_gelu",       "applyNode_bw_gelu_out",           None, False, False),
    "BW_view":       ("fw_view",       "applyNode_bw_view_out",           None, True,  True),
    "BW_transpose":  ("transposeAxes", "applyNode_bw_transposeAxes_out",   None, True,  True),
    "BW_contiguous": ("id",            "applyNode_bw_contiguous_out_loc", None, False, False),
    "BW_div":        ("bw_div",        "applyNode_bw_div_out_loc",        None, True,  True),
    "BW_softmax":    ("bw_softmax",    "applyNode_bw_softmax_out_loc",    None, False, False),
    "BW_multiref":   ("tensorSum",     "applyNode_bw_multiref_out",       None, False, False),
    # BW_embedding: ins = [gTid, idsTid, wTid]; RHS = bw_embedding (s g) (s ids) (s w)
    # — uses ALL THREE inputs (NOT grad-only). params=[offset] selects the vocab-parallel
    # offset variant (applyNode_bw_embedding_offset_out + bw_embedding_offset). Rendering
    # is special-cased in `_pointwise_expr` (BW branch) and `_rhs_ins` keeps all 3 ins.
    "BW_embedding":  ("bw_embedding",  "applyNode_bw_embedding_out",       None, False, False),
}

# Family D pointwise ops -> the private local lemma text (goal-agnostic copies of
# Denote.lean's `_gNNN` versions) + the post-helper normalization tactic (fw_div's
# RHS holds a `((params.head?.getD 1 : Nat) : Scalar)` that `norm_num` must reduce).
OP_LOCAL = {
    "FW_softmax":    dict(post=""),
    "FW_contiguous": dict(post=""),
    "FW_div":        dict(post="  norm_num\n"),
    # backward ops whose only Denote.lean applyNode lemma is `_gNNN`-suffixed.
    "BW_softmax":    dict(post=""),
    "BW_contiguous": dict(post=""),
    "BW_div":        dict(post="  norm_num\n"),
}

# Emitted ONCE at the top of a bridge for each Family-D op actually used. Each is a
# `private` goal-agnostic lemma so it cannot collide with anything in Denote.lean.
OP_LOCAL_LEMMA = {
    "FW_softmax": '''\
-- [EMITTER] local generic FW_softmax applyNode lemma (goal-agnostic; mirrors Denote.lean _gNNN).
private theorem evalOp_fw_softmax_loc (numParts rank : Nat) (params : List Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_softmax" params [x] = [fw_softmax x] := rfl
private theorem applyNode_fw_softmax_out_loc
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_softmax", ins := [xTid], outs := [outTid], params := params } outTid = fw_softmax (s xTid) := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_softmax_loc]
  change storeSet s [(outTid, fw_softmax (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]
''',
    "FW_contiguous": '''\
-- [EMITTER] local generic FW_contiguous applyNode lemma (goal-agnostic; mirrors Denote.lean _gNNN).
private theorem evalOp_fw_contiguous_loc (numParts rank : Nat) (params : List Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_contiguous" params [x] = [fw_contiguous x] := rfl
private theorem applyNode_fw_contiguous_out_loc
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_contiguous", ins := [xTid], outs := [outTid], params := params } outTid = fw_contiguous (s xTid) := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_contiguous_loc]
  change storeSet s [(outTid, fw_contiguous (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]
''',
    "FW_div": '''\
-- [EMITTER] local generic FW_div applyNode lemma (goal-agnostic; mirrors Denote.lean _gNNN).
private theorem evalOp_fw_div_loc (numParts rank : Nat) (params : List Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_div" params [x] =
      [fw_div ((params.head?.getD 1 : Nat) : Scalar) x] := rfl
private theorem applyNode_fw_div_out_loc
    (g : GraphDecl) (s : Store) (rank : Nat) (params : List Nat) (inTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_div", ins := [inTid], outs := [outTid], params := params } outTid =
      fw_div ((params.head?.getD 1 : Nat) : Scalar) (s inTid) := by
  unfold applyNode
  rw [show ([inTid] : List Tid).map s = [s inTid] from rfl, evalOp_fw_div_loc]
  change storeSet s [(outTid, fw_div ((params.head?.getD 1 : Nat) : Scalar) (s inTid))] outTid = _
  unfold storeSet
  simp [List.find?]
''',
    "BW_softmax": '''\
-- [EMITTER] local generic BW_softmax applyNode lemma (goal-agnostic; mirrors Denote.lean _gNNN).
private theorem evalOp_bw_softmax_loc (numParts rank : Nat) (params : List Nat) (g y : Tensor) :
    evalOp numParts rank "OpName.BW_softmax" params [g, y] = [bw_softmax g y] := rfl
private theorem applyNode_bw_softmax_out_loc
    (gr : GraphDecl) (s : Store) (rank : Nat) (gTid yTid outTid : Tid) (params : List Nat) :
    applyNode gr s { rank := rank, op := "OpName.BW_softmax", ins := [gTid, yTid], outs := [outTid], params := params } outTid = bw_softmax (s gTid) (s yTid) := by
  unfold applyNode
  rw [show ([gTid, yTid] : List Tid).map s = [s gTid, s yTid] from rfl, evalOp_bw_softmax_loc]
  change storeSet s [(outTid, bw_softmax (s gTid) (s yTid))] outTid = _
  unfold storeSet
  simp [List.find?]
''',
    "BW_contiguous": '''\
-- [EMITTER] local generic BW_contiguous applyNode lemma (goal-agnostic; evalOp = [g]).
private theorem evalOp_bw_contiguous_loc (numParts rank : Nat) (params : List Nat) (g x : Tensor) :
    evalOp numParts rank "OpName.BW_contiguous" params [g, x] = [g] := rfl
private theorem applyNode_bw_contiguous_out_loc
    (gr : GraphDecl) (s : Store) (rank : Nat) (gTid xTid outTid : Tid) (params : List Nat) :
    applyNode gr s { rank := rank, op := "OpName.BW_contiguous", ins := [gTid, xTid], outs := [outTid], params := params } outTid = s gTid := by
  unfold applyNode
  rw [show ([gTid, xTid] : List Tid).map s = [s gTid, s xTid] from rfl, evalOp_bw_contiguous_loc]
  change storeSet s [(outTid, s gTid)] outTid = _
  unfold storeSet
  simp [List.find?]
''',
    "BW_div": '''\
-- [EMITTER] local generic BW_div applyNode lemma (goal-agnostic; mirrors Denote.lean _gNNN).
private theorem evalOp_bw_div_loc (numParts rank : Nat) (params : List Nat) (g x : Tensor) :
    evalOp numParts rank "OpName.BW_div" params [g, x] =
      [bw_div ((params.head?.getD 1 : Nat) : Scalar) g] := rfl
private theorem applyNode_bw_div_out_loc
    (gr : GraphDecl) (s : Store) (rank : Nat) (params : List Nat) (gTid xTid outTid : Tid) :
    applyNode gr s { rank := rank, op := "OpName.BW_div", ins := [gTid, xTid], outs := [outTid], params := params } outTid =
      bw_div ((params.head?.getD 1 : Nat) : Scalar) (s gTid) := by
  unfold applyNode
  rw [show ([gTid, xTid] : List Tid).map s = [s gTid, s xTid] from rfl, evalOp_bw_div_loc]
  change storeSet s [(outTid, bw_div ((params.head?.getD 1 : Nat) : Scalar) (s gTid))] outTid = _
  unfold storeSet
  simp [List.find?]
''',
}

# ---- Multi-output backward-pass ops --------------------------------------
# A BW op that produces a TUPLE of outputs (outs=[dx,dw(,db)]); a goal frames ONE
# of them. value = dict with:
#   fn        : denote function (returns a tuple)
#   nargs     : number of inputs the RHS reads (all ins; none dropped for these)
#   outs      : per-output (applyNode_lemma, rhs_projection, n_sidecond)
#               rhs_projection appended to `fn (s a) (s b) ...` e.g. ".1", ".2.1".
#               n_sidecond = number of `!=` hypotheses the lemma takes (filled `by decide`).
#   snd_loc   : optional flag whose 2nd-output lemma is gNNN-only -> emit `_loc`.
BW_MULTI = {
    "BW_linear": dict(fn="bw_linear", nargs=3, outs=[
        ("applyNode_bw_linear_fst_out", ".1", 1),
        ("applyNode_bw_linear_snd_out", ".2", 1),
    ]),
    "BW_matmul": dict(fn="bw_matmul", nargs=3, outs=[
        ("applyNode_bw_matmul_fst_out", ".1", 1),
        ("applyNode_bw_matmul_snd_out", ".2", 1),
    ]),
    "BW_add": dict(fn="bw_add2", nargs=3, outs=[
        ("applyNode_bw_add2_fst_out", ".1", 1),
        ("applyNode_bw_add2_snd_out_loc", ".2", 1),   # snd: gNNN-only -> local copy
    ], snd_loc=True),
    "BW_layernorm": dict(fn="bw_layernorm", nargs=4, outs=[
        ("applyNode_bw_layernorm_dx_out", ".1", 0),
        ("applyNode_bw_layernorm_dw_out", ".2.1", 1),
        ("applyNode_bw_layernorm_db_out", ".2.2", 2),
    ]),
}


def is_bw_multi(op):
    return op in BW_MULTI


# Private goal-agnostic copy of the BW_add second-output applyNode lemma. The
# inviolable Denote.lean only ships per-goal `_gNNN` suffixed copies
# (applyNode_bw_add2_snd_out_g110 etc.); the body is fully generic (universally
# quantified graph/store/rank/tids, uses the generic `evalOp_bw_add2` lemma), so
# we emit a private `_loc` rename — never touching Denote.lean. Mirrors the
# OP_LOCAL_LEMMA mechanism used for FW_div/FW_softmax.
BW_MULTI_LOCAL_LEMMA = {
    "BW_add": '''\
-- [EMITTER] local generic BW_add second-output (dy) applyNode lemma (goal-agnostic;
-- mirrors Denote.lean's applyNode_bw_add2_snd_out_gNNN, dropping the goal suffix).
private theorem applyNode_bw_add2_snd_out_loc
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]
''',
}


def _bw_meta(op, idx):
    """(applyNode_lemma, projection_str, n_sidecond) for output `idx` of a BW
    multi-output op."""
    return BW_MULTI[op]["outs"][idx]


def _bw_lout(node, bw_idx):
    """Logical output tid for a node under projection index `bw_idx`. For a BW
    multi-output node this is outs[bw_idx] (the framed projection); for any other
    node it is outs[0]."""
    if bw_idx is not None and node.op in BW_MULTI:
        return node.outs[bw_idx]
    return node.outs[0]


def _bw_apply(node, bw_idx):
    """The `applyNode_bw_..._out <args>` rewrite term for a BW multi node's framed
    output. Supplies graph/store as `_ _`, then rank + every in/out tid + the ≠
    side conditions as `(by decide)`."""
    lemma, _proj, nsc = _bw_meta(node.op, bw_idx)
    tids = " ".join(str(t) for t in (list(node.ins) + list(node.outs)))
    decides = "".join(" (by decide)" for _ in range(nsc))
    return f"{lemma} _ _ {node.rank} {tids}{decides}"


def _bw_expr(node, args, bw_idx):
    """Projected RHS expression `(bw_fn arg0 arg1 ...).<proj>` for a BW multi node."""
    fn = BW_MULTI[node.op]["fn"]
    _lemma, proj, _nsc = _bw_meta(node.op, bw_idx)
    inner = fn + " " + " ".join(_paren(a) for a in args)
    return f"({inner}){proj}"


def _bw_multi_local_used(ir, bw_idx):
    """Ordered list of BW multi op kinds in `ir` that require a private `_loc`
    applyNode lemma for the framed projection (currently only BW_add's 2nd out)."""
    if bw_idx is None:
        return []
    used = []
    for nd in (ir.sm_nodes + ir.pm_nodes):
        op = nd.op
        if op not in BW_MULTI or op not in BW_MULTI_LOCAL_LEMMA:
            continue
        lemma, _proj, _nsc = _bw_meta(op, bw_idx)
        if lemma.endswith("_loc") and op not in used:
            used.append(op)
    return used


def _emit_bw_multi_local_lemmas(ir, bw_idx):
    ops = _bw_multi_local_used(ir, bw_idx)
    if not ops:
        return ""
    return "".join(BW_MULTI_LOCAL_LEMMA[op] for op in ops) + "\n"


# collective op -> dict(fn, mini_lemma, full_lemma, kind)
#   kind 'list' : ins is a list of K tids;  render fn args per `form`
#   kind 'single': ins is a single tid (chunk)
COLLECTIVE = {
    "AllToAllPrim":  dict(fn="allToAllPrimWithDims", mini="applyNode_allToAllPrimWithDims_out",
                          full="applyNode_allToAllPrimWithDims_out", kind="list",
                          form="K rank LIST p0 p1", nparams=2),
    "AllGatherPrim": dict(fn="allGatherPrimDimN", mini="applyNode_allGatherPrimDimN_out",
                          full="applyNode_allGatherPrimDimN_out_thm", kind="list",
                          form="p0 K rank LIST", nparams=1),
    "AllReducePrim": dict(fn="allReducePrim", mini="applyNode_allReducePrim_out",
                          full="applyNode_allReducePrim_out", kind="list",
                          form="K rank LIST", nparams=0),
    "ChunkPrim":     dict(fn="chunkPrimDimN", mini="applyNode_chunkPrimDimN_out",
                          full="applyNode_chunkPrimDimN_out", kind="single",
                          form="p0 K rank ARG", nparams=1),
    # CROSS_DP_WRED: cross data-parallel weight reduction (tensorSum over per-rank
    # weight-gradients). Singleton output that is IN-PLACE (out tid == first in tid).
    # RHS = cross_dp_wred (ins.map s); no numRanks/rank/dim params in the call.
    "CROSS_DP_WRED": dict(fn="cross_dp_wred", mini="applyNode_cross_dp_wred_out",
                          full="applyNode_cross_dp_wred_out", kind="list",
                          form="LIST", nparams=0),
}

# Ops we cannot render generically (only suffixed local lemmas exist).
# FW_multiref stays here (handled by dedicated A2/A3/B/C family renderers BEFORE the
# _check_supported gate). FW_div/FW_softmax/FW_contiguous moved INTO the POINTWISE
# table (Family D) — they render via local `_loc` lemmas emitted per-bridge.
SKIP_OPS = {"FW_multiref"}

# Family D pointwise op kinds (need local lemmas emitted + possible post-normalize).
FAMILY_D_OPS = set(OP_LOCAL.keys())


class UnsupportedTopology(Exception):
    pass


@dataclass
class PMNode:
    rank: int
    op: str
    ins: list
    outs: list
    params: list
    node_idx: int = -1
    is_final: bool = False
    bw_idx: int = None    # for multi-output BW nodes: framed output position in `outs`


def is_collective(op): return op in COLLECTIVE
def is_pointwise(op):   return op in POINTWISE


def _rhs_ins(node):
    """Inputs that actually appear in the op's RHS expression (and therefore need a
    prefix_eq / applyNode_skip rewrite). For most ops this is every input; for
    backward ops whose RHS reads only the gradient, the carried original input(s) are
    dropped. bw_sum/bw_gelu/bw_softmax read BOTH grad and the original, so keep two."""
    op = node.op
    if op in BW_MULTI:
        return list(node.ins)                 # multi-out BW RHS reads every input
    if op.startswith("BW_"):
        if op in ("BW_sum", "BW_gelu", "BW_softmax"):
            return node.ins[:2]
        if op == "BW_multiref":
            return list(node.ins)            # tensorSum over all inputs
        if op == "BW_embedding":
            return list(node.ins)            # bw_embedding reads g, ids, w (all three)
        return node.ins[:1]                   # grad only (view/transpose/div/contiguous)
    return list(node.ins)


def _op_post(op):
    """Post-`rw [helper]` normalization tactic for a pointwise op (e.g. fw_div needs
    `norm_num` to reduce `((params.head?.getD 1 : Nat) : Scalar)`). Empty for ops that
    need none. Returns a string ending in newline, or ''."""
    return OP_LOCAL.get(op, {}).get("post", "")


def _after_apply_simp(op):
    """Normalization that must run IMMEDIATELY after `rw [applyNode_..._out]`, BEFORE
    any `*_prefix_eq` / `applyNode_skip` rewrites of the inner input tids. BW_multiref's
    lemma yields `tensorSum (ins.map s)` = `tensorSum (List.map s [a, b, ...])`; the
    inner-tid rewrites need the `denoteGraph .. a` / `s a` subterms EXPOSED (un-wrapped
    from List.map) to fire, so we reduce List.map here first. Ends in newline, or ''."""
    if op == "BW_multiref":
        return "  simp only [List.map]\n"
    return ""


def _family_d_ops_used(ir):
    """Ordered list of Family-D op kinds appearing in this goal (sm + pm), for which
    we must emit a private local `_loc` lemma. Dedupe, stable order."""
    used = []
    for nd in (ir.sm_nodes + ir.pm_nodes):
        if nd.op in FAMILY_D_OPS and nd.op not in used:
            used.append(nd.op)
    return used


def _emit_local_lemmas(ir):
    """Concatenated private local lemma text for every Family-D op used in `ir`."""
    ops = _family_d_ops_used(ir)
    if not ops:
        return ""
    return "".join(OP_LOCAL_LEMMA[op] for op in ops) + "\n"


def _check_supported(ir):
    for nd in ir.sm_nodes + ir.pm_nodes:
        if nd.op in SKIP_OPS:
            raise UnsupportedTopology(f"op {nd.op} requires suffixed/local lemma")
        if not (is_collective(nd.op) or is_pointwise(nd.op) or is_bw_multi(nd.op)):
            raise UnsupportedTopology(f"unknown op {nd.op}")


# ---------------- expression builders ----------------
def _paren(a):
    return f"({a})"


def _collective_expr(op, rank, params, args, K):
    """Render a collective call. args: list of bare arg-strings.
    K: literal int (mini) or string 'pm.numRanks' (full)."""
    meta = COLLECTIVE[op]
    fn = meta["fn"]
    if meta["kind"] == "single":
        # chunkPrimDimN dim K rank (ARG)   (single arg, parenthesized)
        return f"{fn} {params[0]} {K} {rank} {_paren(args[0])}"
    lst = "[" + ", ".join(args) + "]"     # list elements bare (incl nested exprs)
    form = meta["form"]
    if form == "K rank LIST p0 p1":
        return f"{fn} {K} {rank} {lst} {params[0]} {params[1]}"
    if form == "p0 K rank LIST":
        return f"{fn} {params[0]} {K} {rank} {lst}"
    if form == "K rank LIST":
        return f"{fn} {K} {rank} {lst}"
    if form == "LIST":
        return f"{fn} {lst}"
    raise UnsupportedTopology(f"collective form {form}")


def _pointwise_expr(op, params, args):
    """args: bare arg-strings; each function argument gets parenthesized."""
    fn, _, _, has_params, pbefore = POINTWISE[op]
    # ---- Backward-pass ops: RHS depends on the gradient (ins[0]) only -------
    # `args` carries every node input (grad + carried originals); BW RHS uses just
    # the grad. bw_sum/bw_gelu/bw_softmax are the exception: their semantics use
    # BOTH the grad and the original input, so they keep two args.
    if op.startswith("BW_"):
        g = _paren(args[0])
        if op == "BW_contiguous":
            return g                                   # evalOp = [g]; RHS is the grad itself
        if op == "BW_view":
            pstr = "[" + ", ".join(str(p) for p in params) + "]"
            return f"fw_view {pstr} {g}"
        if op == "BW_transpose":
            return f"transposeAxes {params[0]} {params[1]} {g}"
        if op == "BW_div":
            c = (params[0] if params else 1)
            return f"bw_div (({c} : Nat) : Scalar) {g}"
        if op == "BW_multiref":
            # tensorSum over ALL inputs (ins.map acc). args already = every input.
            return "tensorSum [" + ", ".join(args) + "]"
        if op == "BW_embedding":
            # bw_embedding (g) (ids) (w)  [plain]  OR  bw_embedding_offset off (g) (ids) (w)
            # ins order = [gTid, idsTid, wTid]; params=[offset] => vocab-parallel variant.
            if params:
                return f"bw_embedding_offset {params[0]} " + " ".join(_paren(a) for a in args[:3])
            return "bw_embedding " + " ".join(_paren(a) for a in args[:3])
        if op in ("BW_sum", "BW_gelu", "BW_softmax"):
            return f"{fn} {g} {_paren(args[1])}"
        # default single-grad form
        return f"{fn} {g}"
    if op == "FW_div":
        # fw_div ((c : Nat) : Scalar) (x): scalar c = params.head?.getD 1, rendered as a
        # literal so the RHS matches the post-`norm_num`-reduced applyNode lemma output.
        c = (params[0] if params else 1)
        return f"{fn} (({c} : Nat) : Scalar) {_paren(args[0])}"
    if has_params and pbefore:
        if op == "FW_view":
            pstr = "[" + ", ".join(str(p) for p in params) + "]"
            return f"{fn} {pstr} {_paren(args[0])}"
        if op == "FW_transpose":
            return f"{fn} {params[0]} {params[1]} {_paren(args[0])}"
    return fn + " " + " ".join(_paren(a) for a in args)


def node_expr(node, acc, inline_map, K, bw_idx=None):
    """Fully-nested expression for `node`'s output. inline_map: tid -> PMNode.
    Returns the bare expression (no outer parens)."""
    def arg(tid):
        if tid in inline_map:
            return node_expr(inline_map[tid], acc, inline_map, K, bw_idx)
        return f"{acc} {tid}"
    args = [arg(t) for t in node.ins]
    if is_collective(node.op):
        return _collective_expr(node.op, node.rank, node.params or [], args, K)
    if node.op in BW_MULTI:
        return _bw_expr(node, args, bw_idx)
    return _pointwise_expr(node.op, node.params or [], args)


# ---------------- node literal (for `show pm.nodes[idx] = {...}`) ----------------
def _node_literal(node, out, explicit_ins=False):
    rank, op = node.rank, node.op
    # Multi-output nodes (BW_linear/matmul/add/layernorm) must carry their FULL
    # outs list — the applyNode lemma's node literal pattern requires it.
    outs_list = node.outs if (op in BW_MULTI or len(node.outs) > 1) else [out]
    if is_collective(op) and COLLECTIVE[op]["kind"] == "list" and not explicit_ins:
        base = node.ins[0]
        K = len(node.ins)
        # The compact `(List.range K).map (fun r => base + r)` form is ONLY valid when
        # the collective's ins are contiguous (base, base+1, ..., base+K-1). Some
        # collectives gather a STRIDED projection (e.g. goal_247's AllGather over
        # [3277, 3279, 3281, 3283], stride 2) — then the range form denotes the WRONG
        # node literal and `native_decide` rejects it. Fall back to the explicit list
        # whenever the ins are not perfectly contiguous.
        if node.ins == list(range(base, base + K)):
            ins_s = f"((List.range {K}).map (fun r => {base} + r))"
        else:
            ins_s = "[" + ", ".join(str(x) for x in node.ins) + "]"
    else:
        # explicit list form — required when collective ins are non-contiguous (e.g.
        # a collective gathering a strided BW projection like [3161, 3163, 3165, 3167]).
        ins_s = "[" + ", ".join(str(x) for x in node.ins) + "]"
    outs_s = "[" + ", ".join(str(x) for x in outs_list) + "]"
    parts = [f"rank := {rank}", f'op := "OpName.{op}"', f"ins := {ins_s}", f"outs := {outs_s}"]
    if node.params:
        parts.append("params := [" + ", ".join(str(p) for p in node.params) + "]")
    return "{ " + ", ".join(parts) + " }"


def _is_range_collective(node):
    return is_collective(node.op) and COLLECTIVE[node.op]["kind"] == "list"


# ---------------- segment renderers ----------------
def denote_sm_block(n, sm_node, bw_idx=None):
    smn = PMNode(sm_node.rank, sm_node.op, sm_node.ins, sm_node.outs, sm_node.params)
    is_bw = bw_idx is not None and sm_node.op in BW_MULTI
    out = _bw_lout(smn, bw_idx) if is_bw else sm_node.outs[0]
    rhs = node_expr(smn, "s", {}, 4, bw_idx)
    if is_bw:
        apply = _bw_apply(smn, bw_idx)
        post = ""
    else:
        apply = _pointwise_lemma_name(sm_node)
        post = _op_post(sm_node.op)
    return (
f"""-- ========== mini sm_goal_{n} computes {out} ({sm_node.op}) ==========
theorem denote_sm_goal_{n}_{out} (s : Store) :
    denoteGraph sm_goal_{n} s {out} = {rhs} := by
  simp only [sm_goal_{n}, denoteGraph, List.foldl]
  rw [{apply}]
{_after_apply_simp(sm_node.op)}{post}
""")


def sm_frame_block(n, sm_node, idx, bw_idx=None):
    smn = PMNode(sm_node.rank, sm_node.op, sm_node.ins, sm_node.outs, sm_node.params)
    is_bw = bw_idx is not None and sm_node.op in BW_MULTI
    out = _bw_lout(smn, bw_idx) if is_bw else sm_node.outs[0]
    if is_bw:
        apply = _bw_apply(smn, bw_idx)
        post = ""
    else:
        apply = _pointwise_lemma_name(sm_node)
        post = _op_post(sm_node.op)
    lit = _node_literal(smn, out)
    prefix = ",\n      ".join(
        f"sm_prefix_eq initSM {idx} {t} (by native_decide)" for t in _rhs_ins(smn))
    return (
f"""-- ========== SM self-frame ==========
theorem sm_frame_{out}_self (initSM : Store) :
    denoteGraph sm initSM {out} = denoteGraph sm_goal_{n} (denoteGraph sm initSM) {out} := by
  rw [denote_sm_goal_{n}_{out}]
  rw [sm_val initSM {idx} {out} (by native_decide) (by native_decide)]
  rw [show sm.nodes[{idx}]'(by native_decide)
      = {lit}
      from by native_decide]
  rw [{apply}]
{_after_apply_simp(sm_node.op)}  rw [{prefix}]
{post}
""")


def _pmfull_name(out, n, bw_idx):
    """pm_full helper theorem name. ALWAYS goal-prefixed (`pm_full_g<n>_<tid>`).
    These are module-local helper lemmas, only referenced inside their own bridge.
    Two different goals can frame the SAME pm tid (e.g. goal_102 and goal_247 both
    touch tid 3261) and BOTH emit a `pm_full_<tid>` lemma in the shared namespace
    `TrainVerify.Denote.GeneratedGoals`. When a downstream bridge imports an upstream
    one whose tid overlaps, the un-prefixed names collide -> `already declared`. Goal
    prefixing makes every bridge's helpers unique. (Previously only BW-multi chunked
    inputs were prefixed; the forward/mid overlap was latent until ordered builds
    started importing every prereq bridge.)"""
    return f"pm_full_g{n}_{out}"


def pm_full_block(node, bw_idx=None, n=None):
    """One pm_full_<out> theorem for a MID node (one level, immediate ins)."""
    is_bw = bw_idx is not None and node.op in BW_MULTI
    out = _bw_lout(node, bw_idx) if is_bw else node.outs[0]
    name = _pmfull_name(out, n, bw_idx)
    acc = "denoteGraph pm initPM"
    idx = node.node_idx
    explicit = bw_idx is not None
    lit = _node_literal(node, out, explicit_ins=explicit)
    args = [f"{acc} {t}" for t in node.ins]
    if is_collective(node.op):
        meta = COLLECTIVE[node.op]
        rhs = _collective_expr(node.op, node.rank, node.params or [], args, "pm.numRanks")
        lemma = meta["full"]
        if meta["kind"] != "list":
            range_simp = ""
        elif explicit:
            range_simp = "\n  simp only [List.map]"
        else:
            range_simp = "\n  simp only [List.range, List.range.loop, List.map]"
        post = ""
    elif is_bw:
        rhs = _bw_expr(node, args, bw_idx)
        lemma = _bw_apply(node, bw_idx)
        range_simp = ""
        post = ""
    else:
        rhs = _pointwise_expr(node.op, node.params or [], args)
        lemma = _pointwise_lemma_name(node)
        # BW_multiref's lemma yields `tensorSum (ins.map (denoteGraph ..))`; the
        # following `pm_prefix_eq` rewrites need the `denoteGraph .. tid` subterms
        # exposed, so reduce List.map right after the lemma (before prefix).
        range_simp = "\n  simp only [List.map]" if node.op == "BW_multiref" else ""
        post = _op_post(node.op)
    prefix = ",\n      ".join(
        f"pm_prefix_eq initPM {idx} {t} (by native_decide)" for t in _rhs_ins(node))
    return (
f"""theorem {name} (initPM : Store) :
    denoteGraph pm initPM {out}
      = {rhs} := by
  rw [pm_val initPM {idx} {out} (by native_decide) (by native_decide)]
  rw [show pm.nodes[{idx}]'(by native_decide)
      = {lit}
      from by native_decide]
  rw [{lemma}]{range_simp}
  rw [{prefix}]
{post}
""")


def denote_pm_block(n, node, inline_map, bw_idx=None):
    """denote_pm_goal_N_<final> : mini graph computes final = fully-nested expr (literal K=4, s)."""
    is_bw = bw_idx is not None and node.op in BW_MULTI
    out = _bw_lout(node, bw_idx) if is_bw else node.outs[0]
    rhs = node_expr(node, "s", inline_map, 4, bw_idx)
    has_mid = any(t in inline_map for t in node.ins)
    if is_collective(node.op):
        meta = COLLECTIVE[node.op]
        lemma = meta["mini"]
        # Match the (fast) handwritten pattern: the mini-graph foldl resolves the
        # collective output directly. Avoid `repeat rw [applyNode_eq_of_not_mem_outs
        # (h := by decide)]` here — over a K=4 collective mini-graph the repeated
        # metavariable `by decide` non-membership search is pathologically slow
        # (minutes vs seconds). A heartbeat-bumped `congr 1` closes the goal.
        tac = (f"  simp only [pm_goal_{n}, denoteGraph, List.foldl]\n"
               f"  repeat rw [applyNode_skip _ _ _ {out} (by decide)]\n"
               f"  rw [{lemma}]\n")
        if meta["kind"] == "list":
            tac += "  simp only [List.map]\n"
        tac += "  try (set_option maxHeartbeats 800000 in congr 1)\n"
    else:
        if is_bw:
            apply = _bw_apply(node, bw_idx)
        else:
            apply = _pointwise_lemma_name(node)
        if not has_mid:
            # Fast path (leaf inputs only): explicit-tid skips avoid pathological
            # metavariable `by decide` search (e.g. replicated finals like g9).
            ins_seen = []
            for t in _rhs_ins(node):
                if t not in ins_seen:
                    ins_seen.append(t)
            tac = (f"  simp only [pm_goal_{n}, denoteGraph, List.foldl]\n"
                   f"  repeat rw [applyNode_skip _ _ _ {out} (by decide)]\n"
                   f"  rw [{apply}]\n")
            tac += _after_apply_simp(node.op)
            for t in ins_seen:
                tac += f"  repeat rw [applyNode_skip _ _ _ {t} (by decide)]\n"
            tac += ("" if is_bw else _op_post(node.op))
        else:
            tac = (f"  simp only [pm_goal_{n}, denoteGraph, List.foldl]\n"
                   f"  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]\n"
                   f"  rw [{apply}]\n"
                   f"  try congr 1\n"
                   f"  try (repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)])\n")
    return (
f"""theorem denote_pm_goal_{n}_{out} (s : Store) :
    denoteGraph pm_goal_{n} s {out} = {rhs} := by
{tac}
""")


def pm_frame_block(node, inline_map, mid_rw_order, any_collective, bw_idx=None, n=None,
                   inplace_info=None):
    """pm_frame_<final>_self : full pm computes final = nested expr (denoteGraph accessor)."""
    is_bw = bw_idx is not None and node.op in BW_MULTI
    out = _bw_lout(node, bw_idx) if is_bw else node.outs[0]
    # In-place collective shared input: handled by the dedicated `pm_inplace` lemma,
    # NOT by `pm_prefix_eq` (the collective node itself writes that tid, so the suffix
    # is not write-free and pm_prefix_eq's side condition is false).
    ip = inplace_info[0] if (inplace_info is not None and is_collective(node.op)
                             and out == node.outs[0]) else None
    acc = "denoteGraph pm initPM"
    rhs = node_expr(node, acc, inline_map, 4, bw_idx)
    idx = node.node_idx
    explicit = bw_idx is not None
    lit = _node_literal(node, out, explicit_ins=explicit)
    lines = [
        f"theorem pm_frame_{out}_self (initPM : Store) :",
        f"    denoteGraph pm initPM {out}",
        f"      = {rhs} := by",
        f"  rw [pm_val initPM {idx} {out} (by native_decide) (by native_decide)]",
        f"  rw [show pm.nodes[{idx}]'(by native_decide)",
        f"      = {lit}",
        f"      from by native_decide]",
    ]
    if is_collective(node.op):
        meta = COLLECTIVE[node.op]
        lines.append(f"  rw [{meta['full']}]")
        if meta["kind"] == "list":
            if explicit:
                lines.append("  simp only [List.map]")
            else:
                lines.append("  simp only [List.range, List.range.loop, List.map]")
        post = ""
    elif is_bw:
        lines.append(f"  rw [{_bw_apply(node, bw_idx)}]")
        post = ""
    else:
        helper = _pointwise_lemma_name(node)
        lines.append(f"  rw [{helper}]")
        # BW_multiref's lemma yields `tensorSum (ins.map (denoteGraph pm initPM))`; the
        # following `pm_prefix_eq` rewrites need the `denoteGraph pm initPM tid`
        # subterms exposed, so reduce List.map right after the lemma (before prefix).
        if node.op == "BW_multiref":
            lines.append("  simp only [List.map]")
        post = _op_post(node.op)
    if ip is not None:
        lines.append(f"  rw [pm_inplace_g{n}_{ip}]")
    prefix = ",\n      ".join(
        f"pm_prefix_eq initPM {idx} {t} (by native_decide)"
        for t in _rhs_ins(node) if t != ip)
    if prefix:
        lines.append(f"  rw [{prefix}]")
    if mid_rw_order:
        rws = ", ".join(_pmfull_name(m, n, bw_idx) for m in mid_rw_order)
        lines.append(f"  rw [{rws}]")
    # The `pm.numRanks = 4` normalisation is only needed when a collective whose RHS
    # actually mentions `pm.numRanks` was introduced (every collective except the
    # param-free CROSS_DP_WRED). Either the framing node itself, or one of the mids
    # rewritten in via `pm_full`, can be such a collective.
    def _bears_numranks(op):
        return is_collective(op) and op != "CROSS_DP_WRED"
    needs_numranks = _bears_numranks(node.op) or any(
        m in inline_map and _bears_numranks(inline_map[m].op) for m in mid_rw_order)
    if needs_numranks:
        lines.append("  rw [show pm.numRanks = 4 from by native_decide]")
    # Pointwise-op post-normalize (e.g. fw_div scalar param) goes LAST, after the mid
    # rewrites have exposed the final `fw_div ((params.head?.getD 1)) ...` shape.
    if post:
        lines.append(post.rstrip("\n"))
    return "\n".join(lines) + "\n\n"


# ---------------- in-place collective (CROSS_DP_WRED) ----------------
def _find_inplace_collective(ir, bw_idx):
    """Detect an IN-PLACE collective: a collective node whose single output tid also
    appears among its inputs (e.g. CROSS_DP_WRED, where the reduction overwrites the
    rank-0 per-rank producer's tensor in place). Returns (cn, p0, ip) with cn = the
    collective PMNode, p0 = the per-rank producer PMNode whose framed output is the
    shared tid, ip = that shared tid; or None when there is no in-place collective."""
    for cn in ir.pm_nodes:
        if not is_collective(cn.op):
            continue
        ip = cn.outs[0]
        if ip not in cn.ins:
            continue
        for p0 in ir.pm_nodes:
            if p0 is cn:
                continue
            if _bw_lout(p0, bw_idx) == ip:
                return cn, p0, ip
    return None


def _pointwise_lemma_name(node):
    """Just the applyNode lemma NAME for a POINTWISE node (offset-aware for BW_embedding).
    Used at `rw [<name>]` sites in denote_pm_block where the lemma is applied by
    unification (no explicit tids)."""
    _, lemma, *_ = POINTWISE[node.op]
    if node.op == "BW_embedding" and node.params:
        return "applyNode_bw_embedding_offset_out"
    return lemma


def _pointwise_apply(node):
    """The `applyNode_..._out _ _ rank <ins> <out>` rewrite term for a single-output
    POINTWISE node. Picks the offset variant lemma for BW_embedding when params present."""
    _, lemma, *_ = POINTWISE[node.op]
    if node.op == "BW_embedding" and node.params:
        lemma = "applyNode_bw_embedding_offset_out"
        tids = " ".join(str(t) for t in (list(node.ins) + list(node.outs)))
        return f"{lemma} _ _ {node.rank} {node.params[0]} {tids}"
    tids = " ".join(str(t) for t in (list(node.ins) + list(node.outs)))
    return f"{lemma} _ _ {node.rank} {tids}"


def _emit_inplace_lemma(n, p0, ip, kp, kc, bw_idx):
    """Prefix-value lemma for an in-place collective's shared input. The collective at
    node index `kc` overwrites tid `ip` (produced by per-rank node `p0` at index `kp`,
    kp < kc) in place, so `pm_prefix_eq` cannot be used for `ip` at `kc` (the suffix DOES
    write it). This lemma instead computes the value of `ip` in the *prefix* graph
    `{pm with nodes := pm.nodes.take kc}` (where the only writer of `ip` is `p0`), peeling
    the nodes between `p0` and the collective, then evaluating `p0` directly."""
    acc = "denoteGraph pm initPM"
    args = [f"{acc} {t}" for t in p0.ins]
    if p0.op in BW_MULTI:
        rhs = _bw_expr(p0, args, bw_idx)
        apply = _bw_apply(p0, bw_idx)
    else:
        # pointwise per-rank producer (e.g. BW_embedding / FW_sum under CROSS_DP_WRED)
        rhs = _pointwise_expr(p0.op, p0.params or [], args)
        apply = _pointwise_apply(p0)
    lit = _node_literal(p0, ip, explicit_ins=True)
    prefix = ",\n      ".join(
        f"pm_prefix_eq initPM {kp} {t} (by native_decide)" for t in _rhs_ins(p0))
    return (
f"""theorem pm_inplace_g{n}_{ip} (initPM : Store) :
    denoteGraph {{pm with nodes := pm.nodes.take {kc}}} initPM {ip}
      = {rhs} := by
  rw [denoteGraph_tid_eq_of_suffix_no_writes
        {{pm with nodes := pm.nodes.take {kc}}} initPM {ip}
        (pm.nodes.take {kp + 1}) ((pm.nodes.take {kc}).drop {kp + 1})
        (by native_decide) (by native_decide)]
  show denoteGraph {{pm with nodes := pm.nodes.take {kp + 1}}} initPM {ip} = _
  rw [pm_step initPM {kp} (by native_decide)]
  rw [show pm.nodes[{kp}]'(by native_decide)
      = {lit}
      from by native_decide]
  rw [{apply}]
  rw [{prefix}]

""")


# ---------------- top-level ----------------
def render_universal(n, ir, topo, probe_map, input_sources, prereqs, imports):
    # Family A2 dispatch: multiref-2-output second-out (no collective). Must run
    # BEFORE _check_supported (which rejects FW_multiref via SKIP_OPS). This family
    # has its own renderer + a private local lemma, so the SKIP_OPS guard is moot.
    if is_multiref2_second(ir, topo):
        return render_multiref2_second(n, ir, topo, probe_map, input_sources,
                                       prereqs, imports)
    # Family A3 dispatch: multiref-N-output i-th-out (no collective). Generalizes A2
    # to any output count / any output index. Same gate placement rationale as A2.
    if is_multirefN_nth(ir, topo):
        return render_multirefN_nth(n, ir, topo, probe_map, input_sources,
                                    prereqs, imports)
    # Family B dispatch: multiref-first-out MIDs feeding collective finals (AllToAll/
    # AllGather/...). Runs BEFORE _check_supported (which rejects FW_multiref).
    if is_multiref_first_collective(ir, topo):
        return render_multiref_first_collective(n, ir, topo, probe_map, input_sources,
                                                prereqs, imports)
    _check_supported(ir)
    sm_node = ir.sm_nodes[0]
    # Multi-output backward ops: the goal frames ONE projection of the op's output
    # tuple. `bw_idx` = position of lineage.ts among the SM node's outs; the SAME
    # projection index applies to every per-rank PM BW node (the other outputs are
    # dead). For non-BW goals bw_idx stays None and behaviour is unchanged.
    bw_idx = (sm_node.outs.index(ir.lineage.ts)
              if is_bw_multi(sm_node.op) and ir.lineage.ts in sm_node.outs else None)
    if sm_node.op not in POINTWISE and not is_bw_multi(sm_node.op):
        raise UnsupportedTopology(f"sm op {sm_node.op} not pointwise/bw-multi")
    smn0 = PMNode(sm_node.rank, sm_node.op, sm_node.ins, sm_node.outs, sm_node.params or [])
    sm_out = _bw_lout(smn0, bw_idx) if bw_idx is not None else sm_node.outs[0]

    final_set = set(topo.final_tps)
    mid_set = set(topo.mid_tids)

    def lout(nd):
        return _bw_lout(nd, bw_idx)

    # build PMNode list with probe indices (keyed by each node's framed output)
    pm_nodes = []
    for nd in ir.pm_nodes:
        pn = PMNode(nd.rank, nd.op, nd.ins, nd.outs, nd.params or [])
        out = lout(pn)
        pi = probe_map["pm"].get(out, {})
        pn.node_idx = pi.get("node_idx", -1)
        pn.is_final = (out in final_set)
        pm_nodes.append(pn)
    by_out = {lout(nd): nd for nd in pm_nodes}

    # inline_map for fully-nested final expressions: all mids
    inline_map = {lout(nd): nd for nd in pm_nodes if lout(nd) in mid_set}

    # mids in mini-graph creation order
    mid_nodes_in_order = [nd for nd in pm_nodes if lout(nd) in mid_set]

    any_collective = any(is_collective(nd.op) for nd in pm_nodes)

    # ----- in-place collective (CROSS_DP_WRED) detection -----
    # An in-place collective overwrites a per-rank producer's framed output `ip` in
    # place. That producer's node is NOT a mid (its output tid is the goal's final tp,
    # shared with the collective), so it is absent from `inline_map`/`mid_nodes_in_order`.
    # Register it in inline_map under `ip` so the collective's nested RHS inlines the
    # rank-0 producer expression (instead of a bare store lookup), and remember the
    # (producer-idx, collective-idx) pair for the prefix-value lemma + pm_frame.
    inplace = _find_inplace_collective(ir, bw_idx)
    inplace_info = None
    if inplace is not None:
        cn, p0, ip = inplace
        # `ip` is written TWICE (in-place): once by the per-rank producer `p0` and once
        # by the collective `cn`. probe_map[...][ip] keeps only the max-index writer
        # (the collective). Recover both from the `writers` list: the collective is the
        # max-index writer; the producer `kp` is the writer whose op == p0.op (and which
        # is NOT the collective node).
        pm_ip = probe_map["pm"].get(ip, {})
        kc = pm_ip.get("node_idx", -1)
        writers = pm_ip.get("writers", [])
        kp = -1
        for w in writers:
            wop = w["op"].split(".")[-1] if w["op"] else ""
            if w["node_idx"] != kc and wop == p0.op:
                kp = w["node_idx"]; break
        if kp == -1:
            # fallback: largest writer index strictly below the collective
            below = [w["node_idx"] for w in writers if w["node_idx"] < kc]
            kp = max(below) if below else probe_map["pm"].get(p0.outs[0], {}).get("node_idx", -1)
        pn_p0 = PMNode(p0.rank, p0.op, p0.ins, p0.outs, p0.params or [])
        pn_p0.node_idx = kp
        inline_map[ip] = pn_p0
        inplace_info = (ip, kp, kc, pn_p0)

    # ----- header -----
    header_inputs = ", ".join(f"{s.tid}<-{s.kind}:{s.upstream}" for s in input_sources)
    text = R.HEADER.format(
        n=n, sm_op=sm_node.op, sm_ins=sm_node.ins, sm_out=sm_out,
        pm_outs=topo.final_tps, gather_dim=ir.lineage.gatherDim, prereqs=prereqs,
        pn=len(prereqs), input_sources=header_inputs,
        imports="\n".join(f"import {m}" for m in imports),
    )
    # ----- Family-D local lemmas (private goal-agnostic copies of Denote.lean's
    #       per-goal `_gNNN` pointwise lemmas; emitted iff such an op is used) -----
    text += _emit_local_lemmas(ir)
    # ----- BW multi local lemmas (e.g. BW_add 2nd-output `_loc`) -----
    text += _emit_bw_multi_local_lemmas(ir, bw_idx)
    # ----- A: denote_sm -----
    text += denote_sm_block(n, sm_node, bw_idx)
    # ----- B: sm_frame -----
    sm_idx = probe_map["sm"][sm_out]["node_idx"]
    text += sm_frame_block(n, sm_node, sm_idx, bw_idx)
    # ----- C: pm_full for each mid -----
    if mid_nodes_in_order:
        text += f"-- ========== pm_full (mid tensors) ==========\n"
        for nd in mid_nodes_in_order:
            text += pm_full_block(nd, bw_idx, n)
    # ----- C': in-place collective prefix-value lemma -----
    if inplace_info is not None:
        ip, kp, kc, pn_p0 = inplace_info
        text += f"-- ========== pm_inplace (in-place collective producer) ==========\n"
        text += _emit_inplace_lemma(n, pn_p0, ip, kp, kc, bw_idx)
    # ----- D: denote_pm for each final -----
    text += f"-- ========== denote_pm (final tps {topo.final_tps}) ==========\n"
    for tp in topo.final_tps:
        text += denote_pm_block(n, by_out[tp], inline_map, bw_idx)
    # ----- E: pm_frame for each final -----
    text += f"-- ========== pm_frame (final tps) ==========\n"
    for tp in topo.final_tps:
        fnode = by_out[tp]
        # mids reachable from this final, reverse-topo (closest first = reverse creation order)
        reach = _reachable_mids(fnode, by_out, mid_set)
        # IN-PLACE FIX: when the collective producer for rank-0 is in-place (its out tid
        # == the collective node's first in / shared tid `ip`), _reachable_mids self-loops
        # on `ip` via by_out[ip]==fnode and never descends into the rank-0 producer pn_p0.
        # That drops pn_p0's own mid inputs (e.g. the rank-0 chunk tid) from the rw list,
        # leaving them unresolved. Seed the traversal from pn_p0 explicitly to recover them.
        if inplace_info is not None and inplace_info[3] is not None:
            reach |= _reachable_mids(inplace_info[3], by_out, mid_set)
            if lout(inplace_info[3]) in mid_set:
                reach.add(lout(inplace_info[3]))
        mid_rw = [m for m in reversed([lout(nd) for nd in mid_nodes_in_order]) if m in reach]
        text += pm_frame_block(fnode, inline_map, mid_rw, any_collective, bw_idx, n,
                               inplace_info)
    # ----- F: hInitCut helper -----
    text += R.hinitcut_helper(n, prereqs)
    # ----- G+H: assembly -----
    text += R.cut_to_full_block(n, sm_out, topo.final_tps, prereqs, input_sources,
                                ir.sm_shapes, ir.pm_shapes)
    return text


# ============================================================================
# Family A2: FW_multiref (2 outputs, params=[2]), SM/PM finals = SECOND output,
# no collective. The second output of a 2-way multiref equals the input directly.
# PM finals are per-rank second outputs (= per-rank inputs); SM final = 2nd output.
# Validated vs handwritten Goal259/269/273 (g259 local-lemma spike: RC=0, 56s,
# 0 sorryAx). We emit a PRIVATE local copy of the goal-agnostic lemma so we never
# touch the inviolable Denote.lean (which holds per-goal `_gNNN` suffixed copies).
# ============================================================================

MULTIREF2_SECOND_LOCAL = '''\
-- [EMITTER] local generic multiref-2-output second-out lemma (goal-agnostic).
private theorem applyNode_fw_multiref2_second_out_loc
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 : Tid) (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := [t1, t2], params := [2] } t2 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2].zip (List.replicate 2 (s xTid))) t2 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]
'''


def _multiref2_second_skips(pm_finals_nodes, target_final):
    """rw list to evaluate denoteGraph for `target_final` (= second output t2 of one
    multiref node) over a K-node multiref mini-graph.

    The foldl nests as applyNode_{K-1} (... (applyNode_0 s)); `rw` peels from the
    OUTERMOST node (K-1) inward. So the order is:
      - nodes ABOVE the target (index > tgt_idx), outer-first: skip on target_final
        (they don't write it) — count = (K-1 - tgt_idx)
      - AT the target node: apply the second-out lemma
      - nodes BELOW the target (index < tgt_idx): skip on xTid (the expr is now `s xTid`)
        — count = tgt_idx
    This matches the handwritten Goal259 ordering exactly."""
    K = len(pm_finals_nodes)
    tgt_idx = next(i for i, nd in enumerate(pm_finals_nodes) if nd.outs[1] == target_final)
    tgt = pm_finals_nodes[tgt_idx]
    xTid = tgt.ins[0]
    rws = []
    # outer nodes (above target): skip on target final tid
    for _ in range(K - 1 - tgt_idx):
        rws.append(f"applyNode_skip _ _ _ {target_final} (by decide)")
    # target node: apply lemma
    rws.append(
        f"applyNode_fw_multiref2_second_out_loc _ _ {tgt.rank} "
        f"{xTid} {tgt.outs[0]} {tgt.outs[1]} (by decide)")
    # inner nodes (below target): skip on input tid
    for _ in range(tgt_idx):
        rws.append(f"applyNode_skip _ _ _ {xTid} (by decide)")
    return rws


def is_multiref2_second(ir, topo):
    """True iff goal is multiref-2-output second-out, no-collective family."""
    sm = ir.sm_nodes[0] if ir.sm_nodes else None
    if sm is None or sm.op != "FW_multiref" or len(sm.outs) != 2 or sm.params != [2]:
        return False
    if ir.lineage.ts != sm.outs[1]:
        return False
    if any(is_collective(nd.op) for nd in ir.pm_nodes):
        return False
    finals = set(topo.final_tps)
    for nd in ir.pm_nodes:
        if nd.op != "FW_multiref" or len(nd.outs) != 2 or nd.params != [2]:
            return False
        if nd.outs[1] not in finals:
            return False
    return True


def render_multiref2_second(n, ir, topo, probe_map, input_sources, prereqs, imports):
    """Complete bridge for multiref-2-output second-out (no collective). Cloned from
    handwritten Goal259Bridge."""
    sm_node = ir.sm_nodes[0]
    sm_final = ir.lineage.ts                 # SECOND output (e.g. 907), NOT outs[0]
    sm_x = sm_node.ins[0]
    pm_finals = list(topo.final_tps)
    pm_nodes = list(ir.pm_nodes)
    pm_by_final = {nd.outs[1]: nd for nd in pm_nodes}

    header_inputs = ", ".join(f"{s.tid}<-{s.kind}:{s.upstream}" for s in input_sources)
    text = R.HEADER.format(
        n=n, sm_op=sm_node.op, sm_ins=sm_node.ins, sm_out=sm_final,
        pm_outs=pm_finals, gather_dim=ir.lineage.gatherDim, prereqs=prereqs,
        pn=len(prereqs), input_sources=header_inputs,
        imports="\n".join(f"import {m}" for m in imports),
    )
    text += MULTIREF2_SECOND_LOCAL + "\n"

    text += f"-- ========== denote_pm (finals {pm_finals} = multiref 2nd out = input) ==========\n"
    for tp in pm_finals:
        x = pm_by_final[tp].ins[0]
        rw_body = ",\n      ".join(_multiref2_second_skips(pm_nodes, tp))
        text += (
f"""theorem denote_pm_goal_{n}_{tp} (s : Store) :
    denoteGraph pm_goal_{n} s {tp} = s {x} := by
  simp only [pm_goal_{n}, denoteGraph, List.foldl]
  rw [{rw_body}]

""")

    text += f"-- ========== denote_sm (final {sm_final} = multiref 2nd out = s {sm_x}) ==========\n"
    text += (
f"""theorem denote_sm_goal_{n}_{sm_final} (s : Store) :
    denoteGraph sm_goal_{n} s {sm_final} = s {sm_x} := by
  simp only [sm_goal_{n}, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_loc _ _ {sm_node.rank} {sm_x} {sm_node.outs[0]} {sm_final} (by decide)]

""")

    sm_idx = probe_map["sm"][sm_final]["node_idx"]
    text += (
f"""theorem sm_frame_{sm_final}_self (initSM : Store) :
    denoteGraph sm initSM {sm_final} = denoteGraph sm_goal_{n} (denoteGraph sm initSM) {sm_final} := by
  rw [denote_sm_goal_{n}_{sm_final}]
  rw [sm_val initSM {sm_idx} {sm_final} (by native_decide) (by native_decide)]
  rw [show sm.nodes[{sm_idx}]'(by native_decide)
      = {{ rank := {sm_node.rank}, op := "OpName.FW_multiref", ins := [{sm_x}], outs := [{sm_node.outs[0]}, {sm_final}], params := [2] }}
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_loc _ _ {sm_node.rank} {sm_x} {sm_node.outs[0]} {sm_final} (by decide)]
  rw [sm_prefix_eq initSM {sm_idx} {sm_x} (by native_decide)]

""")

    for tp in pm_finals:
        nd = pm_by_final[tp]
        x = nd.ins[0]
        idx = probe_map["pm"][tp]["node_idx"]
        text += (
f"""theorem pm_frame_{tp}_self (initPM : Store) :
    denoteGraph pm initPM {tp} = denoteGraph pm_goal_{n} (denoteGraph pm initPM) {tp} := by
  rw [denote_pm_goal_{n}_{tp}]
  rw [pm_val initPM {idx} {tp} (by native_decide) (by native_decide)]
  rw [show pm.nodes[{idx}]'(by native_decide)
      = {{ rank := {nd.rank}, op := "OpName.FW_multiref", ins := [{x}], outs := [{nd.outs[0]}, {tp}], params := [2] }}
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_loc _ _ {nd.rank} {x} {nd.outs[0]} {tp} (by decide)]
  rw [pm_prefix_eq initPM {idx} {x} (by native_decide)]

""")

    text += R.hinitcut_helper(n, prereqs)
    text += R.cut_to_full_block(n, sm_final, pm_finals, prereqs, input_sources,
                                ir.sm_shapes, ir.pm_shapes, frame_via_denote=False)
    return text


def _reachable_mids(node, by_out, mid_set):
    """Set of mid tids reachable (as inputs, transitively) from node, following only
    the inputs that SURVIVE into each producer's RHS expression.

    A backward op that drops some of its carried inputs (e.g. BW_contiguous, whose
    RHS is just `s gTid` and discards the second input) reduces those discarded
    operand chains OUT of the goal. Their `pm_full` rewrites would then find no
    pattern. So we traverse via `_rhs_ins(producer)` (surviving inputs only), not the
    raw `producer.ins`, mirroring exactly which `denoteGraph .. tid` subterms remain
    after the producer's applyNode lemma fires."""
    seen = set()
    stack = list(_rhs_ins(node))
    while stack:
        t = stack.pop()
        if t in mid_set and t not in seen:
            seen.add(t)
            if t in by_out:
                stack.extend(_rhs_ins(by_out[t]))
    return seen


# ============================================================================
# Family A3: FW_multiref with N outputs (params=[N]), SM/PM finals = the i-th
# output (ANY position i). Generalizes A2 (which was the special case N=2, i=1).
# Every output of an N-way multiref equals the input directly (storeSet/find?
# returns the input tensor regardless of which output position is queried, as
# long as that tid differs from the earlier outputs). Validated vs handwritten
# Goal261Bridge (i=0) and Goal263Bridge (i=1): both compile RC=0, 0 sorryAx.
#
# We emit PRIVATE local copies of the goal-agnostic lemmas so we never touch the
# inviolable Denote.lean (which holds per-goal `_gNNN`-suffixed copies). The skip
# (passthrough) of non-target nodes uses the fully-generic library lemma
# `applyNode_eq_of_not_mem_outs` (works on the whole node, any output count).
# ============================================================================

def _multirefN_nth_local(num_out):
    """Emit a private local lemma proving the i-th output of a `num_out`-output
    multiref equals the input, for EACH position i in [0, num_out). Each lemma
    takes the (i) earlier outputs' distinctness from the target as hypotheses
    (only the strictly-earlier outputs can shadow `find?`)."""
    out_vars = [f"t{j}" for j in range(num_out)]
    outs_lit = "[" + ", ".join(out_vars) + "]"
    parts = [
        "-- [EMITTER] local generic multiref-N-output i-th-out lemmas (goal-agnostic)."
    ]
    for i in range(num_out):
        tgt = out_vars[i]
        # only earlier outputs (j < i) can win find? before the target; require ≠.
        hyps = [(f"h{j}{i}", f"t{j} ≠ {tgt}") for j in range(i)]
        hyp_sig = "".join(f" ({name} : {prop})" for name, prop in hyps)
        hyp_simp = "".join(f", {name}" for name, _ in hyps)
        parts.append(
            f"private theorem applyNode_fw_multiref{num_out}_out{i}_loc\n"
            f"    (g : GraphDecl) (s : Store) (rank : Nat) (x : Tid) "
            f"({' '.join(out_vars)} : Tid){hyp_sig} :\n"
            f"    applyNode g s {{ rank := rank, op := \"OpName.FW_multiref\", ins := [x],\n"
            f"                    outs := {outs_lit}, params := [{num_out}] }} {tgt} = s x := by\n"
            f"  unfold applyNode\n"
            f"  rw [show ([x] : List Tid).map s = [s x] from rfl, evalOp_fw_multiref]\n"
            f"  change storeSet s ({outs_lit}.zip (List.replicate {num_out} (s x))) {tgt} = _\n"
            f"  unfold storeSet\n"
            f"  simp [List.zip, List.zipWith, List.replicate, List.find?{hyp_simp}]\n")
    return "\n".join(parts) + "\n"


def is_multirefN_nth(ir, topo):
    """True iff goal is multiref-N-output i-th-out, no-collective family (N≥2).
    SM is a single multiref; every PM node is the SAME-shape multiref; SM final =
    lineage.ts is one of the SM outputs at index i; every PM final is the output
    at that SAME index i of its node. (A2's N=2,i=1 case is excluded here so the
    two renderers don't both claim a goal — A2 keeps its dedicated path.)"""
    if is_multiref2_second(ir, topo):
        return False
    sm = ir.sm_nodes[0] if ir.sm_nodes else None
    if sm is None or sm.op != "FW_multiref":
        return False
    num_out = len(sm.outs)
    if num_out < 2 or sm.params != [num_out]:
        return False
    if ir.lineage.ts not in sm.outs:
        return False
    idx = sm.outs.index(ir.lineage.ts)
    if any(is_collective(nd.op) for nd in ir.pm_nodes):
        return False
    finals = set(topo.final_tps)
    for nd in ir.pm_nodes:
        if nd.op != "FW_multiref" or len(nd.outs) != num_out or nd.params != [num_out]:
            return False
        # the goal final for this node must be its output at the SAME index i
        if nd.outs[idx] not in finals:
            return False
    # all finals must be accounted for by some node's index-i output
    accounted = {nd.outs[idx] for nd in ir.pm_nodes}
    if finals - accounted:
        return False
    return True


def _multirefN_nth_pm_skips(pm_nodes, target_final, idx):
    """rw list to evaluate denoteGraph for `target_final` (= output at index `idx`
    of one multiref node) over a K-node multiref mini-graph.

    foldl nests applyNode_{K-1}(...(applyNode_0 s)); rw peels OUTERMOST first.
      - nodes ABOVE the target (list index > tgt): skip on target_final (they
        don't write it) — generic `applyNode_eq_of_not_mem_outs`.
      - AT target node: apply the index-`idx` out lemma (needs the idx earlier
        outputs ≠ target as `by decide` args).
      - nodes BELOW the target (list index < tgt): expr is now `s xTid`; skip on
        xTid — generic `applyNode_eq_of_not_mem_outs`.
    Mirrors the handwritten Goal261/Goal263 ordering exactly."""
    K = len(pm_nodes)
    tgt_idx = next(i for i, nd in enumerate(pm_nodes) if nd.outs[idx] == target_final)
    tgt = pm_nodes[tgt_idx]
    xTid = tgt.ins[0]
    rws = []
    for _ in range(K - 1 - tgt_idx):
        rws.append(f"applyNode_eq_of_not_mem_outs _ _ _ {target_final} (by decide)")
    # target: idx-th out lemma; earlier-output distinctness args
    rws.append(_multirefN_nth_apply(tgt.rank, xTid, tgt.outs, idx))
    for _ in range(tgt_idx):
        rws.append(f"applyNode_eq_of_not_mem_outs _ _ _ {xTid} (by decide)")
    return rws


def _multirefN_nth_apply(rank, xTid, outs, idx):
    """The single `applyNode_fw_multirefN_outI_loc ...` application term."""
    decides = "".join(" (by decide)" for _ in range(idx))
    return (f"applyNode_fw_multiref{len(outs)}_out{idx}_loc _ _ {rank} "
            f"{xTid} {' '.join(str(t) for t in outs)}{decides}")


def render_multirefN_nth(n, ir, topo, probe_map, input_sources, prereqs, imports):
    """Complete bridge for multiref-N-output i-th-out (no collective). Generalizes
    render_multiref2_second; cloned from handwritten Goal261/Goal263Bridge."""
    sm_node = ir.sm_nodes[0]
    sm_final = ir.lineage.ts
    idx = sm_node.outs.index(sm_final)
    num_out = len(sm_node.outs)
    sm_x = sm_node.ins[0]
    pm_finals = list(topo.final_tps)
    pm_nodes = list(ir.pm_nodes)
    pm_by_final = {nd.outs[idx]: nd for nd in pm_nodes}

    header_inputs = ", ".join(f"{s.tid}<-{s.kind}:{s.upstream}" for s in input_sources)
    text = R.HEADER.format(
        n=n, sm_op=sm_node.op, sm_ins=sm_node.ins, sm_out=sm_final,
        pm_outs=pm_finals, gather_dim=ir.lineage.gatherDim, prereqs=prereqs,
        pn=len(prereqs), input_sources=header_inputs,
        imports="\n".join(f"import {m}" for m in imports),
    )
    text += _multirefN_nth_local(num_out) + "\n"

    text += (f"-- ========== denote_pm (finals {pm_finals} = multiref out[{idx}] "
             f"of {num_out} = input) ==========\n")
    for tp in pm_finals:
        x = pm_by_final[tp].ins[0]
        rw_body = ",\n      ".join(_multirefN_nth_pm_skips(pm_nodes, tp, idx))
        text += (
f"""theorem denote_pm_goal_{n}_{tp} (s : Store) :
    denoteGraph pm_goal_{n} s {tp} = s {x} := by
  simp only [pm_goal_{n}, denoteGraph, List.foldl]
  rw [{rw_body}]

""")

    text += (f"-- ========== denote_sm (final {sm_final} = multiref out[{idx}] "
             f"= s {sm_x}) ==========\n")
    text += (
f"""theorem denote_sm_goal_{n}_{sm_final} (s : Store) :
    denoteGraph sm_goal_{n} s {sm_final} = s {sm_x} := by
  simp only [sm_goal_{n}, denoteGraph, List.foldl]
  rw [{_multirefN_nth_apply(sm_node.rank, sm_x, sm_node.outs, idx)}]

""")

    sm_idx = probe_map["sm"][sm_final]["node_idx"]
    outs_lit = "[" + ", ".join(str(t) for t in sm_node.outs) + "]"
    text += (
f"""theorem sm_frame_{sm_final}_self (initSM : Store) :
    denoteGraph sm initSM {sm_final} = denoteGraph sm_goal_{n} (denoteGraph sm initSM) {sm_final} := by
  rw [denote_sm_goal_{n}_{sm_final}]
  rw [sm_val initSM {sm_idx} {sm_final} (by native_decide) (by native_decide)]
  rw [show sm.nodes[{sm_idx}]'(by native_decide)
      = {{ rank := {sm_node.rank}, op := "OpName.FW_multiref", ins := [{sm_x}], outs := {outs_lit}, params := [{num_out}] }}
      from by native_decide]
  rw [{_multirefN_nth_apply(sm_node.rank, sm_x, sm_node.outs, idx)}]
  rw [sm_prefix_eq initSM {sm_idx} {sm_x} (by native_decide)]

""")

    for tp in pm_finals:
        nd = pm_by_final[tp]
        x = nd.ins[0]
        pidx = probe_map["pm"][tp]["node_idx"]
        nd_outs_lit = "[" + ", ".join(str(t) for t in nd.outs) + "]"
        text += (
f"""theorem pm_frame_{tp}_self (initPM : Store) :
    denoteGraph pm initPM {tp} = denoteGraph pm_goal_{n} (denoteGraph pm initPM) {tp} := by
  rw [denote_pm_goal_{n}_{tp}]
  rw [pm_val initPM {pidx} {tp} (by native_decide) (by native_decide)]
  rw [show pm.nodes[{pidx}]'(by native_decide)
      = {{ rank := {nd.rank}, op := "OpName.FW_multiref", ins := [{x}], outs := {nd_outs_lit}, params := [{num_out}] }}
      from by native_decide]
  rw [{_multirefN_nth_apply(nd.rank, x, nd.outs, idx)}]
  rw [pm_prefix_eq initPM {pidx} {x} (by native_decide)]

""")

    text += R.hinitcut_helper(n, prereqs)
    text += R.cut_to_full_block(n, sm_final, pm_finals, prereqs, input_sources,
                                ir.sm_shapes, ir.pm_shapes, frame_via_denote=False)
    return text


# ============================================================================
# Family B: SM = single FW_multiref (N outputs, params=[N]) whose i-th output is the
# SM final (lineage.ts == sm.outs[i], ANY index i); PM = K per-rank FW_multiref MIDs
# (each contributing its i-th output) feeding K collective finals (AllToAll /
# AllGather / ...). Every output of an N-way multiref equals the input directly, so
# each PM mid (= node.outs[i]) == its input tid, and the collective consumes those
# inputs. The lineage cut (collective == chunk/gather of the gathered SM input)
# lives in the INVIOLABLE Generated `prove_goal_N_cut`; the emitter only frames
# full<->mini. Validated vs handwritten Goal257Bridge (2-out idx0 + AllToAll).
#
# For idx==0 of a 2-output multiref we use the GENERIC `applyNode_fw_multiref2_
# first_out` (already in Denote.lean, zero hyps). For any other (N, i) we emit the
# PRIVATE local lemmas `applyNode_fw_multirefN_outI_loc` (the same ones Family A3
# uses) so we never touch the inviolable Denote.lean.
# ============================================================================

def _mref_mid_index(ir, topo):
    """Return (num_out, idx) if SM is a single N-way FW_multiref whose i-th output is
    lineage.ts; else None. idx is the output position that feeds the collective."""
    sm = ir.sm_nodes[0] if ir.sm_nodes else None
    if sm is None or sm.op != "FW_multiref":
        return None
    num_out = len(sm.outs)
    if num_out < 2 or sm.params != [num_out]:
        return None
    if ir.lineage.ts not in sm.outs:
        return None
    return (num_out, sm.outs.index(ir.lineage.ts))


def is_multiref_first_collective(ir, topo):
    """True iff: SM is a single N-way FW_multiref whose i-th output is the SM final;
    every PM final is a collective node; and every collective input is the i-th
    output of a per-rank N-way FW_multiref MID. (Name kept for back-compat; now
    covers ANY output index i, not just the first.)"""
    nd_idx = _mref_mid_index(ir, topo)
    if nd_idx is None:
        return False
    num_out, idx = nd_idx
    finals = set(topo.final_tps)
    mid_set = set(topo.mid_tids)
    coll_nodes = [nd for nd in ir.pm_nodes if nd.outs[0] in finals]
    mref_nodes = [nd for nd in ir.pm_nodes if nd.op == "FW_multiref"]
    if not coll_nodes or not mref_nodes:
        return False
    # every final node is a collective
    if not all(is_collective(nd.op) for nd in coll_nodes):
        return False
    # every multiref mid is an N-way node whose i-th output is a mid tid
    mid_idx_outs = set()
    for nd in mref_nodes:
        if len(nd.outs) != num_out or nd.params != [num_out]:
            return False
        if nd.outs[idx] not in mid_set:
            return False
        mid_idx_outs.add(nd.outs[idx])
    # every collective input must be one of those multiref i-th-out mids
    for nd in coll_nodes:
        for t in nd.ins:
            if t not in mid_idx_outs:
                return False
    # no other op kinds in PM beyond multiref mids + collective finals
    for nd in ir.pm_nodes:
        if nd.op == "FW_multiref":
            continue
        if nd.outs[0] in finals and is_collective(nd.op):
            continue
        return False
    return True


def render_multiref_first_collective(n, ir, topo, probe_map, input_sources,
                                     prereqs, imports):
    """Complete bridge for Family B (multiref-i-th-out MIDs -> collective finals).
    Cloned structurally from handwritten Goal257Bridge; generalized to any (N, i)."""
    sm_node = ir.sm_nodes[0]
    num_out, idx = _mref_mid_index(ir, topo)
    sm_final = ir.lineage.ts          # i-th output
    sm_x = sm_node.ins[0]
    pm_finals = list(topo.final_tps)
    mid_set = set(topo.mid_tids)

    # multiref MID nodes (i-th out feeds the collective); keep creation order
    mref_nodes = [nd for nd in ir.pm_nodes
                  if nd.op == "FW_multiref" and nd.outs[idx] in mid_set]
    mid_in = {nd.outs[idx]: nd.ins[0] for nd in mref_nodes}   # mid tid -> input tid
    # collective FINAL nodes
    coll_by_final = {nd.outs[0]: nd for nd in ir.pm_nodes if nd.outs[0] in set(pm_finals)}

    # idx==0 of a 2-out multiref: use the generic Denote.lean lemma (zero hyps).
    # Otherwise emit the private local lemmas and apply the idx-th one.
    use_generic_first = (num_out == 2 and idx == 0)
    sm_apply = ("applyNode_fw_multiref2_first_out" if use_generic_first
                else _multirefN_nth_apply(sm_node.rank, sm_x, sm_node.outs, idx))

    header_inputs = ", ".join(f"{s.tid}<-{s.kind}:{s.upstream}" for s in input_sources)
    text = R.HEADER.format(
        n=n, sm_op=sm_node.op, sm_ins=sm_node.ins, sm_out=sm_final,
        pm_outs=pm_finals, gather_dim=ir.lineage.gatherDim, prereqs=prereqs,
        pn=len(prereqs), input_sources=header_inputs,
        imports="\n".join(f"import {m}" for m in imports),
    )
    if not use_generic_first:
        text += _multirefN_nth_local(num_out) + "\n"

    # ----- A: denote_pm for each collective final (in terms of the MID INPUT tids) -----
    text += (f"-- ========== denote_pm (collective finals {pm_finals}; "
             f"args = multiref-first-out inputs) ==========\n")
    for tp in pm_finals:
        nd = coll_by_final[tp]
        # collective args are `s <input_tid_of_each_mid_in>`
        args = [f"s {mid_in[t]}" for t in nd.ins]
        rhs = _collective_expr(nd.op, nd.rank, nd.params or [], args, len(nd.ins))
        meta = COLLECTIVE[nd.op]
        range_simp = ("\n  simp only [List.map]"
                      if meta["kind"] == "list" else "")
        text += (
f"""theorem denote_pm_goal_{n}_{tp} (s : Store) :
    denoteGraph pm_goal_{n} s {tp} = {rhs} := by
  simp only [pm_goal_{n}, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [{meta['mini']}]{range_simp}
  congr 1

""")

    # ----- B: denote_sm (i-th output = s sm_x) -----
    text += (f"-- ========== denote_sm (final {sm_final} = multiref out[{idx}] "
             f"= s {sm_x}) ==========\n")
    text += (
f"""theorem denote_sm_goal_{n}_{sm_final} (s : Store) :
    denoteGraph sm_goal_{n} s {sm_final} = s {sm_x} := by
  simp only [sm_goal_{n}, denoteGraph, List.foldl]
  rw [{sm_apply}]

""")

    # ----- C: sm_frame (full -> mini, i-th out) -----
    sm_idx = probe_map["sm"][sm_final]["node_idx"]
    sm_outs_lit = "[" + ", ".join(str(t) for t in sm_node.outs) + "]"
    text += (
f"""theorem sm_frame_{sm_final}_self (initSM : Store) :
    denoteGraph sm initSM {sm_final} = denoteGraph sm_goal_{n} (denoteGraph sm initSM) {sm_final} := by
  rw [denote_sm_goal_{n}_{sm_final}]
  rw [sm_val initSM {sm_idx} {sm_final} (by native_decide) (by native_decide)]
  rw [show sm.nodes[{sm_idx}]'(by native_decide)
      = {{ rank := {sm_node.rank}, op := "OpName.FW_multiref", ins := [{sm_x}], outs := {sm_outs_lit}, params := [{num_out}] }}
      from by native_decide]
  rw [{sm_apply}]
  rw [sm_prefix_eq initSM {sm_idx} {sm_x} (by native_decide)]

""")

    # ----- D: pm_frame for each MID (mid = input, via multiref i-th out) -----
    text += f"-- ========== pm_frame (multiref-out[{idx}] mids = inputs) ==========\n"
    for nd in mref_nodes:
        mid = nd.outs[idx]
        x = nd.ins[0]
        midx = probe_map["pm"][mid]["node_idx"]
        nd_outs_lit = "[" + ", ".join(str(t) for t in nd.outs) + "]"
        nd_apply = ("applyNode_fw_multiref2_first_out" if use_generic_first
                    else _multirefN_nth_apply(nd.rank, x, nd.outs, idx))
        text += (
f"""theorem pm_frame_{mid} (initPM : Store) :
    denoteGraph pm initPM {mid} = denoteGraph pm initPM {x} := by
  rw [pm_val initPM {midx} {mid} (by native_decide) (by native_decide)]
  rw [show pm.nodes[{midx}]'(by native_decide)
      = {{ rank := {nd.rank}, op := "OpName.FW_multiref", ins := [{x}], outs := {nd_outs_lit}, params := [{num_out}] }}
      from by native_decide]
  rw [{nd_apply}, pm_prefix_eq initPM {midx} {x} (by native_decide)]

""")

    # ----- E: pm_frame_self for each collective final (full -> mini, references mids) -----
    text += f"-- ========== pm_frame_self (collective finals) ==========\n"
    for tp in pm_finals:
        nd = coll_by_final[tp]
        pidx = probe_map["pm"][tp]["node_idx"]
        meta = COLLECTIVE[nd.op]
        # IMPORTANT: use the EXPLICIT ins list (not _node_literal's range form, which
        # assumes contiguous ins). Family B collective ins are the multiref mids,
        # often non-contiguous (e.g. stride-6 [3413,3419,3425,3431]).
        ins_lit = "[" + ", ".join(str(t) for t in nd.ins) + "]"
        params_lit = (", params := [" + ", ".join(str(p) for p in nd.params) + "]"
                      if nd.params else "")
        lit = (f'{{ rank := {nd.rank}, op := "OpName.{nd.op}", '
               f'ins := {ins_lit}, outs := [{tp}]{params_lit} }}')
        prefix = ",\n      ".join(
            f"pm_prefix_eq initPM {pidx} {t} (by native_decide)" for t in nd.ins)
        mid_rws = ", ".join(f"pm_frame_{t}" for t in nd.ins)
        range_simp = ("  simp only [List.map]\n"
                      if meta["kind"] == "list" else "")
        text += (
f"""theorem pm_frame_{tp}_self (initPM : Store) :
    denoteGraph pm initPM {tp} = denoteGraph pm_goal_{n} (denoteGraph pm initPM) {tp} := by
  rw [denote_pm_goal_{n}_{tp}]
  rw [pm_val initPM {pidx} {tp} (by native_decide) (by native_decide)]
  rw [show pm.nodes[{pidx}]'(by native_decide)
      = {lit}
      from by native_decide]
  rw [{meta['full']}, show pm.numRanks = 4 from by native_decide]
{range_simp}  rw [{prefix},
      {mid_rws}]

""")

    # ----- F+G: assembly (frame_via_denote=False; pm_frame_self states mini form) -----
    text += R.hinitcut_helper(n, prereqs)
    text += R.cut_to_full_block(n, sm_final, pm_finals, prereqs, input_sources,
                                ir.sm_shapes, ir.pm_shapes, frame_via_denote=False)
    return text


if __name__ == "__main__":
    print("universal renderer; driven by emit2.py")
