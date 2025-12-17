"""Load NNScaler graphs and emit a Lean4 interpreter that replays the graph.

This version constructs Lean data structures for every node/tensor pulled from
the serialized SM/PM graphs, then interprets them (with predefined semantics
for DATALOADER, FW/BW linear, sum, chunk, all-reduce, all-gather). No manual
graph sketching: changing the input pickle files changes the generated Lean
program.
"""

from __future__ import annotations

from collections import defaultdict, Counter
from dataclasses import dataclass
from pathlib import Path
import argparse
import sys
from textwrap import dedent
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SM_GRAPH = "./genmodel/mgeners/mlp_mgener_dp1_pp1_tp1_nm1_gbs128_dim128_ly1.pkl"
DEFAULT_PM_GRAPH = "./genmodel/mgeners/mlp_mgener_dp1_pp1_tp8_nm1_gbs128_dim128_ly1.pkl"
DEFAULT_OUT_CONCRETE = ROOT / "mathlib4" / "trainverify" / "equal.lean"
DEFAULT_OUT_SPEC = ROOT / "mathlib4" / "trainverify" / "equal_spec.lean"


@dataclass
class TensorMeta:
    tid: int
    shape: Tuple[int, ...]
    initialized: bool


@dataclass
class NodeMeta:
    op: str
    kwargs: Dict
    inputs: List[int]
    outputs: List[int]


def parse_args() -> argparse.Namespace:
  parser = argparse.ArgumentParser(
    description="Emit Lean specs for SM/PM graphs with optional overrides.")
  parser.add_argument(
    "--sm-pkl",
    dest="sm_pkl",
    default=DEFAULT_SM_GRAPH,
    help="Path to the single-model (baseline) graph pickle.")
  parser.add_argument(
    "--pm-pkl",
    dest="pm_pkl",
    default=DEFAULT_PM_GRAPH,
    help="Path to the parallel-model graph pickle.")
  parser.add_argument(
    "--obs-tid",
    dest="obs_tid",
    type=int,
    default=None,
    help="Override the observable tensor id; defaults to the smallest shared tid.")
  parser.add_argument(
    "--out-concrete",
    dest="out_concrete",
    default=str(DEFAULT_OUT_CONCRETE),
    help="Lean file path for the concrete interpreter (default: equal.lean).")
  parser.add_argument(
    "--out-spec",
    dest="out_spec",
    default=str(DEFAULT_OUT_SPEC),
    help="Lean file path for the spec (default: equal_spec.lean).")
  return parser.parse_args()


def load_graphs_from_disk(sm_path: str, pm_path: str):
  sys.path.extend([str(ROOT), str(ROOT / "genmodel"), str(ROOT / "Verdict")])
  from analyze_graph import load_graphs, prepare  # type: ignore
  from verdict.config import Config  # type: ignore

  Config.update_from_args([])
  prepare(Config)

  return load_graphs(sm_path, pm_path)


def extract(graph) -> Tuple[List[NodeMeta], Dict[int, TensorMeta]]:
  tensors: Dict[int, TensorMeta] = {}
  nodes: List[NodeMeta] = []
  for node in graph.nodes():
    op = str(graph.node_opname(node))
    kwargs = dict(graph.node_kwargs(node))
    ins: List[int] = []
    outs: List[int] = []
    for t in graph.node_inputs(node):
      tensors[t.tid] = TensorMeta(t.tid, graph.tensor_shape(t), graph.is_initialized(t))
      ins.append(t.tid)
    for t in graph.node_outputs(node):
      tensors[t.tid] = TensorMeta(t.tid, graph.tensor_shape(t), graph.is_initialized(t))
      outs.append(t.tid)
    nodes.append(NodeMeta(op=op, kwargs=kwargs, inputs=ins, outputs=outs))
  return nodes, tensors


def lean_list_int(xs: List[int]) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_shape(shape: Tuple[int, ...]) -> str:
    return lean_list_int(list(shape))


def render_nat_list_pairs(pairs: List[Tuple[int, List[int]]]) -> str:
    if not pairs:
        return "[]"
    parts = []
    for tid, related in pairs:
        parts.append(f"({tid}, {lean_list_int(related)})")
    return "[" + ", ".join(parts) + "]"


def emit_tensors(name: str, tensors: Dict[int, TensorMeta]) -> str:
  items = []
  for tid, meta in sorted(tensors.items()):
    items.append(f"({tid}, {lean_shape(meta.shape)}, {'true' if meta.initialized else 'false'})")
  body = "[" + ", ".join(items) + "]"
  return f"def {name} : List (Nat × List Nat × Bool) := {body}\n"


def node_literal(n: NodeMeta) -> str:
  op = op_ctor(n.op, n.kwargs)
  ins = lean_list_int(n.inputs)
  outs = lean_list_int(n.outputs)
  return f"⟨{op}, {ins}, {outs}⟩"


def op_kind(op: str, kwargs: Dict) -> Tuple[str, Dict[str, int]]:
  if "DATALOADER" in op:
    return "dataloader", {}
  if "FW_linear" in op:
    return "fw_linear", {}
  if "BW_linear" in op:
    return "bw_linear", {}
  if "FW_sum" in op:
    return "fw_sum", {}
  if "BW_sum" in op:
    return "bw_sum", {}
  if "ChunkPrim" in op:
    dim = int(kwargs.get("dim", 1))
    idx = int(kwargs.get("__collective_idx", 0)) if "__collective_idx" in kwargs else 0
    return "chunk", {"dim": dim, "idx": idx}
  if "AllGatherPrim" in op:
    dim = int(kwargs.get("dim", 0))
    return "all_gather", {"dim": dim}
  if "AllReducePrim" in op:
    return "all_reduce", {}
  return "unknown", {}


def op_ctor(op: str, kwargs: Dict) -> str:
  kind, meta = op_kind(op, kwargs)
  if kind == "dataloader":
    return "Op.dataloader"
  if kind == "fw_linear":
    return "Op.fwLinear"
  if kind == "bw_linear":
    return "Op.bwLinear"
  if kind == "fw_sum":
    return "Op.fwSum"
  if kind == "bw_sum":
    return "Op.bwSum"
  if kind == "chunk":
    return f"Op.chunk {meta['dim']} {meta['idx']}"
  if kind == "all_gather":
    return f"Op.allGather {meta['dim']}"
  if kind == "all_reduce":
    return "Op.allReduce"
  return "Op.unknown"


def emit_nodes(name: str, nodes: List[NodeMeta]) -> str:
  parts = [node_literal(n) for n in nodes]
  body = "[" + ",\n  ".join(parts) + "]"
  return f"def {name} : List Node := {body}\n"


def emit_store_presence_def(name: str, data: List[List[int]]) -> str:
  body_parts = [lean_list_int(lst) for lst in data]
  body = "[" + ", ".join(body_parts) + "]"
  return f"def {name} : List (List Nat) := {body}\n"


def exec_plan_literal(nodes: List[NodeMeta], deps: List[Tuple[int, List[int]]]) -> str:
  dep_map: Dict[int, List[int]] = {idx: dep_list for idx, dep_list in deps}
  entries = []
  for idx, node in enumerate(nodes):
    dep_list = dep_map.get(idx, [])
    entries.append(f"⟨{idx}, {node_literal(node)}, {lean_list_int(dep_list)}⟩")
  return "[" + ",\n  ".join(entries) + "]"


def emit_progress_lemmas(prefix: str, nodes: List[NodeMeta], deps: List[Tuple[int, List[int]]], shapes_name: str, inits_name: str) -> str:
  dep_map: Dict[int, List[int]] = {idx: dep_list for idx, dep_list in deps}
  lemmas: List[str] = []
  for idx, node in enumerate(nodes):
    dep_list = dep_map.get(idx, [])
    lemma_name = f"{prefix}NodeProgress_{idx}"
    doc = f"/-- Progress lemma for {prefix.upper()} node {idx}; deps = {dep_list}. -/"
    node_term = node_literal(node)
    inputs_expr = lean_list_int(node.inputs)
    outputs_expr = lean_list_int(node.outputs)
    kind, meta = op_kind(node.op, node.kwargs)

    assumptions: List[Tuple[str, str]] = []
    helper_call: str

    if kind == "dataloader":
      if not node.outputs:
        raise ValueError(f"Dataloader node {idx} must have at least one output")
      head = node.outputs[0]
      rest_expr = lean_list_int(node.outputs[1:])
      assumptions.append(("hmiss", f"outputsExist {outputs_expr} st = false"))
      helper_call = (
        f"nodeProgress_dataloader (env := env) (shapes := {shapes_name}) "
        f"(inits := {inits_name}) (out := {head}) (restOuts := {rest_expr}) "
        "(st := st) hmiss"
      )
    elif kind == "chunk":
      dim = meta.get("dim", 0)
      idx_param = meta.get("idx", 0)
      assumptions.append(("hready", f"inputsReady {inits_name} {inputs_expr} st = true"))
      assumptions.append(("hmiss", f"outputsExist {outputs_expr} st = false"))
      helper_call = (
        f"nodeProgress_chunk (env := env) (shapes := {shapes_name}) "
        f"(inits := {inits_name}) (dim := {dim}) (idx := {idx_param}) "
        f"(ins := {inputs_expr}) (outs := {outputs_expr}) (st := st) hready hmiss"
      )
    elif kind == "all_gather":
      dim = meta.get("dim", 0)
      assumptions.append(("hready", f"inputsReady {inits_name} {inputs_expr} st = true"))
      assumptions.append(("hmiss", f"outputsExist {outputs_expr} st = false"))
      helper_call = (
        f"nodeProgress_allGather (env := env) (shapes := {shapes_name}) "
        f"(inits := {inits_name}) (dim := {dim}) (ins := {inputs_expr}) "
        f"(outs := {outputs_expr}) (st := st) hready hmiss"
      )
    else:
      helper_map = {
        "fw_linear": "nodeProgress_fwLinear",
        "bw_linear": "nodeProgress_bwLinear",
        "fw_sum": "nodeProgress_fwSum",
        "bw_sum": "nodeProgress_bwSum",
        "all_reduce": "nodeProgress_allReduce",
      }
      if kind not in helper_map:
        raise ValueError(f"Unsupported op {node.op} for NodeProgress automation")
      helper_name = helper_map[kind]
      assumptions.append(("hready", f"inputsReady {inits_name} {inputs_expr} st = true"))
      assumptions.append(("hmiss", f"outputsExist {outputs_expr} st = false"))
      helper_call = (
        f"{helper_name} (env := env) (shapes := {shapes_name}) "
        f"(inits := {inits_name}) (ins := {inputs_expr}) (outs := {outputs_expr}) "
        "(st := st) hready hmiss"
      )

    binder_str = "".join(f"\n    ({name} : {expr})" for name, expr in assumptions)
    proof = f"  simpa using\n    {helper_call}"
    lemma = f"""
{doc}
lemma {lemma_name} {{α : Type}} [Semiring α] (env : Env α) (st : Store α){binder_str} :
  NodeProgress env {shapes_name} {inits_name} {node_term} st := by
{proof}
"""
    lemmas.append(lemma.strip("\n"))
  return "\n\n".join(lemmas)


def compute_tensor_relations(nodes: List[NodeMeta]) -> Tuple[Dict[int, List[int]], Dict[int, List[int]], List[Tuple[int, List[int]]]]:
    producers: Dict[int, List[int]] = defaultdict(list)
    for idx, node in enumerate(nodes):
        for tid in node.outputs:
            producers[tid].append(idx)

    consumers: Dict[int, List[int]] = defaultdict(list)
    for idx, node in enumerate(nodes):
        for tid in node.inputs:
            consumers[tid].append(idx)

    deps: List[Tuple[int, List[int]]] = []
    for idx, node in enumerate(nodes):
        dep_set = set()
        for tid in node.inputs:
            for prod in producers.get(tid, []):
                dep_set.add(prod)
        deps.append((idx, sorted(dep_set)))

    producers_sorted = {tid: sorted(idxs) for tid, idxs in producers.items()}
    consumers_sorted = {tid: sorted(idxs) for tid, idxs in consumers.items()}
    return producers_sorted, consumers_sorted, deps


def enforce_unique_writes(nodes: List[NodeMeta], tensors: Dict[int, TensorMeta]) -> Tuple[List[NodeMeta], Dict[int, TensorMeta]]:
  """Rename tensor ids so that every write produces a fresh id, while reserving the
  canonical id for the final writer. Inputs are rewritten to always reference the
  latest version, yielding an SSA-like graph where GraphWitness assumptions hold."""

  write_counts: Counter[int] = Counter()
  for node in nodes:
    for tid in node.outputs:
      write_counts[tid] += 1

  if not tensors:
    return nodes, tensors

  next_tid = max(tensors.keys()) + 1
  current_version: Dict[int, int] = {tid: tid for tid in tensors.keys()}
  new_tensors = dict(tensors)
  new_nodes: List[NodeMeta] = []

  for node in nodes:
    new_inputs = [current_version.get(tid, tid) for tid in node.inputs]
    new_outputs: List[int] = []
    for tid in node.outputs:
      remaining = write_counts[tid]
      if remaining <= 0:
        raise ValueError(f"Tensor {tid} has no remaining producers")
      if remaining == 1:
        assigned = tid
      else:
        assigned = next_tid
        next_tid += 1
        meta = tensors[tid]
        new_tensors[assigned] = TensorMeta(assigned, meta.shape, meta.initialized)
      write_counts[tid] -= 1
      current_version[tid] = assigned
      new_outputs.append(assigned)
    new_nodes.append(NodeMeta(op=node.op, kwargs=node.kwargs, inputs=new_inputs, outputs=new_outputs))

  return new_nodes, new_tensors


def simulate_store_presence(nodes: List[NodeMeta], init_tids: List[int]) -> Tuple[List[List[int]], List[List[int]]]:
  """Compute the tensor ids present in the store immediately before and after
  each node executes, assuming SSA form and that initial tensors become
  available once first accessed."""

  init_set = set(init_tids)
  present: Dict[int, None] = {}
  before: List[List[int]] = []
  after: List[List[int]] = []

  for node in nodes:
    before.append(sorted(present.keys()))
    for tid in node.inputs:
      if tid in init_set and tid not in present:
        present[tid] = None
    for tid in node.outputs:
      if tid in present:
        raise ValueError(f"Tensor {tid} already present before node output; plan not SSA")
      present[tid] = None
    after.append(sorted(present.keys()))

  return before, after


def main() -> None:
    args = parse_args()
    g_single, g_parallel = load_graphs_from_disk(args.sm_pkl, args.pm_pkl)
    sm_nodes, sm_tensors_raw = extract(g_single)
    pm_nodes, pm_tensors = extract(g_parallel)
    sm_nodes, sm_tensors_raw = enforce_unique_writes(sm_nodes, sm_tensors_raw)
    pm_nodes, pm_tensors = enforce_unique_writes(pm_nodes, pm_tensors)
    sm_producers, sm_consumers, sm_deps = compute_tensor_relations(sm_nodes)
    pm_producers, pm_consumers, pm_deps = compute_tensor_relations(pm_nodes)

    # Align shapes of tensors shared across SM/PM so comparisons operate on the
    # same geometry (keep SM initialization flags intact).
    sm_tensors: Dict[int, TensorMeta] = {}
    for tid, meta in sm_tensors_raw.items():
        if tid in pm_tensors:
            pm_shape = pm_tensors[tid].shape
            sm_tensors[tid] = TensorMeta(meta.tid, pm_shape, meta.initialized)
        else:
            sm_tensors[tid] = meta

    # choose a shared observable tensor ID present in both graphs; default to smallest common tid
    common_tids = sorted(set(sm_tensors.keys()) & set(pm_tensors.keys()))
    obs_tid = args.obs_tid if args.obs_tid is not None else (common_tids[0] if common_tids else 0)

    # identify SM full weight and PM sharded weights (initialized matrices)
    sm_weight_tid = min([tid for tid, meta in sm_tensors.items() if meta.initialized and len(meta.shape) == 2] or [0])
    pm_inits = [(tid, meta.shape) for tid, meta in pm_tensors.items() if meta.initialized and len(meta.shape) == 2]
    shard_width = min([s[1] for _, s in pm_inits] or [1])
    pm_weight_tids = [tid for tid, shape in pm_inits if shape[1] == shard_width]
    pm_weight_tids.sort()
    pm_chunk = shard_width

    shared_tids = sorted(set(sm_tensors.keys()) & set(pm_tensors.keys()))
    sm_only_tids = sorted(set(sm_tensors.keys()) - set(pm_tensors.keys()))
    pm_only_tids = sorted(set(pm_tensors.keys()) - set(sm_tensors.keys()))
    sm_init_tids = sorted(tid for tid, meta in sm_tensors.items() if meta.initialized)
    pm_init_tids = sorted(tid for tid, meta in pm_tensors.items() if meta.initialized)
    shared_init_tids = sorted(set(sm_init_tids) & set(pm_init_tids))
    pm_shard_count = len(pm_weight_tids)

    sm_store_before, sm_store_after = simulate_store_presence(sm_nodes, sm_init_tids)
    pm_store_before, pm_store_after = simulate_store_presence(pm_nodes, pm_init_tids)

    def mapping_literal(mapping: Dict[int, List[int]]) -> str:
        pairs = sorted((tid, ids) for tid, ids in mapping.items())
        return render_nat_list_pairs(pairs)

    def deps_literal(deps: List[Tuple[int, List[int]]]) -> str:
        ordered = sorted(deps, key=lambda item: item[0])
        return render_nat_list_pairs(ordered)

    template_concrete = """
import Std

open Std

abbrev Matrix := List (List Float)

inductive Op where
  | dataloader
  | fwLinear
  | bwLinear
  | fwSum
  | bwSum
  | chunk (dim : Nat) (idx : Nat)
  | allReduce
  | allGather (dim : Nat)
  | unknown
deriving Repr

structure Node where
  op : Op
  inputs : List Nat
  outputs : List Nat
deriving Repr

def toMap (xs : List (Nat × α)) : Std.HashMap Nat α :=
  xs.foldl (fun m (k,v) => m.insert k v) {}

__TENSORS_SM__
__TENSORS_PM__
__NODES_SM__
__NODES_PM__

def smWeightTid : Nat := __SM_W_TID__
def pmWeightTids : List (Nat × Nat) := __PM_W_TIDS__  -- (tid, shardIdx)
def pmChunk : Nat := __PM_CHUNK__

-- deterministic pseudo-random (lightweight): value = scaled(seed + i + j)
def randFloat (state : Nat) : Float :=
  let v := (state % 1000).toFloat / 1000.0
  v * 2.0 - 1.0

def makeMatrix (rows cols seed : Nat) : Matrix :=
  List.range rows |>.map (fun i =>
    List.range cols |>.map (fun j => randFloat (seed + i + j)))

def zerosLike (shape : List Nat) : Matrix :=
  match shape with
  | [r, c] => List.replicate r (List.replicate c 0.0)
  | [r]    => [List.replicate r 0.0]
  | _      => []

def shapeMap (xs : List (Nat × List Nat × Bool)) : Std.HashMap Nat (List Nat) :=
  xs.foldl (fun m (k, s, _) => m.insert k s) {}

def initMap (xs : List (Nat × List Nat × Bool)) : Std.HashMap Nat Bool :=
  xs.foldl (fun m (k, _, b) => m.insert k b) {}

abbrev Store := Std.HashMap Nat Matrix

def getTensor (shapes : Std.HashMap Nat (List Nat)) (inits : Std.HashMap Nat Bool)
    (tid : Nat) (st : Store) : Matrix × Store :=
  match st.find? tid with
  | some v => (v, st)
  | none =>
    let shp := shapes.findD tid []
    let init := inits.findD tid false
    let seed := tid + 17
    -- shared base weight for SM and PM shards
    let baseShape := shapes.findD smWeightTid []
    let shardCols := pmChunk * pmWeightTids.length
    let rows := match baseShape with
      | [r, _] => r
      | _ =>
        match pmWeightTids.head? with
        | some (t, _) =>
            match shapes.findD t [] with
            | [r, _] => r
            | _ => 0
        | none => 0
    let cols := match baseShape with
      | [_ , c] => c
      | _ => shardCols
    let baseWeight : Matrix := makeMatrix rows cols 123
    let shardFromBase (idx : Nat) : Matrix := baseWeight.map (fun r => (r.drop (idx * pmChunk)).take pmChunk)
    let v := if init && shp.length = 2 then
      if tid = smWeightTid then baseWeight
      else match pmWeightTids.find? (fun (t, _) => t = tid) with
        | some (_, idx) => shardFromBase idx
        | none => makeMatrix (shp.get! 0) (shp.get! 1) seed
      else zerosLike shp
    (v, st.insert tid v)

def transpose (m : Matrix) : Matrix :=
  match m with
  | [] => []
  | row :: _ =>
    let cols := row.length
    List.range cols |>.map (fun j => m.map (fun r => r.getD j 0.0))

def dot (a b : List Float) : Float :=
  List.zipWith (· * ·) a b |> List.foldl (· + ·) 0.0

def matmul (a b : Matrix) : Matrix :=
  let bt := transpose b
  a.map (fun row => bt.map (dot row))

def sumAll (m : Matrix) : Float :=
  m.foldl (fun acc row => acc + row.foldl (· + ·) 0.0) 0.0

def sumRows (m : Matrix) : List Float :=
  m.foldl (fun acc row => if acc.length = 0 then row else List.zipWith (· + ·) acc row) []

def onesLike (shape : List Nat) : Matrix :=
  match shape with
  | [r, c] => List.replicate r (List.replicate c 1.0)
  | [r]    => [List.replicate r 1.0]
  | _      => []

def sliceCols (m : Matrix) (start count : Nat) : Matrix :=
  m.map (fun r => (r.drop start).take count)

def sliceRows (m : Matrix) (start count : Nat) : Matrix :=
  (m.drop start).take count

def concatCols (ms : List Matrix) : Matrix :=
  match ms with
  | [] => []
  | _ =>
    let rows := ms.head!.length
    List.range rows |>.map (fun i => ms.foldl (fun acc m => acc ++ m.get! i) [])

def concatRows (ms : List Matrix) : Matrix := ms.foldl (· ++ ·) []

def chunkBy (m : Matrix) (dim start count : Nat) : Matrix :=
  if dim = 0 then sliceRows m start count else sliceCols m start count

def gatherBy (dim : Nat) (parts : List Matrix) : Matrix :=
  if dim = 0 then concatRows parts else concatCols parts

def allReduce (ms : List Matrix) : Matrix :=
  match ms with
  | [] => []
  | m0 :: rest => rest.foldl (fun acc m => List.zipWith (fun r1 r2 => List.zipWith (· + ·) r1 r2) acc m) m0

def headTailN (n : Nat) (xs : List α) : List α :=
  if xs.length ≤ n then xs else xs.take n ++ xs.drop (xs.length - n)

def preview (rows cols : Nat) (m : Matrix) : Matrix :=
  let rsel := headTailN rows m
  rsel.map (fun row => headTailN cols row)

def outputsExist (tids : List Nat) (st : Store) : Bool := tids.all (fun t => st.contains t)

def inputsReady (inits : Std.HashMap Nat Bool) (tids : List Nat) (st : Store) : Bool :=
  tids.all (fun t => st.contains t || inits.findD t false)

def runNode (shapes : Std.HashMap Nat (List Nat)) (inits : Std.HashMap Nat Bool)
    (n : Node) (st : Store) : Store :=
  if outputsExist n.outputs st then st else
  match n.op with
  | Op.dataloader =>
      let shp := shapes.findD n.outputs.head! []
      let seed := n.outputs.head! + 7
      let v := if shp.length = 2 then makeMatrix (shp.get! 0) (shp.get! 1) seed else zerosLike shp
      st.insert n.outputs.head! v
  | Op.fwLinear =>
        if ¬ inputsReady inits n.inputs st then st else
      let (x, st) := getTensor shapes inits (n.inputs.get! 0) st
      let (w, st) := getTensor shapes inits (n.inputs.get! 1) st
      let y := matmul x (transpose w)
      st.insert (n.outputs.get! 0) y
  | Op.fwSum =>
        if ¬ inputsReady inits n.inputs st then st else
      let (x, st) := getTensor shapes inits (n.inputs.get! 0) st
      let s := sumAll x
      st.insert (n.outputs.get! 0) [[s]]
  | Op.bwSum =>
        if ¬ inputsReady inits n.inputs st then st else
      let (g, st) := getTensor shapes inits (n.inputs.get! 0) st
      let (x, st) := getTensor shapes inits (n.inputs.get! 1) st
      let scalar := match g.head? with | some row => row.headD 1.0 | none => 1.0
      let gx := x.map (fun row => row.map (fun _ => scalar))
      st.insert (n.outputs.get! 0) gx
  | Op.bwLinear =>
        if ¬ inputsReady inits n.inputs st then st else
      let (go, st) := getTensor shapes inits (n.inputs.get! 0) st
      let (x, st) := getTensor shapes inits (n.inputs.get! 1) st
      let (w, st) := getTensor shapes inits (n.inputs.get! 2) st
      let gx := matmul go w
      let gw := matmul (transpose x) go
      let st := st.insert (n.outputs.get! 0) gx
      st.insert (n.outputs.get! 1) gw
  | Op.chunk dim idx =>
        if ¬ inputsReady inits n.inputs st then st else
      let (x, st) := getTensor shapes inits (n.inputs.get! 0) st
      let shpOut := shapes.findD (n.outputs.get! 0) []
      let size := if shpOut.length = 2 then (if dim = 0 then shpOut.get! 0 else shpOut.get! 1) else 0
      let start := idx * size
      let part := chunkBy x dim start size
      st.insert (n.outputs.get! 0) part
  | Op.allGather dim =>
        if ¬ inputsReady inits n.inputs st then st else
      let (parts, st) := n.inputs.foldl (fun (ps, st) tid =>
        let (t, st) := getTensor shapes inits tid st
        (ps ++ [t], st)) ([], st)
      let y := gatherBy dim parts
      st.insert (n.outputs.get! 0) y
  | Op.allReduce =>
        if ¬ inputsReady inits n.inputs st then st else
      let (parts, st) := n.inputs.foldl (fun (ps, st) tid =>
        let (t, st) := getTensor shapes inits tid st
        (ps ++ [t], st)) ([], st)
      let y := allReduce parts
      st.insert (n.outputs.get! 0) y
  | Op.unknown => st

def runGraph (nodes : List Node) (shapes : Std.HashMap Nat (List Nat)) (inits : Std.HashMap Nat Bool) : Store :=
  let rec loop (st : Store) (fuel : Nat) : Store :=
    if fuel = 0 then st else
    let (st', progressed) := nodes.foldl (fun (st, prog) n =>
      let stNew := runNode shapes inits n st
      let prog' := prog || (¬ outputsExist n.outputs st) && outputsExist n.outputs stNew
      (stNew, prog')) (st, false)
    if progressed then loop st' (fuel - 1) else st'
  loop {} (5 * nodes.length + 5)

def smShapes := shapeMap tensorShapesSM
def smInits  := initMap tensorShapesSM
def pmShapes := shapeMap tensorShapesPM
def pmInits  := initMap tensorShapesPM

def smStore := runGraph smNodes smShapes smInits
def pmStore := runGraph pmNodes pmShapes pmInits

def smOut : Matrix := smStore.findD __OBS_TID__ []
def pmOut : Matrix := pmStore.findD __OBS_TID__ []

def same : Bool := smOut == pmOut

#eval same
#eval preview 10 10 smOut
#eval preview 10 10 pmOut
"""

    template_spec = """
    import trainverify.core.GraphSpec
    import trainverify.core.GraphWitness
    import trainverify.core.GraphWitnessPipeline
    import trainverify.core.Lemmas

    open Std TrainVerify GraphWitnessPipeline

    namespace TrainVerify.EqualSpec

    universe u

    __TENSORS_SM__
    __TENSORS_PM__
    __NODES_SM__
    __NODES_PM__

    def smSpec : GraphSpec :=
      { tensors := tensorShapesSM
      , nodes := smNodes
      , obsTid := __OBS_TID__
      , fuel := __SM_FUEL__ }

    def pmSpec : GraphSpec :=
      { tensors := tensorShapesPM
      , nodes := pmNodes
      , obsTid := __OBS_TID__
      , fuel := __PM_FUEL__ }

    def sharedTensorIds : List Nat := __SHARED_TIDS__
    def smOnlyTensorIds : List Nat := __SM_ONLY_TIDS__
    def pmOnlyTensorIds : List Nat := __PM_ONLY_TIDS__
    def smInitTensorIds : List Nat := __SM_INIT_TIDS__
    def pmInitTensorIds : List Nat := __PM_INIT_TIDS__
    def sharedInitTensorIds : List Nat := __SHARED_INIT_TIDS__

    def pmShardCount : Nat := __PM_SHARD_COUNT__

    __SM_STORE_BEFORE__
    __SM_STORE_AFTER__
    __PM_STORE_BEFORE__
    __PM_STORE_AFTER__

    def smTensorProducers : List (Nat × List Nat) := __SM_TENSOR_PRODUCERS__
    def smTensorConsumers : List (Nat × List Nat) := __SM_TENSOR_CONSUMERS__
    def smNodeDependencies : List (Nat × List Nat) := __SM_NODE_DEPS__
    def pmTensorProducers : List (Nat × List Nat) := __PM_TENSOR_PRODUCERS__
    def pmTensorConsumers : List (Nat × List Nat) := __PM_TENSOR_CONSUMERS__
    def pmNodeDependencies : List (Nat × List Nat) := __PM_NODE_DEPS__

    def smExecPlan : List ExecPlanEntry := __SM_EXEC_PLAN__
    def pmExecPlan : List ExecPlanEntry := __PM_EXEC_PLAN__

    def smExecState {α : Type u} : ExecPlanState α :=
      GraphWitnessPipeline.mkState (α := α) smExecPlan

    def pmExecState {α : Type u} : ExecPlanState α :=
      GraphWitnessPipeline.mkState (α := α) pmExecPlan

    __SM_PROGRESS_LEMMAS__

    __PM_PROGRESS_LEMMAS__

    def smShapes : ShapeMap := smSpec.shapeMap
    def pmShapes : ShapeMap := pmSpec.shapeMap
    def smInits : InitMap := smSpec.initMap
    def pmInits : InitMap := pmSpec.initMap

    lemma obsTid_mem_shared : smSpec.obsTid ∈ sharedTensorIds := by
      decide

    lemma obsTid_eq : smSpec.obsTid = pmSpec.obsTid := rfl

    variable {α : Type} [Semiring α]

    def smRuntime (env : Env α) : Runtime α := smSpec.runtime env
    def pmRuntime (env : Env α) : Runtime α := pmSpec.runtime env

    def smStore (env : Env α) : Store α := smSpec.store env
    def pmStore (env : Env α) : Store α := pmSpec.store env

    def smOut (env : Env α) : Mat α := smSpec.output env
    def pmOut (env : Env α) : Mat α := pmSpec.output env

    def graphsAgree (env : Env α) : Prop := smOut env = pmOut env

    lemma smGraphWitness (env : Env α) :
        GraphExecWitness env smShapes smInits (smExecState (α := α)) := by
      intro idx
      sorry

    lemma pmGraphWitness (env : Env α) :
        GraphExecWitness env pmShapes pmInits (pmExecState (α := α)) := by
      intro idx
      sorry

    def smExecPlanWitness (env : Env α) :
        GraphWitnessPipeline.ExecPlanWitness env smShapes smInits :=
      { state := smExecState (α := α)
      , witness := smGraphWitness env }

    def pmExecPlanWitness (env : Env α) :
        GraphWitnessPipeline.ExecPlanWitness env pmShapes pmInits :=
      { state := pmExecState (α := α)
      , witness := pmGraphWitness env }

    def execWitnessPair (env : Env α) :
        GraphWitnessPipeline.WitnessPair env smShapes smInits pmShapes pmInits :=
      { sm := smExecPlanWitness env
      , pm := pmExecPlanWitness env }

    lemma sharedTensorEquality (env : Env α) :
        ∀ tid, tid ∈ sharedTensorIds →
          (ExecPlanState.finalStore (smExecState (α := α))
              (Runtime.mkStandard env smShapes smInits)).getD tid [] =
          (ExecPlanState.finalStore (pmExecState (α := α))
              (Runtime.mkStandard env pmShapes pmInits)).getD tid [] := by
      intro tid hmem
      sorry

    lemma smFinalStore_eq_output (env : Env α) :
        (ExecPlanState.finalStore (smExecState (α := α))
            (Runtime.mkStandard env smShapes smInits)).getD smSpec.obsTid [] = smOut env := by
      sorry

    lemma pmFinalStore_eq_output (env : Env α) :
        (ExecPlanState.finalStore (pmExecState (α := α))
            (Runtime.mkStandard env pmShapes pmInits)).getD pmSpec.obsTid [] = pmOut env := by
      sorry

    lemma smFuel_sufficient : smSpec.fuelSufficient := by
      dsimp [GraphSpec.fuelSufficient, GraphSpec.minFuel, smSpec]
      exact Nat.le_of_eq rfl

    lemma pmFuel_sufficient : pmSpec.fuelSufficient := by
      dsimp [GraphSpec.fuelSufficient, GraphSpec.minFuel, pmSpec]
      exact Nat.le_of_eq rfl

    theorem graphsAgree_result {α : Type} [Semiring α] (env : Env α) : graphsAgree env := by
      classical
      let pair := execWitnessPair (α := α) env
      have hshared := sharedTensorEquality (α := α) env
      have hObs : smSpec.obsTid ∈ sharedTensorIds := obsTid_mem_shared
      have hSm := smFinalStore_eq_output (α := α) env
      have hPm := by
        simpa [obsTid_eq] using
          pmFinalStore_eq_output (α := α) env
      exact
        GraphWitnessPipeline.WitnessPair.outputsAgree pair sharedTensorIds smSpec.obsTid
          hshared hObs hSm hPm

    end TrainVerify.EqualSpec
    """

    lean_concrete = template_concrete.replace("__TENSORS_SM__", emit_tensors("tensorShapesSM", sm_tensors))
    lean_concrete = lean_concrete.replace("__TENSORS_PM__", emit_tensors("tensorShapesPM", pm_tensors))
    lean_concrete = lean_concrete.replace("__NODES_SM__", emit_nodes("smNodes", sm_nodes))
    lean_concrete = lean_concrete.replace("__NODES_PM__", emit_nodes("pmNodes", pm_nodes))
    lean_concrete = lean_concrete.replace("__OBS_TID__", str(obs_tid))
    lean_concrete = lean_concrete.replace("__SM_W_TID__", str(sm_weight_tid))
    pm_w_pairs = "[" + ", ".join(f"({tid}, {idx})" for idx, tid in enumerate(pm_weight_tids)) + "]"
    lean_concrete = lean_concrete.replace("__PM_W_TIDS__", pm_w_pairs)
    lean_concrete = lean_concrete.replace("__PM_CHUNK__", str(pm_chunk))

    lean_spec = template_spec.replace("__TENSORS_SM__", emit_tensors("tensorShapesSM", sm_tensors))
    lean_spec = lean_spec.replace("__TENSORS_PM__", emit_tensors("tensorShapesPM", pm_tensors))
    lean_spec = lean_spec.replace("__NODES_SM__", emit_nodes("smNodes", sm_nodes))
    lean_spec = lean_spec.replace("__NODES_PM__", emit_nodes("pmNodes", pm_nodes))
    sm_fuel = 5 * len(sm_nodes) + 5
    pm_fuel = 5 * len(pm_nodes) + 5

    lean_spec = lean_spec.replace("__OBS_TID__", str(obs_tid))
    lean_spec = lean_spec.replace("__SM_FUEL__", str(sm_fuel))
    lean_spec = lean_spec.replace("__PM_FUEL__", str(pm_fuel))
    lean_spec = lean_spec.replace("__SHARED_TIDS__", lean_list_int(shared_tids))
    lean_spec = lean_spec.replace("__SM_ONLY_TIDS__", lean_list_int(sm_only_tids))
    lean_spec = lean_spec.replace("__PM_ONLY_TIDS__", lean_list_int(pm_only_tids))
    lean_spec = lean_spec.replace("__SM_INIT_TIDS__", lean_list_int(sm_init_tids))
    lean_spec = lean_spec.replace("__PM_INIT_TIDS__", lean_list_int(pm_init_tids))
    lean_spec = lean_spec.replace("__SHARED_INIT_TIDS__", lean_list_int(shared_init_tids))
    lean_spec = lean_spec.replace("__PM_SHARD_COUNT__", str(pm_shard_count))
    lean_spec = lean_spec.replace("__SM_STORE_BEFORE__", emit_store_presence_def("smStoreTidsBefore", sm_store_before))
    lean_spec = lean_spec.replace("__SM_STORE_AFTER__", emit_store_presence_def("smStoreTidsAfter", sm_store_after))
    lean_spec = lean_spec.replace("__PM_STORE_BEFORE__", emit_store_presence_def("pmStoreTidsBefore", pm_store_before))
    lean_spec = lean_spec.replace("__PM_STORE_AFTER__", emit_store_presence_def("pmStoreTidsAfter", pm_store_after))
    lean_spec = lean_spec.replace("__SM_TENSOR_PRODUCERS__", mapping_literal(sm_producers))
    lean_spec = lean_spec.replace("__SM_TENSOR_CONSUMERS__", mapping_literal(sm_consumers))
    lean_spec = lean_spec.replace("__SM_NODE_DEPS__", deps_literal(sm_deps))
    lean_spec = lean_spec.replace("__PM_TENSOR_PRODUCERS__", mapping_literal(pm_producers))
    lean_spec = lean_spec.replace("__PM_TENSOR_CONSUMERS__", mapping_literal(pm_consumers))
    lean_spec = lean_spec.replace("__PM_NODE_DEPS__", deps_literal(pm_deps))
    lean_spec = lean_spec.replace("__SM_EXEC_PLAN__", exec_plan_literal(sm_nodes, sm_deps))
    lean_spec = lean_spec.replace("__PM_EXEC_PLAN__", exec_plan_literal(pm_nodes, pm_deps))
    sm_progress = emit_progress_lemmas("sm", sm_nodes, sm_deps, "smShapes", "smInits")
    pm_progress = emit_progress_lemmas("pm", pm_nodes, pm_deps, "pmShapes", "pmInits")
    lean_spec = lean_spec.replace("__SM_PROGRESS_LEMMAS__", sm_progress)
    lean_spec = lean_spec.replace("__PM_PROGRESS_LEMMAS__", pm_progress)

    out_concrete = Path(args.out_concrete)
    out_spec = Path(args.out_spec)
    out_concrete.write_text(dedent(lean_concrete))
    out_spec.write_text(dedent(lean_spec))
    print(f"Wrote Lean concrete graph to {out_concrete}")
    print(f"Wrote Lean symbolic spec graph to {out_spec}")


if __name__ == "__main__":
    main()
