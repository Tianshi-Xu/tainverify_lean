"""Load NNScaler graphs and emit a Lean4 interpreter that replays the graph.

This version constructs Lean data structures for every node/tensor pulled from
the serialized SM/PM graphs, then interprets them (with predefined semantics
for DATALOADER, FW/BW linear, sum, chunk, all-reduce, all-gather). No manual
graph sketching: changing the input pickle files changes the generated Lean
program.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import sys
from textwrap import dedent
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "mathlib4" / "trainverify_lean" / "equal.lean"


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


def load_graphs_from_disk():
    sys.path.extend([str(ROOT), str(ROOT / "genmodel"), str(ROOT / "Verdict")])
    from analyze_graph import load_graphs, prepare  # type: ignore
    from verdict.config import Config  # type: ignore

    Config.update_from_args([])
    prepare(Config)

    sm = "./genmodel/mgeners/mlp_mgener_dp1_pp1_tp1_nm1_gbs128_dim128_ly1.pkl"
    pm = "./genmodel/mgeners/mlp_mgener_dp1_pp1_tp8_nm1_gbs128_dim128_ly1.pkl"
    return load_graphs(sm, pm)


def extract(graph) -> Tuple[List[NodeMeta], Dict[int, TensorMeta]]:
    tensors: Dict[int, TensorMeta] = {}
    nodes: List[NodeMeta] = []
    for node in graph.nodes():
        op = str(graph.node_opname(node))
        kwargs = dict(graph.node_kwargs(node))
        ins = []
        outs = []
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


def emit_tensors(name: str, tensors: Dict[int, TensorMeta]) -> str:
    items = []
    for tid, meta in sorted(tensors.items()):
        items.append(f"({tid}, {lean_shape(meta.shape)}, {'true' if meta.initialized else 'false'})")
    body = "[" + ", ".join(items) + "]"
    return f"def {name} : List (Nat × List Nat × Bool) := {body}\n"


def op_ctor(op: str, kwargs: Dict) -> str:
    if "DATALOADER" in op:
        return "Op.dataloader"
    if "FW_linear" in op:
        return "Op.fwLinear"
    if "BW_linear" in op:
        return "Op.bwLinear"
    if "FW_sum" in op:
        return "Op.fwSum"
    if "BW_sum" in op:
        return "Op.bwSum"
    if "ChunkPrim" in op:
        dim = int(kwargs.get("dim", 1))
        idx = int(kwargs.get("__collective_idx", 0)) if "__collective_idx" in kwargs else 0
        return f"Op.chunk {dim} {idx}"
    if "AllGatherPrim" in op:
        dim = int(kwargs.get("dim", 0))
        return f"Op.allGather {dim}"
    if "AllReducePrim" in op:
        return "Op.allReduce"
    return "Op.unknown"


def emit_nodes(name: str, nodes: List[NodeMeta]) -> str:
    parts = []
    for n in nodes:
        op = op_ctor(n.op, n.kwargs)
        ins = lean_list_int(n.inputs)
        outs = lean_list_int(n.outputs)
        parts.append(f"{{ op := {op}, inputs := {ins}, outputs := {outs} }}")
    body = "[" + ",\n  ".join(parts) + "]"
    return f"def {name} : List Node := {body}\n"


def main() -> None:
    g_single, g_parallel = load_graphs_from_disk()
    sm_nodes, sm_tensors_raw = extract(g_single)
    pm_nodes, pm_tensors = extract(g_parallel)

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
    obs_tid = common_tids[0] if common_tids else 0

    # identify SM full weight and PM sharded weights (initialized matrices)
    sm_weight_tid = min([tid for tid, meta in sm_tensors.items() if meta.initialized and len(meta.shape) == 2] or [0])
    pm_inits = [(tid, meta.shape) for tid, meta in pm_tensors.items() if meta.initialized and len(meta.shape) == 2]
    shard_width = min([s[1] for _, s in pm_inits] or [1])
    pm_weight_tids = [tid for tid, shape in pm_inits if shape[1] == shard_width]
    pm_weight_tids.sort()
    pm_chunk = shard_width

    template = """
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

    lean = template.replace("__TENSORS_SM__", emit_tensors("tensorShapesSM", sm_tensors))
    lean = lean.replace("__TENSORS_PM__", emit_tensors("tensorShapesPM", pm_tensors))
    lean = lean.replace("__NODES_SM__", emit_nodes("smNodes", sm_nodes))
    lean = lean.replace("__NODES_PM__", emit_nodes("pmNodes", pm_nodes))
    lean = lean.replace("__OBS_TID__", str(obs_tid))
    lean = lean.replace("__SM_W_TID__", str(sm_weight_tid))
    pm_w_pairs = "[" + ", ".join(f"({tid}, {idx})" for idx, tid in enumerate(pm_weight_tids)) + "]"
    lean = lean.replace("__PM_W_TIDS__", pm_w_pairs)
    lean = lean.replace("__PM_CHUNK__", str(pm_chunk))

    OUT.write_text(dedent(lean))
    print(f"Wrote Lean graph comparison to {OUT}")


if __name__ == "__main__":
    main()
