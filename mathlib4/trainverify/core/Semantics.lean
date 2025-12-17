/-
Generic small-step execution semantics for graphs.
The semantics is parameterised by an operation interpreter so that the library can
be reused for different concrete runtimes.
-/

import trainverify.core.Model
import trainverify.core.Primitives

open Std

universe u

namespace TrainVerify

variable {α : Type u}

/-- Shapes are tracked as lists of dimensions; the semantics stays agnostic about rank. -/
abbrev ShapeMap := Std.HashMap Nat (List Nat)

/-- Initialise flags tell the runtime whether a tensor should be fetched from the environment. -/
abbrev InitMap := Std.HashMap Nat Bool

/-- The execution environment supplies concrete tensors for ids marked as initialised. -/
structure Env (α : Type u) where
  get : Nat → Mat α

namespace Env

@[simp]
lemma get_def {α : Type u} (ρ : Env α) (tid : Nat) : ρ.get tid = ρ.get tid := rfl

end Env

/-- Determine whether all tensors in `tids` already exist in the store. -/
def outputsExist (tids : List Nat) (st : Store α) : Bool :=
  tids.all (fun t => st.contains t)

/-- Check that every input is ready either because it is present or marked initialised. -/
def inputsReady (inits : InitMap) (tids : List Nat) (st : Store α) : Bool :=
  tids.all (fun t => st.contains t || inits.getD t false)

/-- Fetch a tensor from the store, falling back to the environment or zeros. -/
def fetchTensor [Semiring α]
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (tid : Nat) (st : Store α) : Mat α × Store α :=
  match st.get? tid with
  | some v => (v, st)
  | none =>
      let shp := shapes.getD tid []
      let init := inits.getD tid false
      let v := if init then env.get tid else zerosLike shp
      (v, st.insert tid v)

/-- Fetch a list of tensors in order, threading the store updates. -/
def fetchMany [Semiring α]
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (tids : List Nat) (st : Store α) : List (Mat α) × Store α :=
  tids.foldl
    (fun (acc, store) tid =>
      let (t, store) := fetchTensor env shapes inits tid store
      (acc ++ [t], store))
    ([], st)

/-- Concrete semantics for the baseline set of operators used by TrainVerify. -/
def evalStandard [Semiring α]
    (op : Op) (inputs outputs : List Nat)
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (st : Store α) : Store α :=
  if outputsExist outputs st then st else
  match op with
  | Op.dataloader =>
      match outputs with
      | [] => st
      | out :: _ => st.insertTensor out (env.get out)
  | Op.fwLinear =>
      if ¬ inputsReady inits inputs st then st else
      let xId := inputs.getD 0 0
      let wId := inputs.getD 1 0
      let outId := outputs.getD 0 0
      let (x, st) := fetchTensor env shapes inits xId st
      let (w, st) := fetchTensor env shapes inits wId st
      st.insertTensor outId (matmul x (transpose w))
  | Op.bwLinear =>
      if ¬ inputsReady inits inputs st then st else
      let goId := inputs.getD 0 0
      let xId := inputs.getD 1 0
      let wId := inputs.getD 2 0
      let gxId := outputs.getD 0 0
      let gwId := outputs.getD 1 0
      let (go, st) := fetchTensor env shapes inits goId st
      let (x, st) := fetchTensor env shapes inits xId st
      let (w, st) := fetchTensor env shapes inits wId st
      let gx := matmul go w
      let gw := matmul (transpose x) go
      let st := st.insertTensor gxId gx
      st.insertTensor gwId gw
  | Op.fwSum =>
      if ¬ inputsReady inits inputs st then st else
      let xId := inputs.getD 0 0
      let outId := outputs.getD 0 0
      let (x, st) := fetchTensor env shapes inits xId st
      st.insertTensor outId [[sumAll x]]
  | Op.bwSum =>
      if ¬ inputsReady inits inputs st then st else
      let gId := inputs.getD 0 0
      let xId := inputs.getD 1 0
      let outId := outputs.getD 0 0
      let (g, st) := fetchTensor env shapes inits gId st
      let (x, st) := fetchTensor env shapes inits xId st
      let scalar := match g.head? with
        | some row => row.headD 0
        | none => 0
      let gx := x.map (fun row => row.map (fun _ => scalar))
      st.insertTensor outId gx
  | Op.chunk dim idx =>
      if ¬ inputsReady inits inputs st then st else
      let srcId := inputs.getD 0 0
      let outId := outputs.getD 0 0
      let (src, st) := fetchTensor env shapes inits srcId st
      let shpOut := shapes.getD outId []
      let size :=
        if shpOut.length = 2 then
          if dim = 0 then shpOut.getD 0 0 else shpOut.getD 1 0
        else if shpOut.length = 1 then shpOut.getD 0 0 else 0
      let start := idx * size
      let part := chunkBy src dim start size
      st.insertTensor outId part
  | Op.allGather dim =>
      if ¬ inputsReady inits inputs st then st else
      let (parts, st) := fetchMany env shapes inits inputs st
      let outId := outputs.getD 0 0
      st.insertTensor outId (gatherBy dim parts)
  | Op.allReduce =>
      if ¬ inputsReady inits inputs st then st else
      let (parts, st) := fetchMany env shapes inits inputs st
      let outId := outputs.getD 0 0
      st.insertTensor outId (allReduce parts)
  | Op.custom _ => st

/-- Specification of how to execute an operation. -/
structure OpSpec (α : Type u) where
  /-- Evaluate the operation, producing an updated store. -/
  eval : Op → List Nat → List Nat → Env α → ShapeMap → InitMap → Store α → Store α

/-- Default operation interpreter used by the semantic library. -/
def standardOps [Semiring α] : OpSpec α where
  eval := evalStandard

/-- Runtime configuration shared by all nodes. -/
structure Runtime (α : Type u) where
  env : Env α
  shapes : ShapeMap
  inits : InitMap
  ops : OpSpec α

/-- Convenience constructor for runtimes that use the built-in operation semantics. -/
def Runtime.mkStandard [Semiring α]
    (env : Env α) (shapes : ShapeMap) (inits : InitMap) : Runtime α :=
  { env, shapes, inits, ops := standardOps }

namespace Runtime

variable (cfg : Runtime α)

/-- Execute a single node using the ambient operation interpreter. -/
@[simp]
def runNode (n : Node) (st : Store α) : Store α :=
  cfg.ops.eval n.op n.inputs n.outputs cfg.env cfg.shapes cfg.inits st

/-- Execute a graph by folding across all nodes once. -/
@[simp]
def runOnce (g : Graph) (st : Store α) : Store α :=
  g.foldl (fun acc n => cfg.runNode n acc) st

/-- Execute the graph repeatedly until no progress occurs or fuel runs out. -/
@[simp]
def runGraph (g : Graph) : Nat → Store α → Store α
  | 0, st => st
  | Nat.succ fuel, st =>
      let (st', progressed) := g.foldl
        (fun (acc, prog) n =>
          let stNew := cfg.runNode n acc
          let prog' := prog || (¬ outputsExist n.outputs acc) && outputsExist n.outputs stNew
          (stNew, prog'))
        (st, false)
      if progressed then
        runGraph g fuel st'
      else
        st'

@[simp]
def runGraphInit (g : Graph) (fuel : Nat) : Store α :=
  cfg.runGraph g fuel {}

termination_by runGraph cfg g fuel st => fuel
decreasing_by
  simp_wf

end Runtime

end TrainVerify
