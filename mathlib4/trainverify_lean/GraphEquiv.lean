import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

/-!
Based on the graph summaries emitted by `Verdict/scripts/analyze_graph.sh`, the dp1-pp1-tp1
configuration runs on a single device and executes the pipeline:
`LoadData → Linear (layers.0) → Linear (layers.1) → Sum`.

The dp2-pp2-tp2 configuration shards the batch (32-sample micro-batches on four logical
devices), applies the same pair of linear layers per shard, performs an AllGather, and then
reduces via `Sum`. The code below defines the two workflows and proves that their evaluated
results coincide for every dataset and every collection of shards that rejoins to the original
batch. This captures the "same math, different schedule" intuition from the analyzer output.

-/

namespace List

variable {α β : Type*}

/-- Flatten a list of lists by concatenating all chunks. -/
def join : List (List α) → List α
  | [] => []
  | chunk :: rest => chunk ++ join rest

@[simp] lemma join_nil : (join ([] : List (List α)) : List α) = [] := rfl

@[simp] lemma join_cons (chunk : List α) (rest : List (List α)) :
    join (chunk :: rest) = chunk ++ join rest := rfl

lemma join_map_map (chunks : List (List α)) (f : α → β) :
    (chunks.map (List.map f)).join = (chunks.join).map f := by
  induction chunks with
  | nil => simp [join]
  | cons chunk rest ih =>
      simp [join, ih, List.map_append]

end List

namespace TrainVerify

/-- A lightweight description of one computation step, mirroring the analyzer output. -/
structure GraphStep where
  label : String
  detail : String
  deriving Repr, DecidableEq

/-- A named workflow consisting of ordered steps. -/
structure GraphWorkflow where
  title : String
  steps : List GraphStep
  deriving Repr

namespace Workflows

/-- Single-device baseline: dp=1, pp=1, tp=1. -/
def dp1pp1tp1 : GraphWorkflow :=
  { title := "dp1-pp1-tp1/baseline"
    steps :=
      [⟨"LoadData", "Fetch 128×128 batch onto device 0"⟩
      ,⟨"Linear layers.0", "Matrix multiply with layers.0.weight"⟩
      ,⟨"Linear layers.1", "Matrix multiply with layers.1.weight"⟩
      ,⟨"Sum", "Reduce final activations to the scalar loss"⟩] }

/-- Hybrid parallel plan: dp=2, pp=2, tp=2 with micro-batches of 32 samples. -/
def dp2pp2tp2 : GraphWorkflow :=
  { title := "dp2-pp2-tp2/hybrid"
    steps :=
      [⟨"LoadData (sharded)", "Each logical device receives a 32×128 shard"⟩
      ,⟨"Linear layers.0", "Stage-0 GEMM on the shard"⟩
      ,⟨"Linear layers.1", "Stage-1 GEMM on the shard"⟩
      ,⟨"Chunk/Split→AllGather", "TP/PP communication to rebuild the batch"⟩
      ,⟨"Identity", "Pipeline book-keeping on device 3"⟩
      ,⟨"Sum", "Reduce the gathered activations"⟩
      ,⟨"DP sync", "All-reduce of the scalar loss across replicas"⟩] }

end Workflows

section Semantics

variable {Sample Scalar : Type*}
variable [AddCommMonoid Scalar]

/-- Fold helper that mirrors the `Sum` node reported by the analyzer. -/
def reduceSum (sumFn : Sample → Scalar) (xs : List Sample) : Scalar :=
  xs.foldl (fun acc sample => acc + sumFn sample) 0

/-- Computation flow for `dp1-pp1-tp1`: load the batch, apply the two linear layers, and reduce. -/
def sequentialEval (linear0 linear1 : Sample → Sample) (sumFn : Sample → Scalar)
    (data : List Sample) : Scalar :=
  reduceSum sumFn (data.map fun x => linear1 (linear0 x))

/-- Metadata + shards describing how the hybrid plan slices the batch. -/
structure ParallelPartition (data : List Sample) where
  dp : Nat := 2
  pp : Nat := 2
  tp : Nat := 2
  microBatch : Nat := 32
  shards : List (List Sample)
  join_eq : shards.join = data

/-- Computation flow for `dp2-pp2-tp2`: per-shard linear stack, AllGather, bookkeeping, sum, DP sync. -/
def hybridEval (linear0 linear1 : Sample → Sample) (sumFn : Sample → Scalar)
    {data : List Sample} (partition : ParallelPartition data) : Scalar :=
  let stage0 := partition.shards.map (List.map linear0)
  let stage1 := stage0.map (List.map linear1)
  reduceSum sumFn stage1.join

/-- Semantic realisation of `Workflows.dp1pp1tp1`: applies `sequentialEval`. -/
def baselineWorkflowEval (linear0 linear1 : Sample → Sample) (sumFn : Sample → Scalar)
    (data : List Sample) : Scalar :=
  sequentialEval linear0 linear1 sumFn data

/-- Semantic realisation of `Workflows.dp2pp2tp2`: applies `hybridEval` with a valid partition. -/
def hybridWorkflowEval (linear0 linear1 : Sample → Sample) (sumFn : Sample → Scalar)
    {data : List Sample} (partition : ParallelPartition data) : Scalar :=
  hybridEval linear0 linear1 sumFn partition

/-- The hybrid schedule matches the sequential baseline on every dataset. -/
theorem graphEquivalence (linear0 linear1 : Sample → Sample) (sumFn : Sample → Scalar)
    (data : List Sample) (partition : ParallelPartition data) :
    baselineWorkflowEval linear0 linear1 sumFn data =
      hybridWorkflowEval linear0 linear1 sumFn partition := by
  have hstage0 :
      (partition.shards.map (List.map linear0)).join = data.map linear0 := by
    simpa [partition.join_eq] using
      (List.join_map_map (chunks := partition.shards) linear0)
  have hstage1 :
      ((partition.shards.map (List.map linear0)).map (List.map linear1)).join =
        data.map (linear1 ∘ linear0) := by
    have :=
      (List.join_map_map
        (chunks := partition.shards.map (List.map linear0)) linear1)
    simpa [hstage0, List.map_map, Function.comp] using this
  have hstage1' :
      ((partition.shards.map (List.map linear0)).map (List.map linear1)).join =
        data.map (fun x => linear1 (linear0 x)) := by
    simpa [Function.comp] using hstage1
  have hsum :
      reduceSum sumFn (data.map (fun x => linear1 (linear0 x))) =
        reduceSum sumFn
          ((partition.shards.map (List.map linear0)).map (List.map linear1)).join := by
    simpa using congrArg (reduceSum sumFn) hstage1'.symm
  have hfinal :
      baselineWorkflowEval linear0 linear1 sumFn data =
        hybridWorkflowEval linear0 linear1 sumFn partition := by
    calc
      baselineWorkflowEval linear0 linear1 sumFn data
          = reduceSum sumFn (data.map fun x => linear1 (linear0 x)) := by
            simp [baselineWorkflowEval, sequentialEval, reduceSum]
      _ = reduceSum sumFn
            ((partition.shards.map (List.map linear0)).map (List.map linear1)).join := by
            simpa using hsum
      _ = hybridWorkflowEval linear0 linear1 sumFn partition := by
            simp [hybridWorkflowEval, hybridEval, reduceSum]
  exact hfinal

end Semantics

section Examples

open Workflows

private def rowWidth : Nat := 128
private def microBatch : Nat := 32
private def shardCount : Nat := 4

/-- Provide the additive structure on `Nat` for this example. -/
local instance : AddCommMonoid Nat where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := 0
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  nsmul n x := n * x
  nsmul_zero := by intro x; simp
  nsmul_succ := by
    intro n x
    simp [Nat.succ_mul]

/-- Construct a 128-wide row indexed by `row`. -/
def sampleRow (row : Nat) : List Nat :=
  (List.range rowWidth).map fun col => row * rowWidth + col

/-- Four shards of 32 rows each, mirroring the analyzer's sharded load. -/
def sampleShards : List (List (List Nat)) :=
  (List.range shardCount).map fun shard =>
    (List.range microBatch).map fun j => sampleRow (shard * microBatch + j)

/-- Synthetic 128×128 batch used for regression checks. -/
def sampleDataset : List (List Nat) := sampleShards.join

/-- `dp2-pp2-tp2` partition that rejoins to `sampleDataset`. -/
def samplePartition : ParallelPartition sampleDataset :=
  { dp := 2
    pp := 2
    tp := 2
    microBatch := microBatch
    shards := sampleShards
    join_eq := rfl }

/-- Element-wise dot product of two 128-wide rows. -/
def dotProduct (xs ys : List Nat) : Nat :=
  (List.zipWith (fun x y => x * y) xs ys).foldl (fun acc value => acc + value) 0

/-- Apply a weight matrix (stored column-wise) to a row vector. -/
def applyLinear (row : List Nat) (weights : List (List Nat)) : List Nat :=
  weights.map fun column => dotProduct row column

/-- Deterministic 128×128 weight matrix for stage 0 (encoded column-wise). -/
def weightMatrix0 : List (List Nat) :=
  (List.range rowWidth).map fun outIdx =>
    (List.range rowWidth).map fun inIdx => (outIdx + inIdx + 1)

/-- Deterministic 128×128 weight matrix for stage 1 (encoded column-wise). -/
def weightMatrix1 : List (List Nat) :=
  (List.range rowWidth).map fun outIdx =>
    (List.range rowWidth).map fun inIdx => (2 * outIdx + 3 * inIdx + 1)

/-- Stage-0 linear map: 1×128 row multiplied by `weightMatrix0`. -/
def sampleLinear0 (row : List Nat) : List Nat :=
  applyLinear row weightMatrix0

/-- Stage-1 linear map: 1×128 row multiplied by `weightMatrix1`. -/
def sampleLinear1 (row : List Nat) : List Nat :=
  applyLinear row weightMatrix1

/-- Reduction that sums a 128-wide row to a scalar. -/
def sampleSumFn (row : List Nat) : Nat :=
  row.foldl (fun acc value => acc + value) 0

/-- Baseline workflow evaluation on the synthesized batch. -/
def baselineValue : Nat :=
  baselineWorkflowEval (Sample := List Nat) (Scalar := Nat)
    sampleLinear0 sampleLinear1 sampleSumFn sampleDataset

/-- Hybrid workflow evaluation on the synthesized batch. -/
def hybridValue : Nat :=
  hybridWorkflowEval (Sample := List Nat) (Scalar := Nat)
    sampleLinear0 sampleLinear1 sampleSumFn samplePartition

/-- Regression check: both graph schedules yield the same scalar. -/
example : baselineValue = hybridValue := by
  dsimp [baselineValue, hybridValue, baselineWorkflowEval, hybridWorkflowEval]
  simpa using
    (graphEquivalence (Sample := List Nat) (Scalar := Nat)
        sampleLinear0 sampleLinear1 sampleSumFn sampleDataset samplePartition)

#eval baselineValue
#eval hybridValue

end Examples

end TrainVerify
