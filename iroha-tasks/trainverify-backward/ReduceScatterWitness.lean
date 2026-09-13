import denote.SourceReduceScatterRead

/-!
K=3, noncontiguous world ranks [0,2,5], selected world rank 2 / local index 1.
Three distinct, position-dependent full [2,6] contributions are reduced and
scattered on dim 1. The actual checked run returns a [2,2] middle chunk, not
the rank-2 chunk, a whole-tensor sum, an average, or an identity result.

Parameter well-formedness / ordered attachment / equal shapes / divisibility
are proved separately: the current ReduceScatter dispatcher does not check all
of them. No output equation or shape is a premise of the successful caller.
-/
namespace TrainVerify.Denote.SourceReduceScatterReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  {rank := 2, op := "OpName.ReduceScatterPrim", ins := [10, 20, 30], outs := [40], params := [1]}
def graph : GraphDecl := {numRanks := 6, nodes := [selected]}
def requests : List InputRequest := [(selected, none)]
def scope : NodeDecl → GroupScopedEval.Request := fun _ => .group (some [0, 2, 5])
def peer (_ : NodeDecl) (rank : Nat) : Tid := if rank = 0 then 10 else if rank = 2 then 20 else 30
def sample (base : Nat) : Tensor := Tensor.mkShape [2, 6] (fun j => ((base + j.val : Nat) : Scalar))
def initial (tid : Tid) : Tensor := sample (if tid = 10 then 2 else if tid = 20 then 7 else 11)
def finalStore : Store := GroupScopedEval.localStep [0, 2, 5] initial selected

/-- These source-fidelity conditions really are simultaneously satisfiable. -/
theorem parameters_satisfiable : ∃ rs : List Nat, ∃ dim : Nat,
    scope selected = .group (some rs) ∧ selected.params = [dim] ∧
    GroupScopedEval.WellFormed graph.numRanks selected.rank rs ∧
    selected.ins = rs.map (peer selected) ∧
    selected.ins.length = rs.length ∧
    rs.idxOf selected.rank = 1 ∧
    (∀ tid ∈ selected.ins, (initial tid).shape = [2, 6]) ∧
    GroupScopedEval.ChunkInput rs dim (tensorSum (selected.ins.map initial)) := by
  refine ⟨[0, 2, 5], 1, rfl, rfl, by decide, rfl, rfl, by decide, ?_, ?_⟩
  · intro tid htid
    rfl
  · unfold GroupScopedEval.ChunkInput
    exact ⟨by decide, by decide, by decide⟩

theorem step_success :
    stepWithInputs graph (scope selected) (peer selected) initial selected none = some finalStore := by
  rw [stepWithInputs_ordinary graph _ _ initial selected (by decide)]
  change step graph (.group (some [0, 2, 5])) (peer selected) initial selected = some finalStore
  rw [step_group graph _ _ initial selected (by decide) (by decide)]
  exact GroupScopedEval.step_scoped graph initial selected [0, 2, 5] (by decide) (by rfl)

theorem run_success :
    runWithInputs graph scope peer graph.nodes (some requests) (some initial) = some finalStore := by
  change (if InputSchedule graph.nodes requests then
    runUsing (fun row a => stepWithInputs graph (scope row.1) (peer row.1) a row.1 row.2)
      requests (some initial) else none) = some finalStore
  rw [if_pos (by decide)]
  exact step_success

/-- The caller consumes an actual successful run, not a stipulated step value. -/
theorem caller_read (s t : Store)
    (hrun : runWithInputs graph scope peer graph.nodes (some requests) (some s) = some t) :
    t 40 = chunkPrimDimN 1 3 1 (tensorSum ([10, 20, 30].map t)) := by
  exact SourceReduceScatterRead.reduceScatter_value_of_split graph scope peer graph.nodes
    requests [] [] selected 2 [0, 2, 5] [10, 20, 30] 40 1 s t
    rfl rfl rfl (by decide) hrun

theorem final_read :
    finalStore 40 = chunkPrimDimN 1 3 1 (tensorSum ([10, 20, 30].map finalStore)) :=
  caller_read initial finalStore run_success

theorem frame (tid : Tid) (h : tid ≠ 40) : finalStore tid = initial tid := by
  apply GroupScopedEval.localStep_skip [0, 2, 5] initial selected tid
  intro hm
  exact h (List.mem_singleton.mp hm)

theorem output_shape : (finalStore 40).shape = [2, 2] := by
  rw [final_read]
  change (chunkPrimDimN 1 3 1 (tensorSum [finalStore 10, finalStore 20, finalStore 30])).shape = [2, 2]
  rw [frame 10 (by decide), frame 20 (by decide), frame 30 (by decide)]
  rfl

-- Row-major source indices of the first and last output are 2 and 9.
theorem output_zero : valAt (finalStore 40) 0 = 26 := by
  rw [final_read]
  change valAt (chunkPrimDimN 1 3 1 (tensorSum [finalStore 10, finalStore 20, finalStore 30])) 0 = 26
  rw [frame 10 (by decide), frame 20 (by decide), frame 30 (by decide)]
  change (0 : Scalar) + ((2 + 2 : Nat) : Scalar) + ((7 + 2 : Nat) : Scalar) + ((11 + 2 : Nat) : Scalar) = 26
  norm_num

theorem output_last : valAt (finalStore 40) 3 = 47 := by
  rw [final_read]
  change valAt (chunkPrimDimN 1 3 1 (tensorSum [finalStore 10, finalStore 20, finalStore 30])) 3 = 47
  rw [frame 10 (by decide), frame 20 (by decide), frame 30 (by decide)]
  change (0 : Scalar) + ((2 + 9 : Nat) : Scalar) + ((7 + 9 : Nat) : Scalar) + ((11 + 9 : Nat) : Scalar) = 47
  norm_num

theorem output_nonconstant : valAt (finalStore 40) 0 ≠ valAt (finalStore 40) 3 := by
  rw [output_zero, output_last]
  norm_num

/-- Explicit successful-run witness with shape, values, and same-final-Store read. -/
theorem caller_nonvacuous : ∃ s t : Store,
    runWithInputs graph scope peer graph.nodes (some requests) (some s) = some t ∧
    t 40 = chunkPrimDimN 1 3 1 (tensorSum ([10, 20, 30].map t)) ∧
    (t 40).shape = [2, 2] ∧
    valAt (t 40) 0 = 26 ∧ valAt (t 40) 3 = 47 :=
  ⟨initial, finalStore, run_success, final_read, output_shape, output_zero, output_last⟩

#print axioms parameters_satisfiable
#print axioms step_success
#print axioms run_success
#print axioms caller_read
#print axioms final_read
#print axioms frame
#print axioms output_shape
#print axioms output_zero
#print axioms output_last
#print axioms output_nonconstant
#print axioms caller_nonvacuous
end
end TrainVerify.Denote.SourceReduceScatterReadWitness
