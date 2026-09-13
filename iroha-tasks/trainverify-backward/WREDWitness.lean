import denote.SourceWREDRead

namespace TrainVerify.Denote.SourceWREDReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  {rank := 2, op := "OpName.CROSS_DP_WRED", ins := [10, 20, 30], outs := [40], params := []}
def graph : GraphDecl := {numRanks := 6, nodes := [selected]}
def requests : List InputRequest := [(selected, none)]
def scope : NodeDecl → GroupScopedEval.Request := fun _ => .group (some [0, 2, 5])
def peer (_ : NodeDecl) (rank : Nat) : Tid := if rank = 0 then 10 else if rank = 2 then 20 else 30
-- Distinct gradients and position-dependent values, not a constant/symmetric test.
def sample (base : Nat) : Tensor := Tensor.mkShape [2, 3] (fun j => ((base + j.val : Nat) : Scalar))
def initial (tid : Tid) : Tensor := sample (if tid = 10 then 2 else if tid = 20 then 7 else 11)
def finalStore : Store := applyNode graph initial selected

theorem contract : WredContract [0, 2, 5] (peer selected) initial selected := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, ?_⟩
  intro tid htid
  rfl

theorem step_success : stepWithInputs graph (scope selected) (peer selected) initial selected none = some finalStore := by
  rw [stepWithInputs_ordinary graph _ _ initial selected (by decide)]
  change step graph (.group (some [0, 2, 5])) (peer selected) initial selected = some finalStore
  rw [step_wred graph _ _ initial selected rfl]
  exact if_pos ⟨by decide, contract⟩

theorem run_success :
    runWithInputs graph scope peer graph.nodes (some requests) (some initial) = some finalStore := by
  change (if InputSchedule graph.nodes requests then
    runUsing (fun row a => stepWithInputs graph (scope row.1) (peer row.1) a row.1 row.2)
      requests (some initial) else none) = some finalStore
  rw [if_pos (by decide)]
  exact step_success

theorem final_read : finalStore 40 = cross_dp_wred ([10, 20, 30].map finalStore) := by
  exact SourceWREDRead.wred_value_of_split graph scope peer graph.nodes requests [] []
    selected 2 [0, 2, 5] [10, 20, 30] 40 initial finalStore rfl rfl rfl (by decide) run_success

theorem frame (tid : Tid) (h : tid ≠ 40) : finalStore tid = initial tid := by
  apply applyNode_eq_of_not_mem_outs graph initial selected tid
  intro hm
  exact h (List.mem_singleton.mp hm)

theorem output_shape : (finalStore 40).shape = [2, 3] := by
  rw [final_read]
  change (finalStore 10).shape = [2, 3]
  rw [frame 10 (by decide)]
  rfl

theorem output_zero : valAt (finalStore 40) 0 = 20 := by
  rw [final_read]
  change valAt (cross_dp_wred [finalStore 10, finalStore 20, finalStore 30]) 0 = 20
  rw [frame 10 (by decide), frame 20 (by decide), frame 30 (by decide)]
  change (0 : Scalar) + 2 + 7 + 11 = 20
  norm_num

theorem output_last : valAt (finalStore 40) 5 = 35 := by
  rw [final_read]
  change valAt (cross_dp_wred [finalStore 10, finalStore 20, finalStore 30]) 5 = 35
  rw [frame 10 (by decide), frame 20 (by decide), frame 30 (by decide)]
  change (0 : Scalar) + ((2 + 5 : Nat) : Scalar) + ((7 + 5 : Nat) : Scalar) + ((11 + 5 : Nat) : Scalar) = 35
  norm_num

theorem caller_nonvacuous : ∃ s t : Store,
    runWithInputs graph scope peer graph.nodes (some requests) (some s) = some t ∧
    t 40 = cross_dp_wred ([10, 20, 30].map t) ∧
    (t 40).shape = [2, 3] ∧
    valAt (t 40) 0 = 20 ∧ valAt (t 40) 5 = 35 :=
  ⟨initial, finalStore, run_success, final_read, output_shape, output_zero, output_last⟩

#print axioms contract
#print axioms step_success
#print axioms run_success
#print axioms final_read
#print axioms frame
#print axioms output_shape
#print axioms output_zero
#print axioms output_last
#print axioms caller_nonvacuous
end
end TrainVerify.Denote.SourceWREDReadWitness
