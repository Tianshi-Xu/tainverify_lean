import denote.SourceBWMultirefRead

/-!
Edit-only candidate; serial Lean/kernel and axiom audits belong to the parent.
Three distinct nonzero, nonconstant contributions at nonconsecutive source IDs
[41,907,113], unrelated to rank 2. The suffix really executes and writes another
output, while preserving every selected input and the selected output. This is
an actual checked source run, not an output-equation assumption or a new eval.
-/
namespace TrainVerify.Denote.MultirefReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

private def inputs : List Tid := [41, 907, 113]
private def selected : NodeDecl :=
  { rank := 2, op := "OpName.BW_multiref", ins := inputs, outs := [509], params := [] }
private def suffix : NodeDecl :=
  { rank := 2, op := "OpName.BW_multiref", ins := [509], outs := [1301], params := [] }
private def nodes : List NodeDecl := [selected, suffix]
private def requests : List InputRequest := [(selected, none), (suffix, none)]
private def g : GraphDecl := { numRanks := 4, nodes := nodes }
private def scope : NodeDecl → GroupScopedEval.Request := fun _ => .global
private def peer : NodeDecl → Nat → Tid := fun _ _ => 0
private def finalStore (s : Store) : Store := applyNode g (applyNode g s selected) suffix

private def gradA : Tensor := Tensor.mkShape [2] (fun i => if i.1 = 0 then 1 else 2)
private def gradB : Tensor := Tensor.mkShape [2] (fun i => if i.1 = 0 then 3 else 5)
private def gradC : Tensor := Tensor.mkShape [2] (fun i => if i.1 = 0 then 7 else 11)
private def initial : Store := fun tid =>
  if tid = 41 then gradA else if tid = 907 then gradB else
  if tid = 113 then gradC else zeroTensor []

theorem schedule_valid : InputSchedule nodes requests := by decide

/-- Complete input liveness includes the selected node and the nonempty suffix. -/
theorem inputs_nonwrites :
    ∀ tid ∈ inputs, ∀ row ∈ (selected, none) :: ([(suffix, none)] : List InputRequest), tid ∉ row.1.outs := by
  decide

theorem run_success (s : Store) :
    runWithInputs g scope peer nodes (some requests) (some s) = some (finalStore s) := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some (finalStore s)
  rw [if_pos schedule_valid]
  change (stepWithInputs g .global (peer selected) s selected none).bind
    (fun a => stepWithInputs g .global (peer suffix) a suffix none) = _
  rw [stepWithInputs_ordinary g .global (peer selected) s selected (by decide),
    step_global g (peer selected) s selected (by decide)]
  change stepWithInputs g .global (peer suffix) (applyNode g s selected) suffix none = _
  rw [stepWithInputs_ordinary g .global (peer suffix) (applyNode g s selected) suffix
    (by decide)]
  exact step_global g (peer suffix) (applyNode g s selected) suffix (by decide)

/-- Arbitrary final Store, constrained only by the original successful run. -/
theorem caller_read (s t : Store)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t 509 = tensorSum (inputs.map t) :=
  SourceBWMultirefRead.bw_multiref_value_of_split
    g scope peer nodes requests [] [(suffix, none)] selected 2 inputs 509 s t
    rfl rfl rfl inputs_nonwrites hrun

theorem same_final_read (s : Store) :
    (finalStore s) 509 = tensorSum (inputs.map (finalStore s)) :=
  caller_read s (finalStore s) (run_success s)

private theorem input_preserved (s : Store) (tid : Tid) (ht : tid ∈ inputs) :
    (finalStore s) tid = s tid := by
  change applyNode g (applyNode g s selected) suffix tid = s tid
  rw [applyNode_skip g (applyNode g s selected) suffix tid
    (inputs_nonwrites tid ht (suffix, none)
      (List.mem_cons_of_mem (selected, none) List.mem_cons_self))]
  exact applyNode_skip g s selected tid
    (inputs_nonwrites tid ht (selected, none) List.mem_cons_self)

theorem final_inputs :
    (finalStore initial) 41 = gradA ∧ (finalStore initial) 907 = gradB ∧
    (finalStore initial) 113 = gradC := by
  refine ⟨?_, ?_, ?_⟩
  · exact input_preserved initial 41 (by decide)
  · exact input_preserved initial 907 (by decide)
  · exact input_preserved initial 113 (by decide)

theorem concrete_sum :
    (finalStore initial) 509 = tensorSum [gradA, gradB, gradC] := by
  have h := same_final_read initial
  change (finalStore initial) 509 =
    tensorSum [(finalStore initial) 41, (finalStore initial) 907, (finalStore initial) 113] at h
  rw [final_inputs.1, final_inputs.2.1, final_inputs.2.2] at h
  exact h

theorem output_shape : ((finalStore initial) 509).shape = [2] := by
  rw [concrete_sum]
  exact tensorSum_shape gradA [gradB, gradC]

theorem sum_values :
    valAt ((finalStore initial) 509) 0 = 11 ∧
    valAt ((finalStore initial) 509) 1 = 18 := by
  rw [concrete_sum]
  change (0 + (1 : Scalar) + 3 + 7 = 11) ∧ (0 + (2 : Scalar) + 5 + 11 = 18)
  norm_num

/-- Each entire contribution is nonzero, not merely the combined output. -/
theorem contributions_nonzero :
    ∀ x ∈ [gradA, gradB, gradC], ∀ i, i < prodShape x.shape → valAt x i ≠ 0 := by
  intro x hx i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · rw [valAt_of_lt _ _ hi]
    change (if i = 0 then (1 : Scalar) else 2) ≠ 0
    split_ifs <;> norm_num
  · rw [valAt_of_lt _ _ hi]
    change (if i = 0 then (3 : Scalar) else 5) ≠ 0
    split_ifs <;> norm_num
  · rw [valAt_of_lt _ _ hi]
    change (if i = 0 then (7 : Scalar) else 11) ≠ 0
    split_ifs <;> norm_num

theorem contributions_different :
    valAt gradA 0 ≠ valAt gradB 0 ∧ valAt gradA 0 ≠ valAt gradC 0 ∧
    valAt gradB 0 ≠ valAt gradC 0 := by
  change (1 : Scalar) ≠ 3 ∧ (1 : Scalar) ≠ 7 ∧ (3 : Scalar) ≠ 7
  norm_num

theorem contributions_nonconstant :
    valAt gradA 0 ≠ valAt gradA 1 ∧ valAt gradB 0 ≠ valAt gradB 1 ∧
    valAt gradC 0 ≠ valAt gradC 1 := by
  change (1 : Scalar) ≠ 2 ∧ (3 : Scalar) ≠ 5 ∧ (7 : Scalar) ≠ 11
  norm_num

/-- Dropping the middle original contribution is observably wrong, even though
its two retained tensors still have the correct output shape. -/
theorem drop_contribution_wrong :
    (finalStore initial) 509 ≠
      tensorSum [(finalStore initial) 41, (finalStore initial) 113] := by
  intro h
  have h0 := congrArg (fun x : Tensor => valAt x 0) h
  rw [sum_values.1, final_inputs.1, final_inputs.2.2] at h0
  change (11 : Scalar) = 0 + 1 + 7 at h0
  norm_num at h0

/-- A inhabited contract including the checked run, full input nonwrites,
SAME-final-Store sum, complete output shape and two nonzero output values. -/
theorem caller_nonvacuous :
    ∃ s t : Store,
      s 41 = gradA ∧ s 907 = gradB ∧ s 113 = gradC ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      (∀ tid ∈ inputs, ∀ row ∈ (selected, none) :: ([(suffix, none)] : List InputRequest), tid ∉ row.1.outs) ∧
      t 41 = gradA ∧ t 907 = gradB ∧ t 113 = gradC ∧
      t 509 = tensorSum (inputs.map t) ∧ (t 509).shape = [2] ∧
      valAt (t 509) 0 = 11 ∧ valAt (t 509) 1 = 18 ∧
      t 509 ≠ tensorSum [t 41, t 113] := by
  exact ⟨initial, finalStore initial, rfl, rfl, rfl, run_success initial,
    inputs_nonwrites, final_inputs.1, final_inputs.2.1, final_inputs.2.2,
    same_final_read initial, output_shape, sum_values.1, sum_values.2,
    drop_contribution_wrong⟩

#print axioms schedule_valid
#print axioms inputs_nonwrites
#print axioms run_success
#print axioms caller_read
#print axioms same_final_read
#print axioms final_inputs
#print axioms concrete_sum
#print axioms output_shape
#print axioms sum_values
#print axioms contributions_nonzero
#print axioms contributions_different
#print axioms contributions_nonconstant
#print axioms drop_contribution_wrong
#print axioms caller_nonvacuous
end
end TrainVerify.Denote.MultirefReadWitness
