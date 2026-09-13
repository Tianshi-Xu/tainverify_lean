import denote.SourceBWLinearRead

/-!
Source-read witness. The parent replayed the RED body without the new import,
then kernel-checked the helper and unchanged GREEN caller contracts serially.
For a RED replay, replace only the final import `denote.SourceBWLinearRead` with
`denote.SourceValueRead` in a separate probe file, with no candidate import.
Expected RED: unknown SourceBWLinearRead.bw_linear_dx_value_of_split and
SourceBWLinearRead.bw_linear_dw_value_of_split (not an import/cache failure).
GREEN: freshly build the candidate and elaborate this witness body.
Every theorem below has its own axiom audit. No native_decide or tensor-output
hypothesis is used. This is a conditional source-read test, not a capture or
whole-model backward-equivalence certificate.
-/
namespace TrainVerify.Denote.SourceBWLinearReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

-- Both sides of the selected occurrence are nonempty, and source TID order
-- is deliberately not sorted. The strict suffix reads the selected dX.
def prefixNode : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [20, 30], outs := [90], params := [] }
def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [10, 20, 30], outs := [50, 40], params := [] }
def suffixNode : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [50, 30], outs := [80], params := [] }
def nodes : List NodeDecl := [prefixNode, selected, suffixNode]
def requests : List InputRequest := [(prefixNode, none), (selected, none), (suffixNode, none)]
def scope : NodeDecl → GroupScopedEval.Request := fun _ => .global
def peer : NodeDecl → Nat → Tid := fun _ _ => 0
def finalStore (g : GraphDecl) (s : Store) : Store :=
  applyNode g (applyNode g (applyNode g s prefixNode) selected) suffixNode

theorem schedule_valid : InputSchedule nodes requests := by decide

theorem ordinary_step (g : GraphDecl) (a : Store) (n : NodeDecl)
    (hloader : n.op ≠ "OpName.DATALOADER") (hop : ordinary n.op = true) :
    stepWithInputs g (scope n) (peer n) a n none = some (applyNode g a n) := by
  rw [stepWithInputs_ordinary g (scope n) (peer n) a n hloader]
  exact step_global g (peer n) a n hop

theorem run_success (g : GraphDecl) (s : Store) :
    runWithInputs g scope peer nodes (some requests) (some s) = some (finalStore g s) := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some (finalStore g s)
  rw [if_pos schedule_valid]
  have hp (a : Store) := ordinary_step g a prefixNode (by decide) (by decide)
  have hb (a : Store) := ordinary_step g a selected (by decide) (by decide)
  have hq (a : Store) := ordinary_step g a suffixNode (by decide) (by decide)
  change ((stepWithInputs g (scope prefixNode) (peer prefixNode) s prefixNode none).bind
    (fun a => stepWithInputs g (scope selected) (peer selected) a selected none)).bind
    (fun a => stepWithInputs g (scope suffixNode) (peer suffixNode) a suffixNode none) = _
  simp only [hp, hb, hq, Option.bind_some]
  rfl

theorem dx_read (g : GraphDecl) (s : Store) :
    (finalStore g s) 50 =
      (bw_linear ((finalStore g s) 10) ((finalStore g s) 20) ((finalStore g s) 30)).1 := by
  exact SourceBWLinearRead.bw_linear_dx_value_of_split g scope peer nodes requests
    [(prefixNode, none)] [(suffixNode, none)] selected 0 10 20 30 50 40
    s (finalStore g s) rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (run_success g s)

theorem dw_read (g : GraphDecl) (s : Store) :
    (finalStore g s) 40 =
      (bw_linear ((finalStore g s) 10) ((finalStore g s) 20) ((finalStore g s) 30)).2 := by
  exact SourceBWLinearRead.bw_linear_dw_value_of_split g scope peer nodes requests
    [(prefixNode, none)] [(suffixNode, none)] selected 0 10 20 30 50 40
    s (finalStore g s) rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (run_success g s)

-- Non-symmetric, nonzero compatible tensors: dy=[2,3,5], x=[2,3,7], w=[5,7].
def grad : Tensor := { shape := [2, 3, 5], val := fun _ => 1 }
def input : Tensor := { shape := [2, 3, 7], val := fun _ => 2 }
def weight : Tensor := { shape := [5, 7], val := fun _ => 3 }
def initial : Store := fun tid =>
  if tid = 10 then grad else if tid = 20 then input else if tid = 30 then weight
  else zeroTensor []

theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      (s 10).shape = [2, 3, 5] ∧ (s 20).shape = [2, 3, 7] ∧ (s 30).shape = [5, 7] ∧
      valAt (s 10) 0 = 1 ∧ valAt (s 20) 0 = 2 ∧ valAt (s 30) 0 = 3 ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 50 = (bw_linear (t 10) (t 20) (t 30)).1 ∧
      t 40 = (bw_linear (t 10) (t 20) (t 30)).2 := by
  refine ⟨initial, finalStore g initial, rfl, rfl, rfl, ?_, ?_, ?_,
    run_success g initial, dx_read g initial, dw_read g initial⟩
  · rw [valAt_of_lt (initial 10) 0 (by decide)]
    rfl
  · rw [valAt_of_lt (initial 20) 0 (by decide)]
    rfl
  · rw [valAt_of_lt (initial 30) 0 (by decide)]
    rfl

-- Aliased outputs must not be admitted by the checked original schedule.
theorem aliased_outputs_rejected :
    ¬ InputSchedule
      [{ rank := 0, op := "OpName.BW_linear", ins := [10, 20, 30], outs := [50, 50], params := [] }]
      [({ rank := 0, op := "OpName.BW_linear", ins := [10, 20, 30], outs := [50, 50], params := [] }, none)] := by
  decide

#print axioms schedule_valid
#print axioms ordinary_step
#print axioms run_success
#print axioms dx_read
#print axioms dw_read
#print axioms caller_nonvacuous
#print axioms aliased_outputs_rejected
end
end TrainVerify.Denote.SourceBWLinearReadWitness
