import denote.SourceBWDivRead

/-! A positive exact scalar denominator with nonconstant, nonzero saved/cotangent
inputs and derivative values in one successful original checked run. -/
namespace TrainVerify.Denote.SourceBWDivReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_div", ins := [10, 20], outs := [50], params := [4] }
def nodes : List NodeDecl := [selected]
def requests : List InputRequest := [(selected, none)]
def scope : NodeDecl → GroupScopedEval.Request := fun _ => .global
def peer : NodeDecl → Nat → Tid := fun _ _ => 0
def finalStore (g : GraphDecl) (s : Store) : Store := applyNode g s selected

theorem schedule_valid : InputSchedule nodes requests := by decide

theorem run_success (g : GraphDecl) (s : Store) :
    runWithInputs g scope peer nodes (some requests) (some s) = some (finalStore g s) := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some (finalStore g s)
  rw [if_pos schedule_valid]
  change stepWithInputs g (scope selected) (peer selected) s selected none = _
  rw [stepWithInputs_ordinary g (scope selected) (peer selected) s selected (by decide)]
  exact step_global g (peer selected) s selected (by decide)

theorem caller_read (g : GraphDecl) (s t : Store)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t 50 = bw_div (4 : Scalar) (t 10) :=
  SourceBWDivRead.bw_div_value_of_split g scope peer nodes requests [] [] selected
    0 10 20 50 4 s t rfl rfl rfl (by decide) hrun

def seed : Tensor := { shape := [1,2,2,2], val := fun i => ((4*(i.val+1) : Nat) : Scalar) }
def saved : Tensor := { shape := [1,2,2,2], val := fun i => ((i.val+20 : Nat) : Scalar) }
def initial : Store := fun tid => if tid=10 then seed else if tid=20 then saved else zeroTensor []

theorem inputs_nonzero (i : Fin 8) : valAt seed i.val ≠ 0 ∧ valAt saved i.val ≠ 0 := by
  rw [valAt_of_lt seed i.val i.isLt,valAt_of_lt saved i.val i.isLt]
  change (((4*(i.val+1) : Nat) : Scalar) ≠ 0) ∧ (((i.val+20 : Nat) : Scalar) ≠ 0)
  constructor <;> positivity

theorem inputs_nonconstant : valAt seed 0 ≠ valAt seed 1 ∧ valAt saved 0 ≠ valAt saved 1 := by
  rw [valAt_of_lt seed 0 (by decide),valAt_of_lt seed 1 (by decide),
      valAt_of_lt saved 0 (by decide),valAt_of_lt saved 1 (by decide)]
  dsimp [seed,saved]
  norm_num

theorem inputs_preserved (g : GraphDecl) : (finalStore g initial) 10 = seed ∧ (finalStore g initial) 20 = saved := by
  constructor
  all_goals
    change applyNode g initial selected _ = _
    rw [applyNode_eq_of_not_mem_outs g initial selected _ (by decide)]
    rfl

theorem concrete_read (g : GraphDecl) : (finalStore g initial) 50 = bw_div (4 : Scalar) seed := by
  have h := caller_read g initial _ (run_success g initial)
  rw [(inputs_preserved g).1] at h
  exact h

theorem pointwise_derivative (g : GraphDecl) (i : Fin 8) :
    valAt ((finalStore g initial) 50) i.val = ((i.val+1 : Nat) : Scalar) := by
  rw [concrete_read g,valAt_of_lt (bw_div (4 : Scalar) seed) i.val i.isLt]
  change valAt seed i.val / 4 = ((i.val+1 : Nat) : Scalar)
  rw [valAt_of_lt seed i.val i.isLt]
  change ((4*(i.val+1) : Nat) : Scalar)/4 = ((i.val+1 : Nat) : Scalar)
  push_cast
  ring

theorem output_shape (g : GraphDecl) : ((finalStore g initial) 50).shape = [1,2,2,2] := by
  rw [concrete_read g]
  rfl

theorem output_nonzero (g : GraphDecl) (i : Fin 8) : valAt ((finalStore g initial) 50) i.val ≠ 0 := by
  rw [pointwise_derivative g i]
  positivity

theorem output_nonconstant (g : GraphDecl) :
    valAt ((finalStore g initial) 50) 0 ≠ valAt ((finalStore g initial) 50) 1 := by
  rw [pointwise_derivative g ⟨0,by decide⟩,pointwise_derivative g ⟨1,by decide⟩]
  norm_num

theorem not_cotangent (g : GraphDecl) : (finalStore g initial) 50 ≠ seed := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [pointwise_derivative g ⟨0,by decide⟩,valAt_of_lt seed 0 (by decide)] at hv
  dsimp [seed] at hv
  norm_num at hv

theorem not_saved (g : GraphDecl) : (finalStore g initial) 50 ≠ saved := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [pointwise_derivative g ⟨0,by decide⟩,valAt_of_lt saved 0 (by decide)] at hv
  dsimp [saved] at hv
  norm_num at hv

theorem not_multiply (g : GraphDecl) : (finalStore g initial) 50 ≠ scalarMul 4 seed := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [pointwise_derivative g ⟨0,by decide⟩] at hv
  dsimp [scalarMul,seed,Tensor.mkShape,valAt,prodShape] at hv
  norm_num at hv

theorem caller_nonvacuous (g : GraphDecl) : ∃ s t : Store,
    s 10 = seed ∧ s 20 = saved ∧
    (∀ i : Fin 8, valAt (s 10) i.val ≠ 0 ∧ valAt (s 20) i.val ≠ 0) ∧
    (valAt (s 10) 0 ≠ valAt (s 10) 1 ∧ valAt (s 20) 0 ≠ valAt (s 20) 1) ∧
    runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
    t 10 = seed ∧ t 20 = saved ∧ t 50 = bw_div (4 : Scalar) (t 10) ∧
    (t 50).shape = [1,2,2,2] ∧
    (∀ i : Fin 8, valAt (t 50) i.val = ((i.val+1 : Nat) : Scalar) ∧ valAt (t 50) i.val ≠ 0) ∧
    valAt (t 50) 0 ≠ valAt (t 50) 1 ∧ t 50 ≠ seed ∧ t 50 ≠ saved ∧ t 50 ≠ scalarMul 4 seed := by
  exact ⟨initial,finalStore g initial,rfl,rfl,inputs_nonzero,inputs_nonconstant,run_success g initial,
    (inputs_preserved g).1,(inputs_preserved g).2,caller_read g initial _ (run_success g initial),
    output_shape g,(fun i => ⟨pointwise_derivative g i,output_nonzero g i⟩),output_nonconstant g,
    not_cotangent g,not_saved g,not_multiply g⟩

#print axioms caller_nonvacuous
#print axioms caller_read
#print axioms pointwise_derivative
#print axioms not_cotangent
#print axioms not_saved
#print axioms not_multiply
end
end TrainVerify.Denote.SourceBWDivReadWitness
