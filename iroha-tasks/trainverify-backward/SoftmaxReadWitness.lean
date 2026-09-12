import denote.SourceBWSoftmaxRead

/-! Nonconstant saved logits log(2),log(3) produce probabilities 2/5,3/5.
Two batch rows have different cotangents and different nonzero derivatives.
One original checked run; local evidence, not full-model or Torch refinement. -/
namespace TrainVerify.Denote.SourceBWSoftmaxReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_softmax", ins := [10, 20], outs := [50], params := [3] }
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
    t 50 = bw_softmax (t 10) (t 20) :=
  SourceBWSoftmaxRead.bw_softmax_value_of_split
    g scope peer nodes requests [] [] selected 0 10 20 50 [3] s t
    rfl rfl rfl (by decide) (by decide) hrun

def seed : Tensor :=
  { shape := [1,2,1,2], val := fun i => ([1,3,2,6] : List Scalar).getD i.val 0 }
def saved : Tensor :=
  { shape := [1,2,1,2], val := fun i => if i.val % 2 = 0 then Real.log 2 else Real.log 3 }
def probabilities : Tensor :=
  { shape := [1,2,1,2], val := fun i => if i.val % 2 = 0 then 2/5 else 3/5 }
def initial : Store := fun tid =>
  if tid = 10 then seed else if tid = 20 then saved else zeroTensor []

theorem saved_nonzero (i : Fin 4) : valAt saved i.val ≠ 0 := by
  rw [valAt_of_lt saved i.val i.isLt]
  change (if i.val % 2 = 0 then Real.log 2 else Real.log 3) ≠ 0
  split_ifs
  · exact ne_of_gt (Real.log_pos (by norm_num))
  · exact ne_of_gt (Real.log_pos (by norm_num))

theorem seed_nonzero (i : Fin 4) : valAt seed i.val ≠ 0 := by
  rw [valAt_of_lt seed i.val i.isLt]
  fin_cases i <;> dsimp [seed] <;> norm_num

theorem seed_nonconstant : valAt seed 0 ≠ valAt seed 1 := by
  rw [valAt_of_lt seed 0 (by decide), valAt_of_lt seed 1 (by decide)]
  dsimp [seed]
  norm_num

theorem saved_nonconstant : valAt saved 0 ≠ valAt saved 1 := by
  rw [valAt_of_lt saved 0 (by decide), valAt_of_lt saved 1 (by decide)]
  change Real.log 2 ≠ Real.log 3
  intro h
  have hh := congrArg Real.exp h
  rw [Real.exp_log (by norm_num), Real.exp_log (by norm_num)] at hh
  norm_num at hh

theorem probabilities_exact : softmax saved = probabilities := by
  apply Tensor.ext (t1 := softmax saved) (t2 := probabilities) rfl
  intro idx hi
  change idx < 4 at hi
  interval_cases idx <;>
    dsimp [softmax, saved, probabilities, Tensor.mkShape, valAt, prodShape, List.reverse, List.reverseAux] <;>
    norm_num [Finset.sum_range_succ, expFn, Real.exp_log]

theorem inputs_preserved (g : GraphDecl) :
    (finalStore g initial) 10 = seed ∧ (finalStore g initial) 20 = saved := by
  constructor
  all_goals
    change applyNode g initial selected _ = _
    rw [applyNode_eq_of_not_mem_outs g initial selected _ (by decide)]
    rfl

theorem concrete_read (g : GraphDecl) : (finalStore g initial) 50 = bw_softmax seed saved := by
  have h := caller_read g initial _ (run_success g initial)
  rw [(inputs_preserved g).1, (inputs_preserved g).2] at h
  exact h

def expected (i : Nat) : Scalar := ([-12/25,12/25,-24/25,24/25] : List Scalar).getD i 0

theorem pointwise_derivative (g : GraphDecl) (i : Fin 4) :
    valAt ((finalStore g initial) 50) i.val = expected i.val := by
  rw [concrete_read g]
  change valAt (softmaxBwdFromOutput seed (softmax saved)) i.val = expected i.val
  rw [probabilities_exact]
  fin_cases i <;>
    dsimp [softmaxBwdFromOutput, probabilities, seed, expected, Tensor.mkShape, valAt,
      prodShape, List.reverse, List.reverseAux] <;>
    norm_num [Finset.sum_range_succ]

theorem output_shape (g : GraphDecl) : ((finalStore g initial) 50).shape = [1,2,1,2] := by
  rw [concrete_read g]
  rfl

theorem output_nonzero (g : GraphDecl) (i : Fin 4) : valAt ((finalStore g initial) 50) i.val ≠ 0 := by
  rw [pointwise_derivative g i]
  fin_cases i <;> norm_num [expected]

theorem output_nonconstant (g : GraphDecl) :
    valAt ((finalStore g initial) 50) 0 ≠ valAt ((finalStore g initial) 50) 1 := by
  rw [pointwise_derivative g ⟨0, by decide⟩, pointwise_derivative g ⟨1, by decide⟩]
  norm_num [expected]

theorem batches_distinct (g : GraphDecl) :
    valAt ((finalStore g initial) 50) 0 ≠ valAt ((finalStore g initial) 50) 2 := by
  rw [pointwise_derivative g ⟨0, by decide⟩, pointwise_derivative g ⟨2, by decide⟩]
  norm_num [expected]

theorem row_sum_zero (g : GraphDecl) (b : Fin 2) :
    valAt ((finalStore g initial) 50) (b.val*2) + valAt ((finalStore g initial) 50) (b.val*2+1) = 0 := by
  fin_cases b
  · change valAt ((finalStore g initial) 50) 0 + valAt ((finalStore g initial) 50) 1 = 0
    rw [pointwise_derivative g ⟨0, by decide⟩, pointwise_derivative g ⟨1, by decide⟩]
    norm_num [expected]
  · change valAt ((finalStore g initial) 50) 2 + valAt ((finalStore g initial) 50) 3 = 0
    rw [pointwise_derivative g ⟨2, by decide⟩, pointwise_derivative g ⟨3, by decide⟩]
    norm_num [expected]

theorem not_cotangent (g : GraphDecl) : (finalStore g initial) 50 ≠ seed := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [pointwise_derivative g ⟨0, by decide⟩, valAt_of_lt seed 0 (by decide)] at hv
  dsimp [seed, expected] at hv
  norm_num at hv

theorem not_saved (g : GraphDecl) : (finalStore g initial) 50 ≠ saved := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [pointwise_derivative g ⟨0, by decide⟩, valAt_of_lt saved 0 (by decide)] at hv
  dsimp [saved, expected] at hv
  norm_num at hv
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

def missingDot : Tensor :=
  { shape := [1,2,1,2], val := fun i => valAt probabilities i.val * valAt seed i.val }

theorem not_missing_dot (g : GraphDecl) : (finalStore g initial) 50 ≠ missingDot := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [pointwise_derivative g ⟨0, by decide⟩] at hv
  dsimp [missingDot, valAt, probabilities, seed, expected, prodShape] at hv
  norm_num at hv

theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      s 10 = seed ∧ s 20 = saved ∧ softmax (s 20) = probabilities ∧
      (∀ i : Fin 4, valAt (s 10) i.val ≠ 0 ∧ valAt (s 20) i.val ≠ 0) ∧
      valAt (s 10) 0 ≠ valAt (s 10) 1 ∧ valAt (s 20) 0 ≠ valAt (s 20) 1 ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 10 = seed ∧ t 20 = saved ∧ t 50 = bw_softmax (t 10) (t 20) ∧
      (t 50).shape = [1,2,1,2] ∧
      (∀ i : Fin 4, valAt (t 50) i.val = expected i.val ∧ valAt (t 50) i.val ≠ 0) ∧
      valAt (t 50) 0 ≠ valAt (t 50) 1 ∧ valAt (t 50) 0 ≠ valAt (t 50) 2 ∧
      (∀ b : Fin 2, valAt (t 50) (b.val*2) + valAt (t 50) (b.val*2+1) = 0) ∧
      t 50 ≠ seed ∧ t 50 ≠ saved ∧ t 50 ≠ missingDot := by
  exact ⟨initial, finalStore g initial, rfl, rfl, probabilities_exact,
    (fun i => ⟨seed_nonzero i, saved_nonzero i⟩), seed_nonconstant, saved_nonconstant,
    run_success g initial, (inputs_preserved g).1, (inputs_preserved g).2,
    caller_read g initial _ (run_success g initial), output_shape g,
    (fun i => ⟨pointwise_derivative g i, output_nonzero g i⟩),
    output_nonconstant g, batches_distinct g, row_sum_zero g,
    not_cotangent g, not_saved g, not_missing_dot g⟩

#print axioms caller_nonvacuous
#print axioms row_sum_zero
#print axioms not_missing_dot
#print axioms caller_read
#print axioms probabilities_exact
#print axioms pointwise_derivative
end
end TrainVerify.Denote.SourceBWSoftmaxReadWitness
