import denote.SourceBWTransposeRead

/-! Joint nonconstant, nonzero successful BW_transpose witness, square swapped
axes in rank four. Output and G have the SAME shape but differ at index 1.
Only local Denote semantics, not capture execution or Torch refinement. -/
namespace TrainVerify.Denote.SourceBWTransposeReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_transpose", ins := [10, 20], outs := [50], params := [1, 2] }
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
    t 50 = transposeAxes 1 2 (t 10) :=
  SourceBWTransposeRead.bw_transpose_value_of_split
    g scope peer nodes requests [] [] selected 0 1 2 10 20 50 s t
    rfl rfl rfl (by decide) (by decide) hrun

def seed : Tensor := { shape := [1, 2, 2, 1], val := fun i => if i.val = 1 then 3 else if i.val = 2 then 5 else 1 }
def saved : Tensor := { shape := [1, 2, 2, 1], val := fun i => if i.val = 0 then -1 else 2 }
def initial : Store := fun tid =>
  if tid = 10 then seed else if tid = 20 then saved else zeroTensor []

theorem seed_nonzero (idx : Nat) (hi : idx < prodShape seed.shape) :
    valAt seed idx ≠ 0 := by
  rw [valAt_of_lt seed idx hi]
  change (if idx = 1 then (3 : Scalar) else if idx = 2 then 5 else 1) ≠ 0
  split_ifs <;> norm_num

theorem saved_nonzero (idx : Nat) (hi : idx < prodShape saved.shape) :
    valAt saved idx ≠ 0 := by
  rw [valAt_of_lt saved idx hi]
  change (if idx = 0 then (-1 : Scalar) else 2) ≠ 0
  split_ifs <;> norm_num

theorem seed_nonconstant : valAt seed 0 ≠ valAt seed 1 := by
  rw [valAt_of_lt seed 0 (by decide), valAt_of_lt seed 1 (by decide)]
  change (1 : Scalar) ≠ 3
  norm_num

theorem saved_nonconstant : valAt saved 0 ≠ valAt saved 1 := by
  rw [valAt_of_lt saved 0 (by decide), valAt_of_lt saved 1 (by decide)]
  change (-1 : Scalar) ≠ 2
  norm_num

theorem seed_preserved (g : GraphDecl) : (finalStore g initial) 10 = seed := by
  change applyNode g initial selected 10 = seed
  rw [applyNode_eq_of_not_mem_outs g initial selected 10 (by decide)]
  rfl

theorem saved_preserved (g : GraphDecl) : (finalStore g initial) 20 = saved := by
  change applyNode g initial selected 20 = saved
  rw [applyNode_eq_of_not_mem_outs g initial selected 20 (by decide)]
  rfl

theorem concrete_read (g : GraphDecl) :
    (finalStore g initial) 50 = transposeAxes 1 2 seed := by
  have h := caller_read g initial (finalStore g initial) (run_success g initial)
  rw [seed_preserved g] at h
  exact h

theorem pointwise_transpose (g : GraphDecl) (idx : Nat) (hi : idx < 4) :
    valAt ((finalStore g initial) 50) idx = valAt seed (idx % 2 * 2 + idx / 2) := by
  rw [concrete_read g]
  interval_cases idx <;> rfl

theorem same_shape (g : GraphDecl) :
    ((finalStore g initial) 50).shape = seed.shape := by
  rw [concrete_read g]
  rfl

theorem not_identity (g : GraphDecl) : (finalStore g initial) 50 ≠ seed := by
  intro h
  have hv := congrArg (fun x => valAt x 1) h
  rw [pointwise_transpose g 1 (by decide)] at hv
  change (5 : Scalar) = 3 at hv
  norm_num at hv

theorem not_saved (g : GraphDecl) : (finalStore g initial) 50 ≠ saved := by
  intro h
  have hv := congrArg (fun x => valAt x 0) h
  rw [pointwise_transpose g 0 (by decide)] at hv
  change (1 : Scalar) = -1 at hv
  norm_num at hv

theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      s 10 = seed ∧ s 20 = saved ∧
      (∀ idx, idx < prodShape (s 10).shape → valAt (s 10) idx ≠ 0) ∧
      (∀ idx, idx < prodShape (s 20).shape → valAt (s 20) idx ≠ 0) ∧
      valAt (s 10) 0 ≠ valAt (s 10) 1 ∧ valAt (s 20) 0 ≠ valAt (s 20) 1 ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 10 = seed ∧ t 20 = saved ∧ t 50 = transposeAxes 1 2 (t 10) ∧
      (∀ idx, idx < 4 → valAt (t 50) idx = valAt (t 10) (idx % 2 * 2 + idx / 2)) ∧
      (t 50).shape = (t 10).shape ∧ t 50 ≠ t 10 ∧ t 50 ≠ t 20 := by
  refine ⟨initial, finalStore g initial, rfl, rfl, seed_nonzero, saved_nonzero,
    seed_nonconstant, saved_nonconstant, run_success g initial,
    seed_preserved g, saved_preserved g,
    caller_read g initial (finalStore g initial) (run_success g initial), ?_⟩
  rw [seed_preserved g, saved_preserved g]
  exact ⟨pointwise_transpose g, same_shape g, not_identity g, not_saved g⟩

#print axioms schedule_valid
#print axioms run_success
#print axioms caller_read
#print axioms seed_nonzero
#print axioms saved_nonzero
#print axioms seed_nonconstant
#print axioms saved_nonconstant
#print axioms seed_preserved
#print axioms saved_preserved
#print axioms concrete_read
#print axioms pointwise_transpose
#print axioms same_shape
#print axioms not_identity
#print axioms not_saved
#print axioms caller_nonvacuous
end
end TrainVerify.Denote.SourceBWTransposeReadWitness
