import denote.SourceBWViewRead

/-!
A joint nonzero/nonconstant successful checked BW_view run: G.shape=[2,3],
saved FW-input shape=[1,2,3]. Equal element count, changed dimension count.
Rejects identity and FW-output-as-saved-input by actual unequal output shapes.
Only a local Denote witness, not whole-capture execution or Torch refinement.
-/
namespace TrainVerify.Denote.SourceBWViewReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_view", ins := [10, 20], outs := [50], params := [1, 2, 3] }
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
    t 50 = fw_view [1, 2, 3] (t 10) :=
  SourceBWViewRead.bw_view_value_of_split
    g scope peer nodes requests [] [] selected 0 1 [2, 3] 10 20 50 s t
    rfl rfl rfl (by decide) (by decide) hrun

def seed : Tensor := { shape := [2, 3], val := fun i => if i.val = 0 then 1 else 3 }
def saved : Tensor := { shape := [1, 2, 3], val := fun i => if i.val = 0 then -1 else 2 }
def initial : Store := fun tid =>
  if tid = 10 then seed else if tid = 20 then saved else zeroTensor []

theorem seed_nonzero (idx : Nat) (hi : idx < prodShape seed.shape) :
    valAt seed idx ≠ 0 := by
  rw [valAt_of_lt seed idx hi]
  change (if idx = 0 then (1 : Scalar) else 3) ≠ 0
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
    (finalStore g initial) 50 = fw_view [1, 2, 3] seed := by
  have h := caller_read g initial (finalStore g initial) (run_success g initial)
  rw [seed_preserved g] at h
  exact h

theorem pointwise_reshape (g : GraphDecl) (idx : Nat)
    (hi : idx < prodShape saved.shape) :
    valAt ((finalStore g initial) 50) idx = valAt seed idx := by
  rw [concrete_read g]
  rw [valAt_of_lt (fw_view [1, 2, 3] seed) idx hi]
  rfl

theorem output_shape (g : GraphDecl) :
    ((finalStore g initial) 50).shape = [1, 2, 3] := by
  rw [concrete_read g]
  rfl

theorem same_element_count : prodShape seed.shape = prodShape saved.shape := rfl

theorem not_identity (g : GraphDecl) : (finalStore g initial) 50 ≠ seed := by
  intro h
  have hs := congrArg Tensor.shape h
  rw [output_shape g] at hs
  change [1, 2, 3] = [2, 3] at hs
  cases hs

theorem not_saved_output (g : GraphDecl) :
    (finalStore g initial) 50 ≠ fw_view (fw_view [2, 3] saved).shape seed := by
  intro h
  have hs := congrArg Tensor.shape h
  rw [output_shape g] at hs
  change [1, 2, 3] = [2, 3] at hs
  cases hs

theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      s 10 = seed ∧ s 20 = saved ∧
      (∀ idx, idx < prodShape (s 10).shape → valAt (s 10) idx ≠ 0) ∧
      (∀ idx, idx < prodShape (s 20).shape → valAt (s 20) idx ≠ 0) ∧
      valAt (s 10) 0 ≠ valAt (s 10) 1 ∧ valAt (s 20) 0 ≠ valAt (s 20) 1 ∧
      prodShape (s 10).shape = prodShape (s 20).shape ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 10 = seed ∧ t 20 = saved ∧ t 50 = fw_view [1, 2, 3] (t 10) ∧
      (∀ idx, idx < prodShape saved.shape → valAt (t 50) idx = valAt seed idx) ∧
      t 50 ≠ seed ∧ t 50 ≠ fw_view (fw_view [2, 3] saved).shape seed := by
  exact ⟨initial, finalStore g initial, rfl, rfl, seed_nonzero, saved_nonzero,
    seed_nonconstant, saved_nonconstant, same_element_count, run_success g initial,
    seed_preserved g, saved_preserved g,
    caller_read g initial (finalStore g initial) (run_success g initial),
    pointwise_reshape g, not_identity g, not_saved_output g⟩

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
#print axioms pointwise_reshape
#print axioms output_shape
#print axioms same_element_count
#print axioms not_identity
#print axioms not_saved_output
#print axioms caller_nonvacuous
end
end TrainVerify.Denote.SourceBWViewReadWitness
