import denote.SourceBWAddRead

/-!
Edit-only candidate, to be kernel-checked serially by the parent.
A real checked singleton BW_add run has nonzero, nonconstant G=[1,3],
X=[2,5], Y=[7,11], not assumed output equations. Both source readers are called.
Same-shape identity is derived separately. A second real run broadcasts a [1]
right operand against [2]; its right gradient has shape [1] and cannot equal G.
This witness concerns exact Denote semantics, not floating-point authentication.
-/
namespace TrainVerify.Denote.SourceBWAddReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_add", ins := [10, 20, 30],
    outs := [50, 60], params := [] }
def nodes : List NodeDecl := [selected]
def requests : List InputRequest := [(selected, none)]
def scope : NodeDecl → GroupScopedEval.Request := fun _ => .global
def peer : NodeDecl → Nat → Tid := fun _ _ => 0
def finalStore (g : GraphDecl) (s : Store) : Store := applyNode g s selected

theorem schedule_valid : InputSchedule nodes requests := by decide

theorem outputs_distinct : (50 : Tid) ≠ 60 := by decide

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
    t 50 = (bw_add2 (t 10) (t 20) (t 30)).1 ∧
    t 60 = (bw_add2 (t 10) (t 20) (t 30)).2 := by
  refine ⟨?_, ?_⟩
  · exact SourceBWAddRead.bw_add_dleft_value_of_split
      g scope peer nodes requests [] [] selected 0 10 20 30 50 60 s t
      rfl rfl rfl outputs_distinct (by decide) (by decide) (by decide) hrun
  · exact SourceBWAddRead.bw_add_dright_value_of_split
      g scope peer nodes requests [] [] selected 0 10 20 30 50 60 s t
      rfl rfl rfl outputs_distinct (by decide) (by decide) (by decide) hrun

theorem add_read (g : GraphDecl) (s : Store) :
    (finalStore g s) 50 =
      (bw_add2 ((finalStore g s) 10) ((finalStore g s) 20) ((finalStore g s) 30)).1 ∧
    (finalStore g s) 60 =
      (bw_add2 ((finalStore g s) 10) ((finalStore g s) 20) ((finalStore g s) 30)).2 :=
  caller_read g s (finalStore g s) (run_success g s)

def seed : Tensor := { shape := [2], val := fun i => if i.val = 0 then 1 else 3 }
def left : Tensor := { shape := [2], val := fun i => if i.val = 0 then 2 else 5 }
def right : Tensor := { shape := [2], val := fun i => if i.val = 0 then 7 else 11 }
def smallRight : Tensor := { shape := [1], val := fun _ => 7 }
def initialWith (y : Tensor) : Store := fun tid =>
  if tid = 10 then seed else if tid = 20 then left else
  if tid = 30 then y else zeroTensor []
def initial : Store := initialWith right

theorem seed_zero_value : valAt seed 0 = 1 := by
  rw [valAt_of_lt seed 0 (by decide)]
  rfl

theorem seed_one_value : valAt seed 1 = 3 := by
  rw [valAt_of_lt seed 1 (by decide)]
  rfl

theorem seed_nonzero (idx : Nat) (hidx : idx < prodShape seed.shape) :
    valAt seed idx ≠ 0 := by
  rw [valAt_of_lt seed idx hidx]
  change (if idx = 0 then (1 : Scalar) else 3) ≠ 0
  split_ifs <;> norm_num

theorem seed_nonconstant : valAt seed 0 ≠ valAt seed 1 := by
  rw [seed_zero_value, seed_one_value]
  norm_num

theorem operands_distinct : left ≠ right := by
  intro h
  have hv := congrArg (fun a : Tensor => valAt a 0) h
  rw [valAt_of_lt left 0 (by decide), valAt_of_lt right 0 (by decide)] at hv
  change (2 : Scalar) = 7 at hv
  norm_num at hv

theorem left_nonconstant : valAt left 0 ≠ valAt left 1 := by
  rw [valAt_of_lt left 0 (by decide), valAt_of_lt left 1 (by decide)]
  change (2 : Scalar) ≠ 5
  norm_num

theorem right_nonconstant : valAt right 0 ≠ valAt right 1 := by
  rw [valAt_of_lt right 0 (by decide), valAt_of_lt right 1 (by decide)]
  change (7 : Scalar) ≠ 11
  norm_num

theorem seed_preserved (g : GraphDecl) (y : Tensor) :
    (finalStore g (initialWith y)) 10 = seed := by
  change applyNode g (initialWith y) selected 10 = seed
  rw [applyNode_eq_of_not_mem_outs g (initialWith y) selected 10 (by decide)]
  rfl

theorem left_preserved (g : GraphDecl) (y : Tensor) :
    (finalStore g (initialWith y)) 20 = left := by
  change applyNode g (initialWith y) selected 20 = left
  rw [applyNode_eq_of_not_mem_outs g (initialWith y) selected 20 (by decide)]
  rfl

theorem right_preserved (g : GraphDecl) (y : Tensor) :
    (finalStore g (initialWith y)) 30 = y := by
  change applyNode g (initialWith y) selected 30 = y
  rw [applyNode_eq_of_not_mem_outs g (initialWith y) selected 30 (by decide)]
  rfl

theorem concrete_reads (g : GraphDecl) (y : Tensor) :
    (finalStore g (initialWith y)) 50 = (bw_add2 seed left y).1 ∧
    (finalStore g (initialWith y)) 60 = (bw_add2 seed left y).2 := by
  have h := add_read g (initialWith y)
  rw [seed_preserved g y, left_preserved g y, right_preserved g y] at h
  exact h

/-- Equal-shape identity is proved, never made a source-reader assumption. -/
theorem same_shape_gradients (g : GraphDecl) :
    (finalStore g initial) 50 = seed ∧ (finalStore g initial) 60 = seed := by
  have h := concrete_reads g right
  refine ⟨?_, ?_⟩
  · exact h.1.trans (bw_add2_fst_same_shape seed left right rfl)
  · exact h.2.trans (bw_add2_snd_same_shape seed left right rfl)

theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      s 10 = seed ∧ s 20 = left ∧ s 30 = right ∧
      (∀ idx, idx < prodShape (s 10).shape → valAt (s 10) idx ≠ 0) ∧
      valAt (s 10) 0 ≠ valAt (s 10) 1 ∧ s 20 ≠ s 30 ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 10 = seed ∧ t 20 = left ∧ t 30 = right ∧
      (t 50 = (bw_add2 (t 10) (t 20) (t 30)).1 ∧
       t 60 = (bw_add2 (t 10) (t 20) (t 30)).2) ∧
      (t 50 = seed ∧ t 60 = seed) := by
  exact ⟨initial, finalStore g initial, rfl, rfl, rfl,
    seed_nonzero, seed_nonconstant, operands_distinct, run_success g initial,
    seed_preserved g right, left_preserved g right, right_preserved g right,
    add_read g initial, same_shape_gradients g⟩

/-- A genuine broadcast case: the second projection reduces to shape [1]. -/
theorem broadcast_output_shapes (g : GraphDecl) :
    ((finalStore g (initialWith smallRight)) 50).shape = [2] ∧
    ((finalStore g (initialWith smallRight)) 60).shape = [1] := by
  have h := concrete_reads g smallRight
  refine ⟨?_, ?_⟩
  · rw [h.1]
    rfl
  · rw [h.2]
    rfl

theorem broadcast_right_not_seed (g : GraphDecl) :
    (finalStore g (initialWith smallRight)) 60 ≠ seed := by
  intro h
  have hs := congrArg Tensor.shape h
  rw [(broadcast_output_shapes g).2] at hs
  change ([1] : Shape) = [2] at hs
  exact (by decide : ([1] : Shape) ≠ [2]) hs

theorem broadcast_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      s 10 = seed ∧ s 20 = left ∧ s 30 = smallRight ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 10 = seed ∧ t 20 = left ∧ t 30 = smallRight ∧
      (t 50 = (bw_add2 (t 10) (t 20) (t 30)).1 ∧
       t 60 = (bw_add2 (t 10) (t 20) (t 30)).2) ∧
      ((t 50).shape = [2] ∧ (t 60).shape = [1]) ∧ t 60 ≠ seed := by
  exact ⟨initialWith smallRight, finalStore g (initialWith smallRight), rfl, rfl, rfl,
    run_success g (initialWith smallRight), seed_preserved g smallRight,
    left_preserved g smallRight, right_preserved g smallRight,
    add_read g (initialWith smallRight), broadcast_output_shapes g,
    broadcast_right_not_seed g⟩

#print axioms schedule_valid
#print axioms outputs_distinct
#print axioms run_success
#print axioms caller_read
#print axioms add_read
#print axioms seed_zero_value
#print axioms seed_one_value
#print axioms seed_nonzero
#print axioms seed_nonconstant
#print axioms operands_distinct
#print axioms left_nonconstant
#print axioms right_nonconstant
#print axioms seed_preserved
#print axioms left_preserved
#print axioms right_preserved
#print axioms concrete_reads
#print axioms same_shape_gradients
#print axioms caller_nonvacuous
#print axioms broadcast_output_shapes
#print axioms broadcast_right_not_seed
#print axioms broadcast_nonvacuous
end
end TrainVerify.Denote.SourceBWAddReadWitness
