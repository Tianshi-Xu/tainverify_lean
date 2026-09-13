import denote.SourceBWMatmulRead

/-!
Joint batched BW_matmul witness: two distinct nonsymmetric 2x2 matrices per
primal, shape [1,2,2,2]. One successful checked run supplies both outputs and
retains both primals. This is local Denote evidence, not full model refinement.
-/
namespace TrainVerify.Denote.SourceBWMatmulReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_matmul", ins := [10, 20, 30], outs := [50, 60], params := [] }
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
    t 50 = (bw_matmul (t 10) (t 20) (t 30)).1 ∧
    t 60 = (bw_matmul (t 10) (t 20) (t 30)).2 := by
  exact ⟨SourceBWMatmulRead.bw_matmul_dx_value_of_split
    g scope peer nodes requests [] [] selected 0 10 20 30 50 60 s t
    rfl rfl rfl (by decide) (by decide) (by decide) (by decide) hrun,
    SourceBWMatmulRead.bw_matmul_dy_value_of_split
    g scope peer nodes requests [] [] selected 0 10 20 30 50 60 s t
    rfl rfl rfl (by decide) (by decide) (by decide) (by decide) hrun⟩

def ramp (offset : Nat) : Tensor :=
  { shape := [1,2,2,2], val := fun i => (i.val + offset : Nat) }
def seed : Tensor := ramp 3
def left : Tensor := ramp 1
def right : Tensor := ramp 11
def initial : Store := fun tid =>
  if tid = 10 then seed else if tid = 20 then left else if tid = 30 then right else zeroTensor []

theorem ramp_nonzero (offset : Nat) (ho : 0 < offset) (i : Fin 8) :
    valAt (ramp offset) i.val ≠ 0 := by
  rw [valAt_of_lt (ramp offset) i.val i.isLt]
  change ((i.val + offset : Nat) : Scalar) ≠ 0
  exact_mod_cast (Nat.ne_of_gt (Nat.add_pos_right i.val ho))

theorem seed_nonconstant : valAt seed 0 ≠ valAt seed 1 := by
  rw [valAt_of_lt seed 0 (by decide), valAt_of_lt seed 1 (by decide)]
  change ((3 : Nat) : Scalar) ≠ ((4 : Nat) : Scalar)
  norm_num
theorem left_nonconstant : valAt left 0 ≠ valAt left 1 := by
  rw [valAt_of_lt left 0 (by decide), valAt_of_lt left 1 (by decide)]
  change ((1 : Nat) : Scalar) ≠ ((2 : Nat) : Scalar)
  norm_num
theorem right_nonconstant : valAt right 0 ≠ valAt right 1 := by
  rw [valAt_of_lt right 0 (by decide), valAt_of_lt right 1 (by decide)]
  change ((11 : Nat) : Scalar) ≠ ((12 : Nat) : Scalar)
  norm_num

theorem inputs_preserved (g : GraphDecl) :
    (finalStore g initial) 10 = seed ∧ (finalStore g initial) 20 = left ∧
    (finalStore g initial) 30 = right := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    change applyNode g initial selected _ = _
    rw [applyNode_eq_of_not_mem_outs g initial selected _ (by decide)]
    rfl

theorem concrete_reads (g : GraphDecl) :
    (finalStore g initial) 50 = (bw_matmul seed left right).1 ∧
    (finalStore g initial) 60 = (bw_matmul seed left right).2 := by
  have h := caller_read g initial (finalStore g initial) (run_success g initial)
  rw [(inputs_preserved g).1, (inputs_preserved g).2.1, (inputs_preserved g).2.2] at h
  exact h

def expected_dx (i : Nat) : Scalar := ([81, 95, 127, 149, 233, 263, 295, 333] : List Scalar).getD i 0

theorem pointwise_dx (g : GraphDecl) (i : Fin 8) :
    valAt ((finalStore g initial) 50) i.val = expected_dx i.val := by
  rw [(concrete_reads g).1]
  fin_cases i <;>
    dsimp [expected_dx, bw_matmul, batchedMatmulBwd, batchedMatmul,
      transpose2d, seed, left, right, ramp, Tensor.mkShape, valAt, prodShape,
      List.reverse, List.reverseAux] <;>
    norm_num [Finset.sum_range_succ]

def expected_dy (i : Nat) : Scalar := ([18, 22, 26, 32, 98, 110, 114, 128] : List Scalar).getD i 0

theorem pointwise_dy (g : GraphDecl) (i : Fin 8) :
    valAt ((finalStore g initial) 60) i.val = expected_dy i.val := by
  rw [(concrete_reads g).2]
  fin_cases i <;>
    dsimp [expected_dy, bw_matmul, batchedMatmulBwd, batchedMatmul,
      transpose2d, seed, left, right, ramp, Tensor.mkShape, valAt, prodShape,
      List.reverse, List.reverseAux] <;>
    norm_num [Finset.sum_range_succ]

theorem output_shapes (g : GraphDecl) :
    ((finalStore g initial) 50).shape = [1,2,2,2] ∧
    ((finalStore g initial) 60).shape = [1,2,2,2] := by
  rw [(concrete_reads g).1, (concrete_reads g).2]
  exact ⟨rfl, rfl⟩

theorem outputs_nonzero (g : GraphDecl) (i : Fin 8) :
    valAt ((finalStore g initial) 50) i.val ≠ 0 ∧
    valAt ((finalStore g initial) 60) i.val ≠ 0 := by
  rw [pointwise_dx g i, pointwise_dy g i]
  fin_cases i <;> norm_num [expected_dx, expected_dy]

theorem outputs_nonconstant (g : GraphDecl) :
    valAt ((finalStore g initial) 50) 0 ≠ valAt ((finalStore g initial) 50) 1 ∧
    valAt ((finalStore g initial) 60) 0 ≠ valAt ((finalStore g initial) 60) 1 := by
  rw [pointwise_dx g ⟨0, by decide⟩, pointwise_dx g ⟨1, by decide⟩,
      pointwise_dy g ⟨0, by decide⟩, pointwise_dy g ⟨1, by decide⟩]
  norm_num [expected_dx, expected_dy]

theorem batches_distinct (g : GraphDecl) :
    valAt ((finalStore g initial) 50) 0 ≠ valAt ((finalStore g initial) 50) 4 ∧
    valAt ((finalStore g initial) 60) 0 ≠ valAt ((finalStore g initial) 60) 4 := by
  rw [pointwise_dx g ⟨0, by decide⟩, pointwise_dx g ⟨4, by decide⟩,
      pointwise_dy g ⟨0, by decide⟩, pointwise_dy g ⟨4, by decide⟩]
  norm_num [expected_dx, expected_dy]

theorem not_swapped (g : GraphDecl) : (finalStore g initial) 50 ≠ (finalStore g initial) 60 := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [pointwise_dx g ⟨0, by decide⟩, pointwise_dy g ⟨0, by decide⟩] at hv
  norm_num [expected_dx, expected_dy] at hv

theorem not_saved (g : GraphDecl) :
    (finalStore g initial) 50 ≠ left ∧ (finalStore g initial) 60 ≠ right := by
  constructor
  · intro h
    have hv := congrArg (fun t => valAt t 0) h
    rw [pointwise_dx g ⟨0, by decide⟩, valAt_of_lt left 0 (by decide)] at hv
    dsimp [expected_dx, left, ramp] at hv
    norm_num at hv
  · intro h
    have hv := congrArg (fun t => valAt t 0) h
    rw [pointwise_dy g ⟨0, by decide⟩, valAt_of_lt right 0 (by decide)] at hv
    dsimp [expected_dy, right, ramp] at hv
    norm_num at hv

theorem wrong_dx_zero : valAt (batchedMatmul seed right) 0 = 85 := by
  dsimp [batchedMatmul, seed, right, ramp, Tensor.mkShape, valAt, prodShape,
    List.reverse, List.reverseAux]
  norm_num [Finset.sum_range_succ]

theorem wrong_dy_zero : valAt (batchedMatmul left seed) 0 = 13 := by
  dsimp [batchedMatmul, seed, left, ramp, Tensor.mkShape, valAt, prodShape,
    List.reverse, List.reverseAux]
  norm_num [Finset.sum_range_succ]

theorem not_missing_transpose (g : GraphDecl) :
    (finalStore g initial) 50 ≠ batchedMatmul seed right ∧
    (finalStore g initial) 60 ≠ batchedMatmul left seed := by
  constructor
  · intro h
    have hv := congrArg (fun t => valAt t 0) h
    rw [pointwise_dx g ⟨0, by decide⟩, wrong_dx_zero] at hv
    norm_num [expected_dx] at hv
  · intro h
    have hv := congrArg (fun t => valAt t 0) h
    rw [pointwise_dy g ⟨0, by decide⟩, wrong_dy_zero] at hv
    norm_num [expected_dy] at hv

-- Every premise and both results inhabit this ONE successful checked run.
theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      s 10 = seed ∧ s 20 = left ∧ s 30 = right ∧
      (∀ i : Fin 8, valAt (s 10) i.val ≠ 0 ∧ valAt (s 20) i.val ≠ 0 ∧ valAt (s 30) i.val ≠ 0) ∧
      valAt (s 10) 0 ≠ valAt (s 10) 1 ∧
      valAt (s 20) 0 ≠ valAt (s 20) 1 ∧ valAt (s 30) 0 ≠ valAt (s 30) 1 ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 10 = seed ∧ t 20 = left ∧ t 30 = right ∧
      t 50 = (bw_matmul (t 10) (t 20) (t 30)).1 ∧
      t 60 = (bw_matmul (t 10) (t 20) (t 30)).2 ∧
      (t 50).shape = [1,2,2,2] ∧ (t 60).shape = [1,2,2,2] ∧
      (∀ i : Fin 8, valAt (t 50) i.val = expected_dx i.val ∧ valAt (t 60) i.val = expected_dy i.val) ∧
      (∀ i : Fin 8, valAt (t 50) i.val ≠ 0 ∧ valAt (t 60) i.val ≠ 0) ∧
      (valAt (t 50) 0 ≠ valAt (t 50) 1 ∧ valAt (t 60) 0 ≠ valAt (t 60) 1) ∧
      (valAt (t 50) 0 ≠ valAt (t 50) 4 ∧ valAt (t 60) 0 ≠ valAt (t 60) 4) ∧
      t 50 ≠ t 60 ∧ (t 50 ≠ left ∧ t 60 ≠ right) ∧
      (t 50 ≠ batchedMatmul seed right ∧ t 60 ≠ batchedMatmul left seed) := by
  exact ⟨initial, finalStore g initial, rfl, rfl, rfl,
    (fun i => ⟨ramp_nonzero 3 (by decide) i, ramp_nonzero 1 (by decide) i, ramp_nonzero 11 (by decide) i⟩),
    seed_nonconstant, left_nonconstant, right_nonconstant, run_success g initial,
    (inputs_preserved g).1, (inputs_preserved g).2.1, (inputs_preserved g).2.2,
    (caller_read g initial _ (run_success g initial)).1,
    (caller_read g initial _ (run_success g initial)).2,
    (output_shapes g).1, (output_shapes g).2,
    (fun i => ⟨pointwise_dx g i, pointwise_dy g i⟩), outputs_nonzero g,
    outputs_nonconstant g, batches_distinct g, not_swapped g, not_saved g, not_missing_transpose g⟩

#print axioms caller_nonvacuous
#print axioms not_swapped
#print axioms not_saved
#print axioms not_missing_transpose
#print axioms inputs_preserved
#print axioms outputs_nonzero
#print axioms outputs_nonconstant
#print axioms batches_distinct
#print axioms caller_read
#print axioms run_success
#print axioms pointwise_dx
#print axioms pointwise_dy
end
end TrainVerify.Denote.SourceBWMatmulReadWitness
