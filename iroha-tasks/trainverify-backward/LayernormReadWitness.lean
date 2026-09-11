import denote.SourceBWLayernormRead

/-!
Satisfiable caller for all three ordinary source BW_layernorm reads. The single
original checked run consumes a nonzero, nonconstant gradient [1,3,2,4,7,5], saved
input [2,5,1,6,3,9], gamma [2,3,4], and beta [1,2,3]. Gradient and input have shape
[2,3]; affine parameters have shape [3]. No output value or shape is assumed.

The witness reuses the source read and existing output-shape lemmas, not another
layernorm implementation. The parent checks this file serially; Python/source
seed authentication and floating-point agreement are separate evidence gates.
-/
namespace TrainVerify.Denote.SourceBWLayernormReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [10, 20, 30, 40],
    outs := [50, 60, 70], params := [] }
def nodes : List NodeDecl := [selected]
def requests : List InputRequest := [(selected, none)]
def scope : NodeDecl → GroupScopedEval.Request := fun _ => .global
def peer : NodeDecl → Nat → Tid := fun _ _ => 0
def finalStore (g : GraphDecl) (s : Store) : Store := applyNode g s selected

theorem schedule_valid : InputSchedule nodes requests := by decide

theorem outputs_distinct :
    (50 : Tid) ≠ 60 ∧ (50 : Tid) ≠ 70 ∧ (60 : Tid) ≠ 70 := by decide

theorem run_success (g : GraphDecl) (s : Store) :
    runWithInputs g scope peer nodes (some requests) (some s) = some (finalStore g s) := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some (finalStore g s)
  rw [if_pos schedule_valid]
  change stepWithInputs g (scope selected) (peer selected) s selected none = _
  rw [stepWithInputs_ordinary g (scope selected) (peer selected) s selected (by decide)]
  exact step_global g (peer selected) s selected (by decide)

/-- Each output is obtained by the new split theorem, with only the actual run
as a dynamic premise. All structural and distinctness conditions are discharged. -/
theorem caller_read (g : GraphDecl) (s t : Store)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t 50 = (bw_layernorm (t 10) (t 20) (t 30) (t 40)).1 ∧
    t 60 = (bw_layernorm (t 10) (t 20) (t 30) (t 40)).2.1 ∧
    t 70 = (bw_layernorm (t 10) (t 20) (t 30) (t 40)).2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact SourceBWLayernormRead.bw_layernorm_dx_value_of_split
      g scope peer nodes requests [] [] selected 0 10 20 30 40 50 60 70 s t
      rfl rfl rfl outputs_distinct.1 outputs_distinct.2.1 outputs_distinct.2.2
      (by decide) (by decide) (by decide) (by decide) hrun
  · exact SourceBWLayernormRead.bw_layernorm_dgamma_value_of_split
      g scope peer nodes requests [] [] selected 0 10 20 30 40 50 60 70 s t
      rfl rfl rfl outputs_distinct.1 outputs_distinct.2.1 outputs_distinct.2.2
      (by decide) (by decide) (by decide) (by decide) hrun
  · exact SourceBWLayernormRead.bw_layernorm_dbeta_value_of_split
      g scope peer nodes requests [] [] selected 0 10 20 30 40 50 60 70 s t
      rfl rfl rfl outputs_distinct.1 outputs_distinct.2.1 outputs_distinct.2.2
      (by decide) (by decide) (by decide) (by decide) hrun

theorem layernorm_read (g : GraphDecl) (s : Store) :
    (finalStore g s) 50 =
      (bw_layernorm ((finalStore g s) 10) ((finalStore g s) 20)
        ((finalStore g s) 30) ((finalStore g s) 40)).1 ∧
    (finalStore g s) 60 =
      (bw_layernorm ((finalStore g s) 10) ((finalStore g s) 20)
        ((finalStore g s) 30) ((finalStore g s) 40)).2.1 ∧
    (finalStore g s) 70 =
      (bw_layernorm ((finalStore g s) 10) ((finalStore g s) 20)
        ((finalStore g s) 30) ((finalStore g s) 40)).2.2 :=
  caller_read g s (finalStore g s) (run_success g s)

def seed : Tensor :=
  { shape := [2, 3], val := fun i =>
      if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 2
      else if i.val = 3 then 4 else if i.val = 4 then 7 else 5 }
def primal : Tensor :=
  { shape := [2, 3], val := fun i =>
      if i.val = 0 then 2 else if i.val = 1 then 5 else if i.val = 2 then 1
      else if i.val = 3 then 6 else if i.val = 4 then 3 else 9 }
def gamma : Tensor :=
  { shape := [3], val := fun i => if i.val = 0 then 2 else if i.val = 1 then 3 else 4 }
def beta : Tensor :=
  { shape := [3], val := fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else 3 }
def initial : Store := fun tid =>
  if tid = 10 then seed else if tid = 20 then primal else
  if tid = 30 then gamma else if tid = 40 then beta else zeroTensor []

theorem seed_zero_value : valAt seed 0 = 1 := by
  rw [valAt_of_lt seed 0 (by decide)]
  rfl

theorem seed_one_value : valAt seed 1 = 3 := by
  rw [valAt_of_lt seed 1 (by decide)]
  rfl

theorem seed_nonzero (idx : Nat) (hidx : idx < prodShape seed.shape) :
    valAt seed idx ≠ 0 := by
  rw [valAt_of_lt seed idx hidx]
  change (if idx = 0 then (1 : Scalar) else if idx = 1 then 3 else if idx = 2 then 2
    else if idx = 3 then 4 else if idx = 4 then 7 else 5) ≠ 0
  split_ifs <;> norm_num

theorem seed_nonconstant : valAt seed 0 ≠ valAt seed 1 := by
  rw [seed_zero_value, seed_one_value]
  norm_num

theorem primal_nonconstant : valAt primal 0 ≠ valAt primal 1 := by
  rw [valAt_of_lt primal 0 (by decide), valAt_of_lt primal 1 (by decide)]
  change (2 : Scalar) ≠ 5
  norm_num

theorem seed_preserved (g : GraphDecl) : (finalStore g initial) 10 = seed := by
  change applyNode g initial selected 10 = seed
  rw [applyNode_eq_of_not_mem_outs g initial selected 10 (by decide)]
  rfl

theorem primal_preserved (g : GraphDecl) : (finalStore g initial) 20 = primal := by
  change applyNode g initial selected 20 = primal
  rw [applyNode_eq_of_not_mem_outs g initial selected 20 (by decide)]
  rfl

theorem gamma_preserved (g : GraphDecl) : (finalStore g initial) 30 = gamma := by
  change applyNode g initial selected 30 = gamma
  rw [applyNode_eq_of_not_mem_outs g initial selected 30 (by decide)]
  rfl

theorem beta_preserved (g : GraphDecl) : (finalStore g initial) 40 = beta := by
  change applyNode g initial selected 40 = beta
  rw [applyNode_eq_of_not_mem_outs g initial selected 40 (by decide)]
  rfl

/-- Concrete tensors on the right are the actual saved inputs of the run. -/
theorem concrete_reads (g : GraphDecl) :
    (finalStore g initial) 50 = (bw_layernorm seed primal gamma beta).1 ∧
    (finalStore g initial) 60 = (bw_layernorm seed primal gamma beta).2.1 ∧
    (finalStore g initial) 70 = (bw_layernorm seed primal gamma beta).2.2 := by
  have h := layernorm_read g initial
  rw [seed_preserved g, primal_preserved g, gamma_preserved g, beta_preserved g] at h
  exact h

theorem output_shapes (g : GraphDecl) :
    ((finalStore g initial) 50).shape = [2, 3] ∧
    ((finalStore g initial) 60).shape = [3] ∧
    ((finalStore g initial) 70).shape = [3] := by
  have h := concrete_reads g
  refine ⟨?_, ?_, ?_⟩
  · rw [h.1]
    exact bw_layernorm_dx_shape seed primal gamma beta 3 [2] rfl
  · rw [h.2.1]
    exact bw_layernorm_dw_shape seed primal gamma beta 3 [2] rfl
  · rw [h.2.2]
    exact bw_layernorm_db_shape seed primal gamma beta 3 [2] rfl

/-- An actual successful checked run, with nonzero/nonconstant gradient, saved
inputs preserved, and all three final-store reads and output shapes derived. -/
theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      s 10 = seed ∧ s 20 = primal ∧ s 30 = gamma ∧ s 40 = beta ∧
      (s 10).shape = [2, 3] ∧ (s 20).shape = [2, 3] ∧
      (s 30).shape = [3] ∧ (s 40).shape = [3] ∧
      (∀ idx, idx < prodShape (s 10).shape → valAt (s 10) idx ≠ 0) ∧
      valAt (s 10) 0 ≠ valAt (s 10) 1 ∧
      valAt (s 20) 0 ≠ valAt (s 20) 1 ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      t 10 = seed ∧ t 20 = primal ∧ t 30 = gamma ∧ t 40 = beta ∧
      (t 50 = (bw_layernorm (t 10) (t 20) (t 30) (t 40)).1 ∧
       t 60 = (bw_layernorm (t 10) (t 20) (t 30) (t 40)).2.1 ∧
       t 70 = (bw_layernorm (t 10) (t 20) (t 30) (t 40)).2.2) ∧
      ((t 50).shape = [2, 3] ∧ (t 60).shape = [3] ∧ (t 70).shape = [3]) := by
  exact ⟨initial, finalStore g initial, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, seed_nonzero, seed_nonconstant, primal_nonconstant,
    run_success g initial, seed_preserved g, primal_preserved g,
    gamma_preserved g, beta_preserved g, layernorm_read g initial, output_shapes g⟩

#print axioms schedule_valid
#print axioms outputs_distinct
#print axioms run_success
#print axioms caller_read
#print axioms layernorm_read
#print axioms seed_zero_value
#print axioms seed_one_value
#print axioms seed_nonzero
#print axioms seed_nonconstant
#print axioms primal_nonconstant
#print axioms seed_preserved
#print axioms primal_preserved
#print axioms gamma_preserved
#print axioms beta_preserved
#print axioms concrete_reads
#print axioms output_shapes
#print axioms caller_nonvacuous
end
end TrainVerify.Denote.SourceBWLayernormReadWitness
