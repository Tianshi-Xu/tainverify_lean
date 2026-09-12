import denote.SourceBWMatmulRead
import denote.SourceReduceScatterRead

namespace TrainVerify.Denote.MatmulDVReduceScatterWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def m0 : NodeDecl := { rank := 0, op := "OpName.BW_matmul", ins := [10,20,30], outs := [50,60] }
def m2 : NodeDecl := { rank := 2, op := "OpName.BW_matmul", ins := [11,21,31], outs := [51,61] }
def rs : NodeDecl := { rank := 2, op := "OpName.ReduceScatterPrim", ins := [60,61], outs := [70], params := [2] }
def graph : GraphDecl := { numRanks := 3, nodes := [m0,m2,rs] }
def requests : List InputRequest := [(m0,none),(m2,none),(rs,none)]
def scope (n : NodeDecl) : GroupScopedEval.Request :=
  if n.op = "OpName.ReduceScatterPrim" then .group (some [0,2]) else .global
def peer (_ : NodeDecl) (rank : Nat) : Tid := if rank = 0 then 60 else 61

def seed (scale : Nat) : Tensor :=
  { shape := [1,2,2,2], val := fun i => ((scale * (i.val+3) : Nat) : Scalar) }
def primal (offset : Nat) : Tensor :=
  { shape := [1,2,2,2], val := fun i => ((i.val+offset : Nat) : Scalar) }
def initial : Store := fun tid =>
  if tid = 10 then seed 1 else if tid = 11 then seed 2 else
  if tid = 20 ∨ tid = 21 then primal 1 else if tid = 30 ∨ tid = 31 then primal 11 else zeroTensor []
def beforeRS : Store := applyNode graph (applyNode graph initial m0) m2
def finalStore : Store := GroupScopedEval.localStep [0,2] beforeRS rs

theorem run_success : runWithInputs graph scope peer graph.nodes (some requests) (some initial) = some finalStore := by
  change (if InputSchedule graph.nodes requests then
    runUsing (fun row a => stepWithInputs graph (scope row.1) (peer row.1) a row.1 row.2)
      requests (some initial) else none) = some finalStore
  rw [if_pos (by decide)]
  change (stepWithInputs graph (scope m0) (peer m0) initial m0 none).bind (fun a =>
    (stepWithInputs graph (scope m2) (peer m2) a m2 none).bind (fun b =>
      stepWithInputs graph (scope rs) (peer rs) b rs none)) = _
  have h0 : stepWithInputs graph (scope m0) (peer m0) initial m0 none = some (applyNode graph initial m0) := by
    rw [stepWithInputs_ordinary _ _ _ _ _ (by decide)]
    exact step_global _ _ _ _ (by decide)
  have h2 : stepWithInputs graph (scope m2) (peer m2) (applyNode graph initial m0) m2 none = some beforeRS := by
    rw [stepWithInputs_ordinary _ _ _ _ _ (by decide)]
    exact step_global _ _ _ _ (by decide)
  rw [h0]
  simp only [Option.bind_some]
  rw [h2]
  simp only [Option.bind_some]
  rw [stepWithInputs_ordinary _ _ _ _ _ (by decide)]
  change step graph (.group (some [0,2])) (peer rs) beforeRS rs = _
  rw [step_group _ _ _ _ _ (by decide) (by decide)]
  exact GroupScopedEval.step_scoped graph beforeRS rs [0,2] (by decide) (by rfl)

theorem caller_read (s t : Store)
    (h : runWithInputs graph scope peer graph.nodes (some requests) (some s) = some t) :
    t 60 = (bw_matmul (t 10) (t 20) (t 30)).2 ∧
    t 61 = (bw_matmul (t 11) (t 21) (t 31)).2 ∧
    t 70 = chunkPrimDimN 2 2 1 (tensorSum [(bw_matmul (t 10) (t 20) (t 30)).2,
      (bw_matmul (t 11) (t 21) (t 31)).2]) := by
  have h0 := SourceBWMatmulRead.bw_matmul_dy_value_of_split graph scope peer graph.nodes
    requests [] [(m2,none),(rs,none)] m0 0 10 20 30 50 60 s t
    rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h
  have h2 := SourceBWMatmulRead.bw_matmul_dy_value_of_split graph scope peer graph.nodes
    requests [(m0,none)] [(rs,none)] m2 2 11 21 31 51 61 s t
    rfl rfl rfl (by decide) (by decide) (by decide) (by decide) h
  have hr := SourceReduceScatterRead.reduceScatter_value_of_split graph scope peer graph.nodes
    requests [(m0,none),(m2,none)] [] rs 2 [0,2] [60,61] 70 2 s t
    rfl rfl rfl (by decide) h
  change t 70 = chunkPrimDimN 2 2 1 (tensorSum [t 60,t 61]) at hr
  rw [h0,h2] at hr
  exact ⟨h0,h2,hr⟩

theorem frame (tid : Tid) (h0 : tid ∉ m0.outs) (h2 : tid ∉ m2.outs) (hr : tid ∉ rs.outs) :
    finalStore tid = initial tid := by
  change GroupScopedEval.localStep [0,2] beforeRS rs tid = _
  rw [GroupScopedEval.localStep_skip [0,2] beforeRS rs tid hr]
  change applyNode graph (applyNode graph initial m0) m2 tid = _
  rw [applyNode_eq_of_not_mem_outs graph _ m2 tid h2,
      applyNode_eq_of_not_mem_outs graph initial m0 tid h0]

theorem concrete_gradients :
    finalStore 60 = (bw_matmul (seed 1) (primal 1) (primal 11)).2 ∧
    finalStore 61 = (bw_matmul (seed 2) (primal 1) (primal 11)).2 := by
  have h := caller_read initial finalStore run_success
  have h0 := h.1
  have h2 := h.2.1
  rw [frame 10 (by decide) (by decide) (by decide), frame 20 (by decide) (by decide) (by decide),
      frame 30 (by decide) (by decide) (by decide)] at h0
  rw [frame 11 (by decide) (by decide) (by decide), frame 21 (by decide) (by decide) (by decide),
      frame 31 (by decide) (by decide) (by decide)] at h2
  exact ⟨h0,h2⟩

def dv0Expected (i : Nat) : Scalar := ([18, 22, 26, 32, 98, 110, 114, 128] : List Scalar).getD i 0

theorem dv0_pointwise (i : Fin 8) : valAt (finalStore 60) i.val = dv0Expected i.val := by
  rw [concrete_gradients.1]
  fin_cases i <;>
    dsimp [dv0Expected, bw_matmul, batchedMatmulBwd, batchedMatmul, transpose2d,
      seed, primal, Tensor.mkShape, valAt, prodShape, List.reverse, List.reverseAux] <;>
    norm_num [Finset.sum_range_succ]

def dv2Expected (i : Nat) : Scalar := ([36, 44, 52, 64, 196, 220, 228, 256] : List Scalar).getD i 0

theorem dv2_pointwise (i : Fin 8) : valAt (finalStore 61) i.val = dv2Expected i.val := by
  rw [concrete_gradients.2]
  fin_cases i <;>
    dsimp [dv2Expected, bw_matmul, batchedMatmulBwd, batchedMatmul, transpose2d,
      seed, primal, Tensor.mkShape, valAt, prodShape, List.reverse, List.reverseAux] <;>
    norm_num [Finset.sum_range_succ]

def outputExpected (i : Nat) : Scalar := ([78, 96, 342, 384] : List Scalar).getD i 0

theorem reduction_read : finalStore 70 = chunkPrimDimN 2 2 1 (tensorSum [finalStore 60,finalStore 61]) := by
  exact SourceReduceScatterRead.reduceScatter_value_of_split graph scope peer graph.nodes
    requests [(m0,none),(m2,none)] [] rs 2 [0,2] [60,61] 70 2 initial finalStore
    rfl rfl rfl (by decide) run_success

theorem gradient_shapes : (finalStore 60).shape = [1,2,2,2] ∧ (finalStore 61).shape = [1,2,2,2] := by
  rw [concrete_gradients.1, concrete_gradients.2]
  exact ⟨rfl,rfl⟩

theorem output_pointwise (i : Fin 4) : valAt (finalStore 70) i.val = outputExpected i.val := by
  rw [reduction_read]
  have h0 := gradient_shapes.1
  fin_cases i
  · simp only [chunkPrimDimN, tensorSum, Tensor.mkShape, h0, valAt, prodShape]
    change (0 : Scalar) + valAt (finalStore 60) 2 + valAt (finalStore 61) 2 = outputExpected _
    rw [dv0_pointwise ⟨2, by decide⟩, dv2_pointwise ⟨2, by decide⟩]
    norm_num [dv0Expected,dv2Expected,outputExpected]
  · simp only [chunkPrimDimN, tensorSum, Tensor.mkShape, h0, valAt, prodShape]
    change (0 : Scalar) + valAt (finalStore 60) 3 + valAt (finalStore 61) 3 = outputExpected _
    rw [dv0_pointwise ⟨3, by decide⟩, dv2_pointwise ⟨3, by decide⟩]
    norm_num [dv0Expected,dv2Expected,outputExpected]
  · simp only [chunkPrimDimN, tensorSum, Tensor.mkShape, h0, valAt, prodShape]
    change (0 : Scalar) + valAt (finalStore 60) 6 + valAt (finalStore 61) 6 = outputExpected _
    rw [dv0_pointwise ⟨6, by decide⟩, dv2_pointwise ⟨6, by decide⟩]
    norm_num [dv0Expected,dv2Expected,outputExpected]
  · simp only [chunkPrimDimN, tensorSum, Tensor.mkShape, h0, valAt, prodShape]
    change (0 : Scalar) + valAt (finalStore 60) 7 + valAt (finalStore 61) 7 = outputExpected _
    rw [dv0_pointwise ⟨7, by decide⟩, dv2_pointwise ⟨7, by decide⟩]
    norm_num [dv0Expected,dv2Expected,outputExpected]

theorem primal_nonzero (offset : Nat) (ho : 0 < offset) (i : Fin 8) :
    valAt (primal offset) i.val ≠ 0 := by
  rw [valAt_of_lt (primal offset) i.val i.isLt]
  change ((i.val + offset : Nat) : Scalar) ≠ 0
  exact_mod_cast (Nat.ne_of_gt (Nat.add_pos_right i.val ho))

theorem seed_nonzero (scale : Nat) (hs : 0 < scale) (i : Fin 8) :
    valAt (seed scale) i.val ≠ 0 := by
  rw [valAt_of_lt (seed scale) i.val i.isLt]
  change ((scale * (i.val+3) : Nat) : Scalar) ≠ 0
  positivity

theorem primal_nonconstant (offset : Nat) : valAt (primal offset) 0 ≠ valAt (primal offset) 1 := by
  rw [valAt_of_lt (primal offset) 0 (by change 0 < 8; decide), valAt_of_lt (primal offset) 1 (by change 1 < 8; decide)]
  change ((0+offset : Nat) : Scalar) ≠ ((1+offset : Nat) : Scalar)
  exact_mod_cast (by omega : 0+offset ≠ 1+offset)

theorem seed_nonconstant (scale : Nat) (hs : 0 < scale) : valAt (seed scale) 0 ≠ valAt (seed scale) 1 := by
  rw [valAt_of_lt (seed scale) 0 (by change 0 < 8; decide), valAt_of_lt (seed scale) 1 (by change 1 < 8; decide)]
  change ((scale*3 : Nat) : Scalar) ≠ ((scale*4 : Nat) : Scalar)
  exact_mod_cast (Nat.ne_of_lt (Nat.mul_lt_mul_of_pos_left (by decide) hs))

theorem contributions_distinct : finalStore 60 ≠ finalStore 61 := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  rw [dv0_pointwise ⟨0,by decide⟩,dv2_pointwise ⟨0,by decide⟩] at hv
  norm_num [dv0Expected,dv2Expected] at hv

theorem output_shape : (finalStore 70).shape = [1,2,1,2] := by
  rw [reduction_read]
  simp only [chunkPrimDimN, tensorSum, gradient_shapes.1, Tensor.mkShape]
  rfl

theorem output_nonzero (i : Fin 4) : valAt (finalStore 70) i.val ≠ 0 := by
  rw [output_pointwise i]
  fin_cases i <;> norm_num [outputExpected]

theorem output_nonconstant : valAt (finalStore 70) 0 ≠ valAt (finalStore 70) 1 := by
  rw [output_pointwise ⟨0,by decide⟩,output_pointwise ⟨1,by decide⟩]
  norm_num [outputExpected]

-- Averaging contributions would divide this true SUM result by two.
theorem not_average : finalStore 70 ≠ scalarDiv (finalStore 70) 2 := by
  intro h
  have hv := congrArg (fun t => valAt t 0) h
  have hr : valAt (scalarDiv (finalStore 70) 2) 0 = valAt (finalStore 70) 0 / 2 := by
    rw [valAt_of_lt _ 0 (by rw [show (scalarDiv (finalStore 70) 2).shape = (finalStore 70).shape from rfl, output_shape]; decide)]
    rfl
  rw [hr,output_pointwise ⟨0,by decide⟩] at hv
  norm_num [outputExpected] at hv

theorem source_conditions :
    GroupScopedEval.WellFormed graph.numRanks rs.rank [0,2] ∧
    rs.ins = [0,2].map (peer rs) ∧ [0,2].idxOf rs.rank = 1 ∧
    (∀ tid ∈ rs.ins, (beforeRS tid).shape = [1,2,2,2]) ∧
    GroupScopedEval.ChunkInput [0,2] 2 (tensorSum (rs.ins.map beforeRS)) := by
  refine ⟨by decide, rfl, by decide, ?_, ?_⟩
  · intro tid ht
    change tid ∈ [60,61] at ht
    rcases List.mem_cons.mp ht with h | h
    · subst tid; rfl
    · have h' := List.mem_singleton.mp h; subst tid; rfl
  · exact ⟨by decide,by decide,by decide⟩

theorem caller_nonvacuous : ∃ s t : Store,
    s 10 = seed 1 ∧ s 11 = seed 2 ∧ s 20 = primal 1 ∧ s 21 = primal 1 ∧
    s 30 = primal 11 ∧ s 31 = primal 11 ∧
    (∀ i : Fin 8, valAt (seed 1) i.val ≠ 0 ∧ valAt (seed 2) i.val ≠ 0 ∧
      valAt (primal 1) i.val ≠ 0 ∧ valAt (primal 11) i.val ≠ 0) ∧
    valAt (seed 1) 0 ≠ valAt (seed 1) 1 ∧ valAt (seed 2) 0 ≠ valAt (seed 2) 1 ∧
    valAt (primal 1) 0 ≠ valAt (primal 1) 1 ∧ valAt (primal 11) 0 ≠ valAt (primal 11) 1 ∧
    runWithInputs graph scope peer graph.nodes (some requests) (some s) = some t ∧
    (∀ tid, tid ∉ m0.outs → tid ∉ m2.outs → tid ∉ rs.outs → t tid = s tid) ∧
    t 60 = (bw_matmul (t 10) (t 20) (t 30)).2 ∧
    t 61 = (bw_matmul (t 11) (t 21) (t 31)).2 ∧
    t 70 = chunkPrimDimN 2 2 1 (tensorSum [(bw_matmul (t 10) (t 20) (t 30)).2,
      (bw_matmul (t 11) (t 21) (t 31)).2]) ∧
    (t 60).shape = [1,2,2,2] ∧ (t 61).shape = [1,2,2,2] ∧ (t 70).shape = [1,2,1,2] ∧
    (∀ i : Fin 8, valAt (t 60) i.val = dv0Expected i.val ∧ valAt (t 61) i.val = dv2Expected i.val) ∧
    (∀ i : Fin 4, valAt (t 70) i.val = outputExpected i.val ∧ valAt (t 70) i.val ≠ 0) ∧
    valAt (t 70) 0 ≠ valAt (t 70) 1 ∧ t 60 ≠ t 61 ∧ t 70 ≠ scalarDiv (t 70) 2 := by
  have h := caller_read initial finalStore run_success
  exact ⟨initial,finalStore,rfl,rfl,rfl,rfl,rfl,rfl,
    (fun i => ⟨seed_nonzero 1 (by decide) i,seed_nonzero 2 (by decide) i,
      primal_nonzero 1 (by decide) i,primal_nonzero 11 (by decide) i⟩),
    seed_nonconstant 1 (by decide),seed_nonconstant 2 (by decide),primal_nonconstant 1,primal_nonconstant 11,
    run_success,frame,h.1,h.2.1,h.2.2,gradient_shapes.1,gradient_shapes.2,output_shape,
    (fun i => ⟨dv0_pointwise i,dv2_pointwise i⟩),
    (fun i => ⟨output_pointwise i,output_nonzero i⟩),output_nonconstant,contributions_distinct,not_average⟩

#print axioms caller_nonvacuous
#print axioms source_conditions
#print axioms contributions_distinct
#print axioms not_average
#print axioms run_success
#print axioms caller_read
#print axioms dv0_pointwise
#print axioms dv2_pointwise
#print axioms output_pointwise
end
end TrainVerify.Denote.MatmulDVReduceScatterWitness
