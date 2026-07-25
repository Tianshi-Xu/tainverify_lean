/-
Concrete non-vacuity regression for the source-witness zigzag layout relation.
-/
import denote.yoco_goals.ZigzagLayoutRel

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.GeneratedPatterns

namespace TrainVerify.Denote.ZigzagLayoutRelRegression
noncomputable section

def x0 : Tensor :=
  Tensor.mkShape [4, 1] (fun i => ((i.val : Nat) : Scalar))

def x1 : Tensor :=
  Tensor.mkShape [4, 1] (fun i => ((4 + i.val : Nat) : Scalar))

def cu : Tensor :=
  Tensor.mkShape [2] (fun i => if i.val = 0 then 0 else 8)

def full : Tensor := allGatherPrimDimN 0 2 0 [x0, x1]
def z0 : Tensor := fw_maybe_shuffle_collective [x0, x1] (decodeCuSeqlens cu) 2 0
def z1 : Tensor := fw_maybe_shuffle_collective [x0, x1] (decodeCuSeqlens cu) 2 1

/-- A concrete compatible RMSNorm scale, not a shape-only proxy. -/
def rmsWeight : Tensor :=
  Tensor.mkShape [1] (fun _ => (2 : Scalar))

/-- A concrete two-head per-head-linear weight `[hW, dW, k] = [2, 1, 1]`. -/
def perHeadWeight : Tensor :=
  Tensor.mkShape [2, 1, 1] (fun i => if i.val = 0 then 2 else 3)

@[simp] theorem perHeadWeight_shape : perHeadWeight.shape = [2, 1, 1] := rfl

def observe4 (x : Tensor) : List Scalar := (List.range 4).map (valAt x)

@[simp] theorem x0_shape : x0.shape = [4, 1] := rfl
@[simp] theorem x1_shape : x1.shape = [4, 1] := rfl

@[simp] theorem decode_cu : decodeCuSeqlens cu = [0, 8] := by
  unfold decodeCuSeqlens cu
  have hp : prodShape (Tensor.mkShape [2]
      (fun i => if i.val = 0 then (0 : Scalar) else 8)).shape = 2 := by
    simp [Tensor.mkShape, prodShape]
  rw [hp]
  change (List.range 2).map _ = _
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.map_append]
  simp only [valAt, Tensor.mkShape, prodShape]
  norm_num [scalarToNat]

@[simp] theorem full_shape : full.shape = [8, 1] := by
  unfold full
  rw [allGatherPrimDimN_shape 0 2 _ [4, 1]]
  · norm_num [List.set, List.getD]
  · simp

private theorem fixture_wf : ZigzagCuWF [0, 8] [x0, x1] 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs0 : s = 0 := by simpa using hs
    subst s
    norm_num
  · intro s hs
    have hs0 : s = 0 := by simpa using hs
    subst s
    norm_num
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> norm_num [x0, x1, Tensor.mkShape, zeroTensor]
  · norm_num [x0, Tensor.mkShape, listLast!]

theorem concrete_zigzag2Rel : Zigzag2Rel full z0 z1 cu [8, 1] [4, 1] := by
  apply Zigzag2Rel.of_sources x0 x1
  · rfl
  · rfl
  · rfl
  · exact full_shape
  · exact x0_shape
  · exact x1_shape
  · simpa only [decode_cu] using fixture_wf

-- The relation is inhabited by actual, unequal layouts rather than a contradictory premise.
theorem concrete_nonvacuity :
    ∃ full z0 z1 cu, Zigzag2Rel full z0 z1 cu [8, 1] [4, 1] :=
  ⟨full, z0, z1, cu, concrete_zigzag2Rel⟩

/-- RED/GREEN regression: actual RMSNorm outputs preserve the faithful zigzag
source relation with the same concrete full and shard shapes. -/
theorem concrete_rms_norm_zigzag2Rel :
    Zigzag2Rel
      (fw_rms_norm full rmsWeight)
      (fw_rms_norm z0 rmsWeight)
      (fw_rms_norm z1 rmsWeight)
      cu [8, 1] [4, 1] := by
  apply Zigzag2Rel.rms_norm (lDim := 4) (h := 1) concrete_zigzag2Rel
  · norm_num
  · norm_num
  · rfl

/-- Concrete RED/GREEN regression for the generic per-head-linear transport.
These are actual Denote tensors, with full output `[8, 2, 1]` and shuffled
rank outputs `[4, 2, 1]`. -/
theorem concrete_per_head_linear_zigzag2Rel :
    Zigzag2Rel
      (fw_per_head_linear full perHeadWeight)
      (fw_per_head_linear z0 perHeadWeight)
      (fw_per_head_linear z1 perHeadWeight)
      cu [8, 2, 1] [4, 2, 1] := by
  apply Zigzag2Rel.per_head_linear (lDim := 4) (k := 1) (hW := 2) (dW := 1)
    concrete_zigzag2Rel perHeadWeight_shape
  all_goals norm_num

/-- The concrete outputs expose the promised three-dimensional shapes. -/
theorem concrete_per_head_linear_shapes :
    (fw_per_head_linear full perHeadWeight).shape = [8, 2, 1] ∧
    (fw_per_head_linear z0 perHeadWeight).shape = [4, 2, 1] ∧
    (fw_per_head_linear z1 perHeadWeight).shape = [4, 2, 1] :=
  concrete_per_head_linear_zigzag2Rel.output_shapes

theorem shard_shapes : x0.shape = [4, 1] ∧ x1.shape = [4, 1] ∧
    z0.shape = [4, 1] ∧ z1.shape = [4, 1] := by
  exact ⟨x0_shape, x1_shape, concrete_zigzag2Rel.rank0_shape,
    concrete_zigzag2Rel.rank1_shape⟩

theorem observed_z0 : observe4 z0 = [0, 1, 6, 7] := by
  have h0 : valAt z0 0 = 0 := by
    unfold z0
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  have h1 : valAt z0 1 = 1 := by
    unfold z0
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  have h2 : valAt z0 2 = 6 := by
    unfold z0
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  have h3 : valAt z0 3 = 7 := by
    unfold z0
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  unfold observe4
  norm_num [List.range_succ, h0, h1, h2, h3]

theorem observed_z1 : observe4 z1 = [2, 3, 4, 5] := by
  have h0 : valAt z1 0 = 2 := by
    unfold z1
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  have h1 : valAt z1 1 = 3 := by
    unfold z1
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  have h2 : valAt z1 2 = 4 := by
    unfold z1
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  have h3 : valAt z1 3 = 5 := by
    unfold z1
    rw [fw_maybe_shuffle_collective_valAt] <;>
      norm_num [decode_cu, gatherFromRank, zigzagPos, zigzagPosAux, sliceSizeAt,
        List.getD, prodShape, x0, x1, Tensor.mkShape]
  unfold observe4
  norm_num [List.range_succ, h0, h1, h2, h3]

end
end TrainVerify.Denote.ZigzagLayoutRelRegression
