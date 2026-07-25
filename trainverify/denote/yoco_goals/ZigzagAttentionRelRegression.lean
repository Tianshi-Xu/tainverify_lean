/-
Concrete value regression for faithful zigzag-attention relation preservation.
-/
import denote.yoco_goals.ZigzagAttentionRel

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns.ZigzagAttentionRelRegression
noncomputable section

private def source0 : Tensor :=
  Tensor.mkShape [4, 2, 1] (fun i => ((i.val : Nat) : Scalar))

private def source1 : Tensor :=
  Tensor.mkShape [4, 2, 1] (fun i => ((100 + i.val : Nat) : Scalar))

private def cu : Tensor :=
  Tensor.mkShape [2] (fun i => if i.val = 0 then 0 else 8)

private def fullQ : Tensor := allGatherPrimDimN 0 2 0 [source0, source1]
private def q0 : Tensor := fw_maybe_shuffle_collective [source0, source1] [0, 8] 2 0
private def q1 : Tensor := fw_maybe_shuffle_collective [source0, source1] [0, 8] 2 1
private def k : Tensor := Tensor.mkShape [8, 1, 1] (fun i => ((200 + i.val : Nat) : Scalar))
private def v : Tensor := Tensor.mkShape [8, 1, 1] (fun i => ((300 + i.val : Nat) : Scalar))

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

private theorem source0_shape : source0.shape = [4, 2, 1] := by
  simp [source0, Tensor.mkShape]

private theorem source1_shape : source1.shape = [4, 2, 1] := by
  simp [source1, Tensor.mkShape]

private theorem sources_wf : ZigzagCuWF [0, 8] [source0, source1] 2 := by
  refine ⟨by omega, rfl, rfl, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    norm_num at hs
    have : s = 0 := by omega
    subst s
    decide
  · intro s hs
    norm_num at hs
    have : s = 0 := by omega
    subst s
    decide
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [source0_shape, source1_shape]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp [source0_shape, source1_shape]
  · simp [source0_shape, listLast!]

/-- A concrete, nonzero source fixture genuinely inhabits the input relation. -/
theorem actual_input_relation :
    Zigzag2Rel fullQ q0 q1 cu [8, 2, 1] [4, 2, 1] := by
  apply Zigzag2Rel.of_sources source0 source1
  · rfl
  · rw [decode_cu]
    rfl
  · rw [decode_cu]
    rfl
  · unfold fullQ
    rw [allGatherPrimDimN_shape 0 2 _ [4, 2, 1]]
    · decide
    · simp [source0_shape]
  · exact source0_shape
  · exact source1_shape
  · rw [decode_cu]
    exact sources_wf

private def fullOut : Tensor :=
  fw_attn_varlen fullQ k v cu cu 2 1 1 1 true 0
private def rank0Out : Tensor :=
  fw_attn_zigzag_collective [q0, q1] k v cu cu 2 1 1 1 true 0 2 0
private def rank1Out : Tensor :=
  fw_attn_zigzag_collective [q0, q1] k v cu cu 2 1 1 1 true 0 2 1

/-- Actual tensors and parameters exercise the generic preservation theorem. -/
theorem actual_attention_relation :
    Zigzag2Rel fullOut rank0Out rank1Out cu [8, 2, 1] [4, 2, 1] := by
  exact Zigzag2Rel.attn_zigzag fullQ q0 q1 cu k v cu cu
    4 2 1 1 1 true 0 actual_input_relation rfl decode_cu
    (by omega) (by decide) (by omega) (by omega) (by omega)

/-- The concrete regression also pins all three output shapes. -/
theorem actual_attention_shapes :
    fullOut.shape = [8, 2, 1] ∧
    rank0Out.shape = [4, 2, 1] ∧ rank1Out.shape = [4, 2, 1] :=
  Zigzag2Rel.output_shapes actual_attention_relation

end
end TrainVerify.Denote.GeneratedPatterns.ZigzagAttentionRelRegression
