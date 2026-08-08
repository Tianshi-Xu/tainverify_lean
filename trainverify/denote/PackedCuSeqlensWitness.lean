/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ZigzagCollective

/-!
# Concrete witness for packed cumulative sequence metadata

This module shows that the caller-visible `PackedCuSeqlensWF` contract is
inhabited.  The witness is the length-two tensor whose values are the cumulative
boundaries `[0, totalTokens]`.
-/

open TrainVerify.Denote

namespace TrainVerify.Denote.ZigzagCollective
noncomputable section

/-- A concrete packed cumulative-sequence tensor for one complete sequence. -/
def packedCuSeqlensSingle (totalTokens : Nat) : Tensor :=
  Tensor.mkShape [2] (fun i =>
    if i.val = 0 then (0 : Scalar) else (totalTokens : Scalar))

@[simp] theorem packedCuSeqlensSingle_shape (totalTokens : Nat) :
    (packedCuSeqlensSingle totalTokens).shape = [2] := by
  rfl

private theorem scalarToNat_natCast (n : Nat) :
    scalarToNat (n : Scalar) = n := by
  unfold scalarToNat
  exact Nat.floor_natCast n

private theorem scalarToNat_zero : scalarToNat (0 : Scalar) = 0 := by
  unfold scalarToNat
  simp

/-- Decoding the concrete tensor exactly recovers its two cumulative boundaries. -/
theorem decode_packedCuSeqlensSingle (totalTokens : Nat) :
    decodeCuSeqlens (packedCuSeqlensSingle totalTokens) = [0, totalTokens] := by
  unfold decodeCuSeqlens packedCuSeqlensSingle
  have hp : prodShape (Tensor.mkShape [2]
      (fun i => if i.val = 0 then (0 : Scalar) else (totalTokens : Scalar))).shape = 2 := by
    simp [Tensor.mkShape, prodShape]
  rw [hp]
  show (List.range 2).map _ = _
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.map_append]
  simp only [valAt, Tensor.mkShape, prodShape]
  simp [scalarToNat_zero, scalarToNat_natCast]

/-- The single-sequence tensor satisfies the packed-metadata contract whenever
context parallelism is positive and the sequence admits `2 * cpSize` slices. -/
theorem packedCuSeqlensSingle_wf
    (totalTokens cpSize : Nat)
    (hcp : 0 < cpSize)
    (hdiv : totalTokens % (2 * cpSize) = 0) :
    PackedCuSeqlensWF (packedCuSeqlensSingle totalTokens) totalTokens cpSize := by
  have hdecode := decode_packedCuSeqlensSingle totalTokens
  refine {
    cp_pos := hcp
    decoded_single := hdecode
    starts_zero := ?_
    has_endpoint := ?_
    monotone := ?_
    divisible := ?_
    endpoint := ?_
  }
  · rw [hdecode]
    rfl
  · rw [hdecode]
    simp
  · intro s hs
    rw [hdecode] at hs ⊢
    norm_num at hs
    have hs0 : s = 0 := by omega
    subst s
    simp
  · intro s hs
    rw [hdecode] at hs ⊢
    norm_num at hs
    have hs0 : s = 0 := by omega
    subst s
    simpa using hdiv
  · rw [hdecode]
    rfl

/-- The concrete Goal 3/4 metadata `[0, 4096]` satisfies the CP2 contract. -/
theorem packedCuSeqlens4096_cp2_wf :
    PackedCuSeqlensWF (packedCuSeqlensSingle 4096) 4096 2 := by
  apply packedCuSeqlensSingle_wf
  · norm_num
  · norm_num

end
end TrainVerify.Denote.ZigzagCollective
