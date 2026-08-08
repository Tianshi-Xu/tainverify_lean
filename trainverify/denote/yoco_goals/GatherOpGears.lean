/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.Gather2Rel
import denote.ZigzagCollective

/-!
# Operator propagation for `Gather2Rel`

`Gather2Rel` shipped with only pack/unpack gears (`of_initGoalHolds` /
`to_initGoalHolds`). Once the zigzag exit hands control back to the ordinary
dim-0 gather world, the remaining chain still needs per-operator propagation.

This file adds those gears. They are markedly simpler than their `Zigzag2Rel`
counterparts: there is no zigzag layout and no cu metadata to carry, so a gear
reduces to "the operator commutes with `allGatherPrimDimN 0 2 0`" plus shape
bookkeeping. The commutation lemmas already exist in `ZigzagCollective`; they
were stated generically over the gather primitive and are reused verbatim here.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-- Row-local RMSNorm preserves a dim-0 two-shard gather relation. -/
theorem Gather2Rel.rms_norm
    {full shard0 shard1 w : Tensor} (lDim hM : Nat)
    (hrel : Gather2Rel full shard0 shard1 [lDim * 2, hM] [lDim, hM])
    (hl : 0 < lDim) (hh : 0 < hM) :
    Gather2Rel (fw_rms_norm full w) (fw_rms_norm shard0 w) (fw_rms_norm shard1 w)
      [lDim * 2, hM] [lDim, hM] := by
  refine ⟨?_, ?_, ?_, ?_, hrel.nonscalar⟩
  · rw [hrel.value]
    exact fw_rms_norm_allGather0_commute_2_core shard0 shard1 w lDim hM hl hh
      hrel.shard0_shape hrel.shard1_shape
  · rw [hrel.value]
    rw [fw_rms_norm_allGather0_commute_2_core shard0 shard1 w lDim hM hl hh
      hrel.shard0_shape hrel.shard1_shape]
    have h0 : (fw_rms_norm shard0 w).shape = [lDim, hM] :=
      fw_rms_norm_shape_2d shard0 w lDim hM hrel.shard0_shape
    have hhead : ((([fw_rms_norm shard0 w, fw_rms_norm shard1 w] : List Tensor)).head?.map
        (fun t => t.shape)).getD [] = [lDim, hM] := by simp [h0]
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, hM] hhead]
    simp [List.set, List.getD]
  · exact fw_rms_norm_shape_2d shard0 w lDim hM hrel.shard0_shape
  · exact fw_rms_norm_shape_2d shard1 w lDim hM hrel.shard1_shape

/-- A replicated per-head projection preserves a dim-0 two-shard gather relation. -/
theorem Gather2Rel.per_head_linear
    {full shard0 shard1 w : Tensor} (lDim k hW dW : Nat)
    (hrel : Gather2Rel full shard0 shard1 [lDim * 2, k] [lDim, k])
    (hw : w.shape = [hW, dW, k])
    (hl : 0 < lDim) (hk : 0 < k) (hhW : 0 < hW) (hdW : 0 < dW) :
    Gather2Rel (fw_per_head_linear full w) (fw_per_head_linear shard0 w)
      (fw_per_head_linear shard1 w) [lDim * 2, hW, dW] [lDim, hW, dW] := by
  have h0 := fw_per_head_linear_shape_2d shard0 w lDim k hW dW
    hrel.shard0_shape hw
  have h1 := fw_per_head_linear_shape_2d shard1 w lDim k hW dW
    hrel.shard1_shape hw
  refine ⟨?_, ?_, h0, h1, ?_⟩
  · rw [hrel.value]
    exact fw_per_head_mix_precision_linear_allGather0_commute_2
      shard0 shard1 w lDim k hW dW hl hk hhW hdW
      hrel.shard0_shape hrel.shard1_shape hw
  · rw [hrel.value,
      fw_per_head_mix_precision_linear_allGather0_commute_2
        shard0 shard1 w lDim k hW dW hl hk hhW hdW
        hrel.shard0_shape hrel.shard1_shape hw]
    have hhead :
        ((([fw_per_head_linear shard0 w, fw_per_head_linear shard1 w] : List Tensor)).head?.map
          (fun t => t.shape)).getD [] = [lDim, hW, dW] := by
      simp [h0]
    rw [allGatherPrimDimN_shape 0 2 _ [lDim, hW, dW] hhead]
    simp [List.set, List.getD]
  · intro hscalar
    have := congrArg List.length hscalar
    simp at this

end

end TrainVerify.Denote.GeneratedPatterns
