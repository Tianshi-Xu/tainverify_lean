/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.DenoteDistributedFaithful

/-!
# Source-witness relation for two-rank zigzag layouts

`Zigzag2Rel` relates an ordinary full tensor to the two *shuffled* context-parallel
shards. Its witnesses are ordinary contiguous source shards: the full tensor is
their ordinary dim-0 gather, while each exposed shard is the corresponding
value-faithful collective shuffle over decoded cumulative-sequence metadata.

The relation deliberately does **not** assert that `z0` and `z1` ordinary-gather
to `full`. Such a statement is false before unshuffling.
-/

open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.GeneratedPatterns
noncomputable section

/-- Proof payload for a fixed pair of ordinary source shards. -/
structure Zigzag2Sources
    (full z0 z1 cu source0 source1 : Tensor)
    (fullShape shardShape : Shape) : Prop where
  full_value : full = allGatherPrimDimN 0 2 0 [source0, source1]
  rank0_value : z0 = fw_maybe_shuffle_collective
    [source0, source1] (decodeCuSeqlens cu) 2 0
  rank1_value : z1 = fw_maybe_shuffle_collective
    [source0, source1] (decodeCuSeqlens cu) 2 1
  full_shape : full.shape = fullShape
  source0_shape : source0.shape = shardShape
  source1_shape : source1.shape = shardShape
  rank0_shape : z0.shape = shardShape
  rank1_shape : z1.shape = shardShape
  cu_wf : ZigzagCuWF (decodeCuSeqlens cu) [source0, source1] 2

/-- A full tensor and two CP2 zigzag shards, pinned existentially to ordinary
contiguous source shards. -/
def Zigzag2Rel
    (full z0 z1 cu : Tensor) (fullShape shardShape : Shape) : Prop :=
  ∃ source0 source1,
    Zigzag2Sources full z0 z1 cu source0 source1 fullShape shardShape

namespace Zigzag2Rel

/-- Build the relation from ordinary source shards. Shuffle shapes follow from
shape preservation, so callers only provide source and full shape facts. -/
theorem of_sources
    {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (source0 source1 : Tensor)
    (hfull : full = allGatherPrimDimN 0 2 0 [source0, source1])
    (hz0 : z0 = fw_maybe_shuffle_collective
      [source0, source1] (decodeCuSeqlens cu) 2 0)
    (hz1 : z1 = fw_maybe_shuffle_collective
      [source0, source1] (decodeCuSeqlens cu) 2 1)
    (hfullShape : full.shape = fullShape)
    (hsource0Shape : source0.shape = shardShape)
    (hsource1Shape : source1.shape = shardShape)
    (hwf : ZigzagCuWF (decodeCuSeqlens cu) [source0, source1] 2) :
    Zigzag2Rel full z0 z1 cu fullShape shardShape := by
  refine ⟨source0, source1, hfull, hz0, hz1, hfullShape,
    hsource0Shape, hsource1Shape, ?_, ?_, hwf⟩
  · rw [hz0, fw_maybe_shuffle_collective_shape]
    exact hsource0Shape
  · rw [hz1, fw_maybe_shuffle_collective_shape]
    exact hsource1Shape

/-- Eliminate the hidden ordinary sources while retaining all value equations. -/
theorem values {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (h : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    ∃ source0 source1,
      full = allGatherPrimDimN 0 2 0 [source0, source1] ∧
      z0 = fw_maybe_shuffle_collective
        [source0, source1] (decodeCuSeqlens cu) 2 0 ∧
      z1 = fw_maybe_shuffle_collective
        [source0, source1] (decodeCuSeqlens cu) 2 1 := by
  rcases h with ⟨source0, source1, hs⟩
  exact ⟨source0, source1, hs.full_value, hs.rank0_value, hs.rank1_value⟩

/-- Eliminate the hidden ordinary sources with exact shapes and metadata WF. -/
theorem sources {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (h : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    ∃ source0 source1,
      source0.shape = shardShape ∧ source1.shape = shardShape ∧
      ZigzagCuWF (decodeCuSeqlens cu) [source0, source1] 2 := by
  rcases h with ⟨source0, source1, hs⟩
  exact ⟨source0, source1, hs.source0_shape, hs.source1_shape, hs.cu_wf⟩

/-- Accessor for the exact full shape. -/
theorem full_shape {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (h : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    full.shape = fullShape := by
  rcases h with ⟨_, _, hs⟩
  exact hs.full_shape

/-- Accessor for rank zero's exact shuffled-shard shape. -/
theorem rank0_shape {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (h : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    z0.shape = shardShape := by
  rcases h with ⟨_, _, hs⟩
  exact hs.rank0_shape

/-- Accessor for rank one's exact shuffled-shard shape. -/
theorem rank1_shape {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (h : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    z1.shape = shardShape := by
  rcases h with ⟨_, _, hs⟩
  exact hs.rank1_shape

/-- The public tensors carry exactly the declared full/shard shapes. -/
theorem output_shapes {full z0 z1 cu : Tensor} {fullShape shardShape : Shape}
    (h : Zigzag2Rel full z0 z1 cu fullShape shardShape) :
    full.shape = fullShape ∧ z0.shape = shardShape ∧ z1.shape = shardShape :=
  ⟨h.full_shape, h.rank0_shape, h.rank1_shape⟩

/-- Row-local RMSNorm preserves the full/source/shuffled value relation. -/
theorem rms_norm
    {full z0 z1 cu w : Tensor} {fullShape shardShape : Shape}
    (lDim h : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu fullShape shardShape)
    (hl : 0 < lDim) (hh : 0 < h)
    (hshard : shardShape = [lDim, h]) :
    Zigzag2Rel
      (fw_rms_norm full w) (fw_rms_norm z0 w) (fw_rms_norm z1 w)
      cu fullShape shardShape := by
  rcases hrel with ⟨source0, source1, hs⟩
  have hs0 : source0.shape = [lDim, h] := hs.source0_shape.trans hshard
  have hs1 : source1.shape = [lDim, h] := hs.source1_shape.trans hshard
  have hfullValue := fw_rms_norm_allGather0_commute_2_core
    source0 source1 w lDim h hl hh hs0 hs1
  have hfullActual : full.shape = [lDim * 2, h] := by
    rw [hs.full_value, allGatherPrimDimN_shape 0 2 _ [lDim, h]]
    · simp [List.set, List.getD]
    · simp [hs0]
  refine ⟨fw_rms_norm source0 w, fw_rms_norm source1 w, ?_, ?_, ?_, ?_,
    (fw_rms_norm_shape_2d source0 w lDim h hs0).trans hshard.symm,
    (fw_rms_norm_shape_2d source1 w lDim h hs1).trans hshard.symm, ?_, ?_,
    ZigzagCuWF.rms_norm_cp2 _ source0 source1 w lDim h hs.cu_wf hs0 hs1⟩
  · rw [hs.full_value]
    exact hfullValue
  · rw [hs.rank0_value]
    exact fw_rms_norm_shuffle_collective_cp2 source0 source1 w
      (decodeCuSeqlens cu) lDim h 0 hl hh (by decide) hs0 hs1
  · rw [hs.rank1_value]
    exact fw_rms_norm_shuffle_collective_cp2 source0 source1 w
      (decodeCuSeqlens cu) lDim h 1 hl hh (by decide) hs0 hs1
  · rw [fw_rms_norm_shape_2d full w (lDim * 2) h hfullActual]
    exact hfullActual.symm.trans hs.full_shape
  · rw [fw_rms_norm_shape_2d z0 w lDim h (hs.rank0_shape.trans hshard)]
    exact hshard.symm
  · rw [fw_rms_norm_shape_2d z1 w lDim h (hs.rank1_shape.trans hshard)]
    exact hshard.symm

/-- A replicated per-head weight preserves the source-witness zigzag relation.
The operation is row-local: it commutes both with the ordinary dim-0 gather and
with each faithful shuffled rank. -/
theorem per_head_linear
    {full z0 z1 cu w : Tensor} (lDim k hW dW : Nat)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, k] [lDim, k])
    (hw : w.shape = [hW, dW, k])
    (hl : 0 < lDim) (hk : 0 < k) (hhW : 0 < hW) (hdW : 0 < dW) :
    Zigzag2Rel
      (fw_per_head_linear full w)
      (fw_per_head_linear z0 w)
      (fw_per_head_linear z1 w)
      cu [lDim * 2, hW, dW] [lDim, hW, dW] := by
  rcases hrel with ⟨source0, source1, hs⟩
  have hs0 : source0.shape = [lDim, k] := hs.source0_shape
  have hs1 : source1.shape = [lDim, k] := hs.source1_shape
  have hfullActual : full.shape = [lDim * 2, k] := hs.full_shape
  have hp0 := fw_per_head_linear_shape_2d source0 w lDim k hW dW hs0 hw
  have hp1 := fw_per_head_linear_shape_2d source1 w lDim k hW dW hs1 hw
  refine ⟨fw_per_head_linear source0 w, fw_per_head_linear source1 w,
    ?_, ?_, ?_, ?_, hp0, hp1, ?_, ?_,
    ZigzagCuWF.per_head_linear_cp2 _ source0 source1 w lDim k hW dW
      hs.cu_wf hs0 hs1 hw⟩
  · rw [hs.full_value]
    exact fw_per_head_mix_precision_linear_allGather0_commute_2
      source0 source1 w lDim k hW dW hl hk hhW hdW hs0 hs1 hw
  · rw [hs.rank0_value]
    exact fw_per_head_linear_shuffle_collective_cp2
      source0 source1 w (decodeCuSeqlens cu) lDim k hW dW 0
      hl hk hhW hdW (by decide) hs0 hs1 hw
  · rw [hs.rank1_value]
    exact fw_per_head_linear_shuffle_collective_cp2
      source0 source1 w (decodeCuSeqlens cu) lDim k hW dW 1
      hl hk hhW hdW (by decide) hs0 hs1 hw
  · exact fw_per_head_linear_shape_2d full w (lDim * 2) k hW dW
      hfullActual hw
  · exact fw_per_head_linear_shape_2d z0 w lDim k hW dW hs.rank0_shape hw
  · exact fw_per_head_linear_shape_2d z1 w lDim k hW dW hs.rank1_shape hw

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
