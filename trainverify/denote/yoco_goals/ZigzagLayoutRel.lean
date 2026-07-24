/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.DenoteDistributedFaithful
import denote.yoco_goals.DistributedMigrationGears

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

end Zigzag2Rel
end
end TrainVerify.Denote.GeneratedPatterns
