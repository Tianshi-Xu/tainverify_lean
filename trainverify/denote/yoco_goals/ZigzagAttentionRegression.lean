/-
Generated-node regression for source-faithful forward zigzag attention.
-/
import denote.DenoteDistributedFaithful
import denote.GeneratedYOCOMoE

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.ZigzagAttentionRegression
noncomputable section

set_option maxRecDepth 100000
set_option linter.style.nativeDecide false

private def dummyNode : NodeDecl := { rank := 0, op := "", ins := [], outs := [] }

def smAttn : NodeDecl := sm.nodes.getD 505 dummyNode
def pmAttn0 : NodeDecl := pm.nodes.getD 1072 dummyNode
def pmAttn1 : NodeDecl := pm.nodes.getD 1073 dummyNode

/-- These are the actual generated SM/PM declarations requested by the regression. -/
theorem smAttn_generated : smAttn =
    { rank := 0, op := "OpName.FW_attn_zigzag",
      ins := [5342, 5343, 5344, 5345, 5346], outs := [5347],
      params := [16, 4, 64, 64, 1, 0] } := by
  native_decide

theorem pmAttn0_generated : pmAttn0 =
    { rank := 0, op := "OpName.FW_attn_zigzag",
      ins := [9659, 5343, 5344, 5345, 5346], outs := [9687],
      params := [16, 4, 64, 64, 1, 0] } := by
  native_decide

theorem pmAttn1_generated : pmAttn1 =
    { rank := 1, op := "OpName.FW_attn_zigzag",
      ins := [9660, 5343, 5344, 5345, 5346], outs := [9688],
      params := [16, 4, 64, 64, 1, 0] } := by
  native_decide

/-- Replica metadata, including its order, is generated rather than inferred. -/
theorem pmAttn_buddies :
    pm.replicaBuddies pmAttn0 = [pmAttn0, pmAttn1] ∧
    pm.replicaBuddies pmAttn1 = [pmAttn0, pmAttn1] := by
  native_decide

def qShard (start : Nat) : Tensor :=
  Tensor.mkShape [4, 16, 1] (fun i => ((start + i.val : Nat) : Scalar))

def fullKV (bias : Nat) : Tensor :=
  Tensor.mkShape [8, 4, 1] (fun i => ((bias + i.val : Nat) : Scalar))

def cuTensor : Tensor :=
  Tensor.mkShape [2] (fun i => if i.val = 0 then 0 else 8)

def attnStore : Store := fun tid =>
  if tid = 5342 then qShard 0
  else if tid = 9659 then qShard 0
  else if tid = 9660 then qShard 64
  else if tid = 5343 then fullKV 1000
  else if tid = 5344 then fullKV 2000
  else if tid = 5345 then cuTensor
  else if tid = 5346 then cuTensor
  else zeroTensor []

@[simp] theorem decode_cuTensor : decodeCuSeqlens cuTensor = [0, 8] := by
  unfold decodeCuSeqlens cuTensor
  have hp : prodShape (Tensor.mkShape [2]
      (fun i => if i.val = 0 then (0 : Scalar) else 8)).shape = 2 := by
    simp [Tensor.mkShape, prodShape]
  rw [hp]
  change (List.range 2).map _ = _
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.map_append]
  simp only [valAt, Tensor.mkShape, prodShape]
  norm_num [scalarToNat]

/-- CP1 is exactly ordinary `fw_attn_varlen`, not merely shape-compatible. -/
theorem sm_cp1_collapses_to_varlen :
    applyNodeDistributedFaithful sm attnStore smAttn 5347 =
      fw_attn_varlen (qShard 0) (fullKV 1000) (fullKV 2000)
        cuTensor cuTensor 16 4 64 64 true 0 := by
  rw [smAttn_generated, applyNodeDistributedFaithful_zigzag_attn_out]
  unfold applyNodeFaithfulZigzagAttnValue
  have hb : sm.replicaBuddies
      ({ rank := 0, op := "OpName.FW_attn_zigzag",
         ins := [5342, 5343, 5344, 5345, 5346], outs := [5347],
         params := [16, 4, 64, 64, 1, 0] } : NodeDecl) =
      [{ rank := 0, op := "OpName.FW_attn_zigzag",
         ins := [5342, 5343, 5344, 5345, 5346], outs := [5347],
         params := [16, 4, 64, 64, 1, 0] }] := by native_decide
  rw [hb]
  have hranks : sm.numRanks = 1 := by native_decide
  rw [hranks]
  simp [attnStore, fw_attn_zigzag_collective]

/-- Rank 0 computes full attention from unshuffled/gathered Q, chunks it, then
reshuffles the chunks.  K/V occur exactly once and are the local generated inputs. -/
theorem pm_rank0_source_formula :
    applyNodeDistributedFaithful pm attnStore pmAttn0 9687 =
      let qs := [qShard 0, qShard 64]
      let linearQs := (List.range 2).map (fun r =>
        fw_maybe_unshuffle_collective qs [0, 8] 2 r)
      let fullOut := fw_attn_varlen (allGatherPrimDimN 0 2 0 linearQs)
        (fullKV 1000) (fullKV 2000) cuTensor cuTensor 16 4 64 64 true 0
      fw_maybe_shuffle_collective
        ((List.range 2).map (fun r => chunkPrimDimN 0 2 r fullOut)) [0, 8] 2 0 := by
  rw [pmAttn0_generated, applyNodeDistributedFaithful_zigzag_attn_out]
  rw [← pmAttn0_generated]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [pmAttn_buddies.1]
  simp only [List.map]
  rw [pmAttn0_generated, pmAttn1_generated]
  have hranks : pm.numRanks = 2 := by native_decide
  rw [hranks]
  simp [attnStore, fw_attn_zigzag_collective, decode_cuTensor]

/-- The second generated replica has the same full-Q computation and preserves rank
1's zigzag order in the final shuffle. -/
theorem pm_rank1_source_formula :
    applyNodeDistributedFaithful pm attnStore pmAttn1 9688 =
      let qs := [qShard 0, qShard 64]
      let linearQs := (List.range 2).map (fun r =>
        fw_maybe_unshuffle_collective qs [0, 8] 2 r)
      let fullOut := fw_attn_varlen (allGatherPrimDimN 0 2 0 linearQs)
        (fullKV 1000) (fullKV 2000) cuTensor cuTensor 16 4 64 64 true 0
      fw_maybe_shuffle_collective
        ((List.range 2).map (fun r => chunkPrimDimN 0 2 r fullOut)) [0, 8] 2 1 := by
  rw [pmAttn1_generated, applyNodeDistributedFaithful_zigzag_attn_out]
  rw [← pmAttn1_generated]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [pmAttn_buddies.2]
  simp only [List.map]
  rw [pmAttn0_generated, pmAttn1_generated]
  have hranks : pm.numRanks = 2 := by native_decide
  rw [hranks]
  simp [attnStore, fw_attn_zigzag_collective, decode_cuTensor]

/-- The concrete generated CP2 outputs retain local Q length and attention width. -/
theorem pm_generated_shapes :
    (applyNodeDistributedFaithful pm attnStore pmAttn0 9687).shape = [4, 16, 64] ∧
    (applyNodeDistributedFaithful pm attnStore pmAttn1 9688).shape = [4, 16, 64] := by
  rw [pm_rank0_source_formula, pm_rank1_source_formula]
  simp only [List.range_succ, List.range_zero, List.map, decode_cuTensor]
  simp [fw_maybe_shuffle_collective_shape, chunkPrimDimN, fw_attn_varlen,
    allGatherPrimDimN, fw_maybe_unshuffle_collective_shape, qShard, fullKV,
    Tensor.mkShape, List.set, List.getD]

/-- Backward zigzag attention remains delegated; there is no backward interception. -/
example (s : Store) (n : NodeDecl)
    (hs : n.op ≠ "OpName.FW_maybe_shuffle")
    (hu : n.op ≠ "OpName.FW_maybe_unshuffle")
    (ha : n.op ≠ "OpName.FW_attn_zigzag") :
    applyNodeDistributedFaithful pm s n = applyNodeDistributed pm s n :=
  applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective pm s n hs hu ha

end
end TrainVerify.Denote.ZigzagAttentionRegression
