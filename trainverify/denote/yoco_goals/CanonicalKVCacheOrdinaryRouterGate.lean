/- Canonical Goal 1 ordinary dim-0 router and scalar-gate closure. -/
import denote.yoco_goals.CanonicalKVCacheOrdinaryNorm
import denote.yoco_goals.CanonicalKVCacheOrdinaryOps

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private theorem ordinary_fw_norm_linear_shape (b k n : Nat) (x w : Tensor)
    (hn : 0 < n) (hx : x.shape = [b, k]) (hw : w.shape = [n, k]) :
    (fw_norm_linear x w).shape = [b, n] := by
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  unfold fw_norm_linear
  rw [hx, hw]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, if_neg hn0]
  rfl

private theorem ordinary_fw_linear_shape (b k n : Nat) (x w : Tensor)
    (hx : x.shape = [b, k]) (hw : w.shape = [n, k]) :
    (fw_linear x w).shape = [b, n] := by
  rw [fw_linear_is_matmul b k n x w hx hw]
  rfl

private theorem ordinary_fw_view_id (x : Tensor) (target : Shape)
    (hx : x.shape = target) : fw_view target x = x := by
  apply Tensor.ext
  · exact hx.symm
  · intro idx hidx
    change idx < prodShape target at hidx
    unfold fw_view
    rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hidx)]
    rfl

namespace Gather2Rel

/-- Every row-local operator transports an ordinary two-shard dim-0 relation. -/
theorem rowLocal {full shard0 shard1 : Tensor} (f : Tensor → Tensor)
    (d e lDim : Nat) (hd : 0 < d) (he : 0 < e) (hl : 0 < lDim)
    (hshape : OrdinaryRowLocalShape f d e) (hcongr : OrdinaryRowLocalCongr f d e)
    (h : Gather2Rel full shard0 shard1 [lDim * 2, d] [lDim, d]) :
    Gather2Rel (f full) (f shard0) (f shard1) [lDim * 2, e] [lDim, e] := by
  refine ⟨?_, hshape (lDim * 2) full h.full_shape,
    hshape lDim shard0 h.shard0_shape, hshape lDim shard1 h.shard1_shape, by simp⟩
  rw [h.value]
  exact ordinary_rowLocal_allGather0_commute_2 f d e lDim hd he hl hshape hcongr
    shard0 shard1 h.shard0_shape h.shard1_shape

/-- Replicated norm-linear preserves ordinary dim-0 layout. -/
theorem norm_linear {full shard0 shard1 w : Tensor} (lDim k n : Nat)
    (h : Gather2Rel full shard0 shard1 [lDim * 2, k] [lDim, k])
    (hw : w.shape = [n, k]) (hl : 0 < lDim) (hk : 0 < k) (hn : 0 < n) :
    Gather2Rel (fw_norm_linear full w) (fw_norm_linear shard0 w)
      (fw_norm_linear shard1 w) [lDim * 2, n] [lDim, n] := by
  refine ⟨?_, ordinary_fw_norm_linear_shape (lDim * 2) k n full w hn h.full_shape hw,
    ordinary_fw_norm_linear_shape lDim k n shard0 w hn h.shard0_shape hw,
    ordinary_fw_norm_linear_shape lDim k n shard1 w hn h.shard1_shape hw, by simp⟩
  rw [h.value]
  exact fw_norm_linear_allGather0_commute_2 shard0 shard1 w lDim k n
    hl hk hn h.shard0_shape h.shard1_shape hw

/-- Routing probabilities preserve ordinary dim-0 layout. -/
theorem topk_probs {full shard0 shard1 : Tensor} (lDim experts topk : Nat)
    (h : Gather2Rel full shard0 shard1 [lDim * 2, experts] [lDim, experts])
    (hl : 0 < lDim) (he : 0 < experts) :
    Gather2Rel (fw_topk_routing full topk experts).1
      (fw_topk_routing shard0 topk experts).1
      (fw_topk_routing shard1 topk experts).1
      [lDim * 2, experts] [lDim, experts] :=
  rowLocal (fun x => (fw_topk_routing x topk experts).1)
    experts experts lDim he he hl
    (OrdinaryRowLocalShape_topk_fst experts topk he)
    (OrdinaryRowLocalCongr_topk_fst experts topk he) h

/-- Routing maps preserve ordinary dim-0 layout. -/
theorem topk_map {full shard0 shard1 : Tensor} (lDim experts topk : Nat)
    (h : Gather2Rel full shard0 shard1 [lDim * 2, experts] [lDim, experts])
    (hl : 0 < lDim) (he : 0 < experts) :
    Gather2Rel (fw_topk_routing full topk experts).2.1
      (fw_topk_routing shard0 topk experts).2.1
      (fw_topk_routing shard1 topk experts).2.1
      [lDim * 2, experts] [lDim, experts] :=
  rowLocal (fun x => (fw_topk_routing x topk experts).2.1)
    experts experts lDim he he hl
    (OrdinaryRowLocalShape_topk_snd experts topk he)
    (OrdinaryRowLocalCongr_topk_snd experts topk he) h

/-- An identity reshape preserves the ordinary relation. -/
theorem view_id {full shard0 shard1 : Tensor} {fullShape shardShape : Shape}
    (h : Gather2Rel full shard0 shard1 fullShape shardShape) :
    Gather2Rel (fw_view fullShape full) (fw_view shardShape shard0)
      (fw_view shardShape shard1) fullShape shardShape := by
  rw [ordinary_fw_view_id full fullShape h.full_shape,
    ordinary_fw_view_id shard0 shardShape h.shard0_shape,
    ordinary_fw_view_id shard1 shardShape h.shard1_shape]
  exact h

/-- A replicated 2-D linear preserves ordinary dim-0 layout. -/
theorem linear {full shard0 shard1 w : Tensor} (lDim inDim outDim : Nat)
    (h : Gather2Rel full shard0 shard1 [lDim * 2, inDim] [lDim, inDim])
    (hw : w.shape = [outDim, inDim])
    (hl : 0 < lDim) (hin : 0 < inDim) (hout : 0 < outDim) :
    Gather2Rel (fw_linear full w) (fw_linear shard0 w) (fw_linear shard1 w)
      [lDim * 2, outDim] [lDim, outDim] := by
  refine ⟨?_, ordinary_fw_linear_shape (lDim * 2) inDim outDim full w h.full_shape hw,
    ordinary_fw_linear_shape lDim inDim outDim shard0 w h.shard0_shape hw,
    ordinary_fw_linear_shape lDim inDim outDim shard1 w h.shard1_shape hw, by simp⟩
  rw [h.value]
  exact fw_mix_precision_linear_allGather0_commute_2 shard0 shard1 w
    lDim inDim outDim hl hin hout h.shard0_shape h.shard1_shape hw

/-- Sigmoid is pointwise and preserves ordinary dim-0 layout. -/
theorem sigmoid {full shard0 shard1 : Tensor} (lDim d : Nat)
    (h : Gather2Rel full shard0 shard1 [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    Gather2Rel (fw_sigmoid full) (fw_sigmoid shard0) (fw_sigmoid shard1)
      [lDim * 2, d] [lDim, d] := by
  have hshape : OrdinaryRowLocalShape fw_sigmoid d d := by
    intro a x hx
    rw [TrainVerify.Denote.fw_sigmoid_shape, hx]
  have hcongr : OrdinaryRowLocalCongr fw_sigmoid d d := by
    intro a b x y ix iy c hx hy hix hiy hc hrow
    have hxi : ix * d + c < prodShape x.shape := by
      rw [hx, ordinary_prodShape_2d]
      calc ix * d + c < ix * d + d := Nat.add_lt_add_left hc _
        _ = (ix + 1) * d := by ring
        _ ≤ a * d := Nat.mul_le_mul_right d hix
    have hyi : iy * d + c < prodShape y.shape := by
      rw [hy, ordinary_prodShape_2d]
      calc iy * d + c < iy * d + d := Nat.add_lt_add_left hc _
        _ = (iy + 1) * d := by ring
        _ ≤ b * d := Nat.mul_le_mul_right d hiy
    have hxy := hrow c hc
    unfold valAt at hxy
    simp only [dif_pos hxi, dif_pos hyi] at hxy
    unfold fw_sigmoid Tensor.mkShape valAt
    simp only [dif_pos hxi, dif_pos hyi]
    exact congrArg sigmoidScalar hxy
  exact rowLocal fw_sigmoid d d lDim hd hd hl hshape hcongr h

end Gather2Rel

/-- The real cache router probabilities and map preserve ordinary dim-0 layout.
The gather/float/norm-linear/chunk/top-k graph path and replicated router weight
are all discharged internally. -/
theorem canonical_kv_cache_ordinary_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9637)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5568)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9647)
      [4096, 64] [2048, 64] ∧
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5569)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9649)
      [4096, 64] [2048, 64] := by
  have hwEq := cKVCr_weight_eq initSM initPM hInit
  have hwShape := cKVCr_weight_shape initPM hPM
  have hLocal := Gather2Rel.norm_linear 2048 1024 64 hNorm hwShape
    (by decide) (by decide) (by decide)
  have hp0Shape := hLocal.shard0_shape
  have hp1Shape := hLocal.shard1_shape
  have hLogits : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5567)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9644)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9645)
      [4096, 64] [2048, 64] := by
    rw [cKVCr_red_sm5567 initSM, cKVCr_red_sm5565 initSM,
      cKVCr_red_sm8348 initSM, hwEq,
      cKVCr_red_pm9644 initPM, cKVCr_red_pm9645 initPM,
      cKVCr_red_pm5567 initPM, cKVCr_red_pm5565 initPM,
      cKVCr_red_pm12094 initPM, cKVCr_red_pm15384 initPM,
      cKVCr_red_pm15386 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hNorm.shard0_shape hNorm.shard1_shape hwShape,
      cKVCr_chunk_gather0 _ _ hp0Shape hp1Shape,
      cKVCr_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hLocal
  have hProbs := Gather2Rel.topk_probs 2048 64 8 hLogits (by decide) (by decide)
  have hMap := Gather2Rel.topk_map 2048 64 8 hLogits (by decide) (by decide)
  rw [cKVCr_red_sm5568 initSM hLogits.full_shape,
    cKVCr_red_pm9646 initPM hLogits.shard0_shape,
    cKVCr_red_pm9647 initPM hLogits.shard1_shape,
    cKVCr_red_sm5569 initSM hLogits.full_shape,
    cKVCr_red_pm9648 initPM hLogits.shard0_shape,
    cKVCr_red_pm9649 initPM hLogits.shard1_shape]
  exact ⟨hProbs, hMap⟩

/-- The real scalar-gate branch preserves ordinary dim-0 layout. -/
theorem canonical_kv_cache_ordinary_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9637)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
      [4096, 1] [2048, 1] := by
  have hSource : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8356)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13807)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCrg_red_sm8356 initSM, cKVCrg_red_pm13806 initPM,
      cKVCrg_red_pm13807 initPM]
    exact hNorm
  have hReshape : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5574)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9658)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9659)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCrg_red_sm5574 initSM, cKVCrg_red_pm9658 initPM,
      cKVCrg_red_pm9659 initPM]
    exact Gather2Rel.view_id hSource
  have hwEq := cKVCrg_weight_eq initSM initPM hInit
  have hwShape := cKVCrg_weight_shape initPM hPM
  have hLinear : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5576)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9662)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9663)
      [4096, 1] [2048, 1] := by
    rw [cKVCrg_red_sm5576 initSM, cKVCrg_red_pm9662 initPM,
      cKVCrg_red_pm9663 initPM, hwEq]
    exact Gather2Rel.linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5577)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9665)
      [4096, 1] [2048, 1] := by
    rw [cKVCrg_red_sm5577 initSM, cKVCrg_red_pm9664 initPM,
      cKVCrg_red_pm9665 initPM]
    exact Gather2Rel.view_id hLinear
  rw [cKVCrg_red_sm5578 initSM, cKVCrg_red_pm9666 initPM,
    cKVCrg_red_pm9667 initPM]
  exact Gather2Rel.sigmoid 2048 1 hView (by decide) (by decide)

/-- Both ordinary router outputs are closed directly from attention output. -/
theorem canonical_kv_cache_ordinary_router_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5568)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9647)
      [4096, 64] [2048, 64] ∧
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5569)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9649)
      [4096, 64] [2048, 64] := by
  have hNorm := canonical_kv_cache_ordinary_norm_from_attention_output
    initSM initPM hInit hAttention
  exact canonical_kv_cache_ordinary_router_from_norm_input initSM initPM hPM hInit hNorm

/-- The ordinary scalar gate is closed directly from attention output. -/
theorem canonical_kv_cache_ordinary_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
      [4096, 1] [2048, 1] := by
  have hNorm := canonical_kv_cache_ordinary_norm_from_attention_output
    initSM initPM hInit hAttention
  exact canonical_kv_cache_ordinary_gate_from_norm_input initSM initPM hPM hInit hNorm

#print axioms canonical_kv_cache_ordinary_router_from_norm_input
#print axioms canonical_kv_cache_ordinary_gate_from_norm_input
#print axioms canonical_kv_cache_ordinary_router_from_attention_output
#print axioms canonical_kv_cache_ordinary_gate_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
