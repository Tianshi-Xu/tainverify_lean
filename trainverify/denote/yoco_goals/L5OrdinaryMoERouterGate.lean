/- Canonical Goal 1 ordinary dim-0 router and scalar-gate closure. -/
import denote.yoco_goals.L5OrdinaryMoENorm
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
theorem l5_ordinary_moe_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8653)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5238)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8662)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8663)
      [4096, 64] [2048, 64] ∧
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5239)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8665)
      [4096, 64] [2048, 64] := by
  have hwEq := l5OMr_weight_eq initSM initPM hInit
  have hwShape := l5OMr_weight_shape initPM hPM
  have hLocal := Gather2Rel.norm_linear 2048 1024 64 hNorm hwShape
    (by decide) (by decide) (by decide)
  have hp0Shape := hLocal.shard0_shape
  have hp1Shape := hLocal.shard1_shape
  have hLogits : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5237)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8660)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8661)
      [4096, 64] [2048, 64] := by
    rw [l5OMr_red_sm5237 initSM, l5OMr_red_sm5235 initSM,
      l5OMr_red_sm8036 initSM, hwEq,
      l5OMr_red_pm8660 initPM, l5OMr_red_pm8661 initPM,
      l5OMr_red_pm5237 initPM, l5OMr_red_pm5235 initPM,
      l5OMr_red_pm11902 initPM, l5OMr_red_pm15336 initPM,
      l5OMr_red_pm15338 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hNorm.shard0_shape hNorm.shard1_shape hwShape,
      l5OMr_chunk_gather0 _ _ hp0Shape hp1Shape,
      l5OMr_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hLocal
  have hProbs := Gather2Rel.topk_probs 2048 64 8 hLogits (by decide) (by decide)
  have hMap := Gather2Rel.topk_map 2048 64 8 hLogits (by decide) (by decide)
  rw [l5OMr_red_sm5238 initSM hLogits.full_shape,
    l5OMr_red_pm8662 initPM hLogits.shard0_shape,
    l5OMr_red_pm8663 initPM hLogits.shard1_shape,
    l5OMr_red_sm5239 initSM hLogits.full_shape,
    l5OMr_red_pm8664 initPM hLogits.shard0_shape,
    l5OMr_red_pm8665 initPM hLogits.shard1_shape]
  exact ⟨hProbs, hMap⟩

/-- The real scalar-gate branch preserves ordinary dim-0 layout. -/
theorem l5_ordinary_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8653)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5248)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8682)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8683)
      [4096, 1] [2048, 1] := by
  have hSource : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13051)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMrg_red_sm8044 initSM, l5OMrg_red_pm13050 initPM,
      l5OMrg_red_pm13051 initPM]
    exact hNorm
  have hReshape : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5244)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8675)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMrg_red_sm5244 initSM, l5OMrg_red_pm8674 initPM,
      l5OMrg_red_pm8675 initPM]
    exact Gather2Rel.view_id hSource
  have hwEq := l5OMrg_weight_eq initSM initPM hInit
  have hwShape := l5OMrg_weight_shape initPM hPM
  have hLinear : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8678)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8679)
      [4096, 1] [2048, 1] := by
    rw [l5OMrg_red_sm5246 initSM, l5OMrg_red_pm8678 initPM,
      l5OMrg_red_pm8679 initPM, hwEq]
    exact Gather2Rel.linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5247)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8680)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8681)
      [4096, 1] [2048, 1] := by
    rw [l5OMrg_red_sm5247 initSM, l5OMrg_red_pm8680 initPM,
      l5OMrg_red_pm8681 initPM]
    exact Gather2Rel.view_id hLinear
  rw [l5OMrg_red_sm5248 initSM, l5OMrg_red_pm8682 initPM,
    l5OMrg_red_pm8683 initPM]
  exact Gather2Rel.sigmoid 2048 1 hView (by decide) (by decide)

/-- Both ordinary router outputs are closed directly from attention output. -/
theorem l5_ordinary_moe_router_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5238)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8662)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8663)
      [4096, 64] [2048, 64] ∧
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5239)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8665)
      [4096, 64] [2048, 64] := by
  have hNorm := l5_ordinary_moe_norm_from_attention_output
    initSM initPM hInit hAttention
  exact l5_ordinary_moe_router_from_norm_input initSM initPM hPM hInit hNorm

/-- The ordinary scalar gate is closed directly from attention output. -/
theorem l5_ordinary_moe_gate_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8649)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5248)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8682)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8683)
      [4096, 1] [2048, 1] := by
  have hNorm := l5_ordinary_moe_norm_from_attention_output
    initSM initPM hInit hAttention
  exact l5_ordinary_moe_gate_from_norm_input initSM initPM hPM hInit hNorm

#print axioms l5_ordinary_moe_router_from_norm_input
#print axioms l5_ordinary_moe_gate_from_norm_input
#print axioms l5_ordinary_moe_router_from_attention_output
#print axioms l5_ordinary_moe_gate_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
