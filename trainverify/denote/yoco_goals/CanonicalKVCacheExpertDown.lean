/- Canonical Goal 1: faithful cache-source expert and dense down relations. -/
import denote.yoco_goals.CanonicalKVCacheBoundary
import denote.yoco_goals.CanonicalL21ExpertDown
import denote.yoco_goals.CanonicalL21Down

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private theorem cKVCed_reduce5
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite, happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4]

private theorem cKVCed_reduce7
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 in5 in6 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4) (s in5) (s in6))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs)
    (hpre5 : ∀ n ∈ g.nodes.drop k, in5 ∉ n.outs)
    (hpre6 : ∀ n ∈ g.nodes.drop k, in6 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4)
        (denoteGraphDistributedFaithful g init in5)
        (denoteGraphDistributedFaithful g init in6) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite, happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4,
    denoteGraphDistributedFaithful_prefix_read g init k in5 hpreNil hpre5,
    denoteGraphDistributedFaithful_prefix_read g init k in6 hpreNil hpre6]

private def cKVCedSmMoE : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [8352, 5568, 5569, 5571, 5572], outs := [5573],
    params := [64, 0, 64, 8] }
private def cKVCedPmMoE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [13796, 9646, 9648, 9652, 9654], outs := [9656],
    params := [64, 0, 32, 8] }
private def cKVCedPmMoE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [13797, 9647, 9649, 9653, 9655], outs := [9657],
    params := [64, 32, 64, 8] }

private theorem cKVCed_buddies :
    sm_goal_1.replicaBuddies cKVCedSmMoE = [cKVCedSmMoE] ∧
    pm_goal_1.replicaBuddies cKVCedPmMoE0 = [cKVCedPmMoE0, cKVCedPmMoE1] ∧
    pm_goal_1.replicaBuddies cKVCedPmMoE1 = [cKVCedPmMoE0, cKVCedPmMoE1] := by
  native_decide

private theorem cKVCed_red_sm5573 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5573 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm_goal_1 initSM 8352)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5568)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5569)
        [denoteGraphDistributedFaithful sm_goal_1 initSM 5571]
        [denoteGraphDistributedFaithful sm_goal_1 initSM 5572]
        64 8 (((10 : Nat) : Scalar)) := by
  refine cKVCed_reduce5 sm_goal_1 initSM 460 cKVCedSmMoE
    8352 5568 5569 5571 5572 5573
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2]
      64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  have hb := cKVCed_buddies.1
  unfold cKVCedSmMoE at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm_goal_1 s 0 8352 5568 5569 5571 5572 5573
    [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem cKVCed_red_pm9656 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9656 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 13796)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9646)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9648)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9652,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9653]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9654,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9655]
        64 8 (((10 : Nat) : Scalar)) := by
  refine cKVCed_reduce7 pm_goal_1 initPM 1027 cKVCedPmMoE0
    13796 9646 9648 9652 9654 9653 9655 9656
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := cKVCed_buddies.2.1
  unfold cKVCedPmMoE0 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 0 13796 9646 9648 9652 9654 9656
    [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem cKVCed_red_pm9657 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9657 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 13797)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9647)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 9649)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9652,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9653]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9654,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9655]
        64 8 (((10 : Nat) : Scalar)) := by
  refine cKVCed_reduce7 pm_goal_1 initPM 1028 cKVCedPmMoE1
    13797 9647 9649 9652 9653 9654 9655 9657
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := cKVCed_buddies.2.2
  unfold cKVCedPmMoE1 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 1 13797 9647 9649 9653 9655 9657
    [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem cKVCed_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem cKVCed_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ goal_1_full_initGoals)
    (W A B : Tid) (shard : Shape)
    (htp : gW.tps = [{rank := 0, tid := A}, {rank := 1, tid := B}])
    (hgd : gW.gatherDim = 0) (hrep : gW.replicated = false) (hts : gW.ts = W)
    (htpShapes : gW.tpShapes = [shard, shard]) (hshard : shard ≠ [1]) :
    initSM W = allGatherPrimDimN 0 2 0 [initPM A, initPM B] := by
  have h := hInit gW hgW
  unfold InitGoalHolds at h
  have hshapes := h.2.1
  rw [htp, htpShapes] at hshapes
  simp only [List.map, List.cons.injEq, and_true] at hshapes
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated gW pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hval
  simp only [List.map] at hval
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_1.numRanks 0 _ _ []
    (by rw [hshapes.1]; exact hshard)] at hval
  rw [show pm_goal_1.numRanks = 2 from rfl] at hval
  exact hval

private theorem cKVCed_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hrel : Zigzag2Rel full z0 z1
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) =
      [0, 2 * 2048] := by
  have hleaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 :=
    cKVCed_leaf pm_goal_1 initPM 6252 (by native_decide) (by native_decide)
  have hcuShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 6252).shape = [2] := by
    rw [hleaf]
    exact hPM 6252 [2] (by native_decide)
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hrel
  apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
  have ht := hs.cu_wf.local_tokens
  simp only [List.getD_cons_zero] at ht
  rw [hs.source0_shape] at ht
  norm_num at ht
  norm_num
  exact ht.symm

/-- The real cache-source remote expert establishes the exact relation consumed by
`canonical_kv_cache_boundary_from_branch_inputs`.  The full expert weights are
reconstructed from `hInit`, and faithful execution uses the graph's actual
`replicaBuddies`; the expert output is not a caller premise. -/
theorem canonical_kv_cache_expert_from_branch_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hX : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8352)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13796)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13797)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hRP : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5568)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9647)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64])
    (hRM : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5569)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5573)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9656)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9657)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hdec := cKVCed_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8352)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13796)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13797)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5568)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9647)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5569)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5571 = allGatherPrimDimN 0 2 0 [initPM 9652, initPM 9653] :=
    cKVCed_weight_bridge initSM initPM hInit initGoal_5571 (by native_decide)
      5571 9652 9653 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5572 = allGatherPrimDimN 0 2 0 [initPM 9654, initPM 9655] :=
    cKVCed_weight_bridge initSM initPM hInit initGoal_5572 (by native_decide)
      5572 9654 9655 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5571).shape = [64, 1024, 1024] :=
    hSM 5571 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5572).shape = [64, 1024, 512] :=
    hSM 5572 [64, 1024, 512] (by native_decide)
  rw [cKVCed_red_sm5573 initSM, cKVCed_red_pm9656 initPM,
    cKVCed_red_pm9657 initPM]
  rw [cKVCed_leaf sm_goal_1 initSM 5571 (by native_decide) (by native_decide),
    cKVCed_leaf sm_goal_1 initSM 5572 (by native_decide) (by native_decide),
    cKVCed_leaf pm_goal_1 initPM 9652 (by native_decide) (by native_decide),
    cKVCed_leaf pm_goal_1 initPM 9653 (by native_decide) (by native_decide),
    cKVCed_leaf pm_goal_1 initPM 9654 (by native_decide) (by native_decide),
    cKVCed_leaf pm_goal_1 initPM 9655 (by native_decide) (by native_decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5571) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5572) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 9652, initPM 9653])
    (allGatherPrimDimN 0 2 0 [initPM 9654, initPM 9655])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

#print axioms canonical_kv_cache_expert_from_branch_inputs

end
end TrainVerify.Denote.GeneratedPatterns
