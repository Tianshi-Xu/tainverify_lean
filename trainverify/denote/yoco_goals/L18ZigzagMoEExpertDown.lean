/- Canonical Goal 1, layer 18: faithful remote-expert MoE output. -/
import denote.yoco_goals.L18ZigzagMoERouter
import denote.yoco_goals.ZigzagMoEGmmRel

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

private theorem l18ZMed_reduce5
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

private theorem l18ZMed_reduce7
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

private def l18ZMedSmMoE : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [8835, 6058, 6059, 6061, 6062], outs := [6063],
    params := [64, 0, 64, 8] }
private def l18ZMedPmMoE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [14860, 11060, 11062, 11066, 11068], outs := [11070],
    params := [64, 0, 32, 8] }
private def l18ZMedPmMoE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [14861, 11061, 11063, 11067, 11069], outs := [11071],
    params := [64, 32, 64, 8] }

private theorem l18ZMed_sm_buddies :
    sm_goal_1.replicaBuddies l18ZMedSmMoE = [l18ZMedSmMoE] := by
  native_decide

private theorem l18ZMed_pm0_buddies :
    pm_goal_1.replicaBuddies l18ZMedPmMoE0 = [l18ZMedPmMoE0, l18ZMedPmMoE1] := by
  native_decide

private theorem l18ZMed_pm1_buddies :
    pm_goal_1.replicaBuddies l18ZMedPmMoE1 = [l18ZMedPmMoE0, l18ZMedPmMoE1] := by
  native_decide

private theorem l18ZMed_red_sm6063 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6063 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm_goal_1 initSM 8835)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6058)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6059)
        [denoteGraphDistributedFaithful sm_goal_1 initSM 6061]
        [denoteGraphDistributedFaithful sm_goal_1 initSM 6062]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l18ZMed_reduce5 sm_goal_1 initSM 807 l18ZMedSmMoE
    8835 6058 6059 6061 6062 6063
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2]
      64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  have hb := l18ZMed_sm_buddies
  unfold l18ZMedSmMoE at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm_goal_1 s 0 8835 6058 6059 6061 6062 6063
    [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l18ZMed_red_pm11070 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11070 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 14860)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11060)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11062)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11066,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11067]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11068,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11069]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l18ZMed_reduce7 pm_goal_1 initPM 1775 l18ZMedPmMoE0
    14860 11060 11062 11066 11068 11067 11069 11070
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := l18ZMed_pm0_buddies
  unfold l18ZMedPmMoE0 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 0 14860 11060 11062 11066 11068
    11070 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l18ZMed_red_pm11071 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11071 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 14861)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11061)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11063)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11066,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11067]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11068,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11069]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l18ZMed_reduce7 pm_goal_1 initPM 1776 l18ZMedPmMoE1
    14861 11061 11063 11066 11067 11068 11069 11071
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := l18ZMed_pm1_buddies
  unfold l18ZMedPmMoE1 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 1 14861 11061 11063 11067 11069
    11071 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l18ZMed_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l18ZMed_weight_bridge (initSM initPM : Store)
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

private theorem l18ZMed_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hrel : Zigzag2Rel full z0 z1
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) =
      [0, 2 * 2048] := by
  have hleaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 :=
    l18ZMed_leaf pm_goal_1 initPM 6252 (by native_decide) (by native_decide)
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

/-- The real canonical L18 remote-expert node preserves the CP2 zigzag layout.
The three relation premises are its computed activation/routing branch inputs;
the expert output itself is derived using the faithful evaluator and the
`replicaBuddies`-declared full expert-weight gather. -/
theorem l18_zigzag_moe_expert_from_branch_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hX : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8835)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14860)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14861)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hRP : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11061)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64])
    (hRM : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11063)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6063)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11070)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11071)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hdec := l18ZMed_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8835)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14860)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14861)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11061)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11063)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 6061 = allGatherPrimDimN 0 2 0 [initPM 11066, initPM 11067] :=
    l18ZMed_weight_bridge initSM initPM hInit initGoal_6061 (by native_decide)
      6061 11066 11067 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 6062 = allGatherPrimDimN 0 2 0 [initPM 11068, initPM 11069] :=
    l18ZMed_weight_bridge initSM initPM hInit initGoal_6062 (by native_decide)
      6062 11068 11069 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 6061).shape = [64, 1024, 1024] :=
    hSM 6061 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 6062).shape = [64, 1024, 512] :=
    hSM 6062 [64, 1024, 512] (by native_decide)
  rw [l18ZMed_red_sm6063 initSM, l18ZMed_red_pm11070 initPM,
    l18ZMed_red_pm11071 initPM]
  rw [l18ZMed_leaf sm_goal_1 initSM 6061 (by native_decide) (by native_decide),
    l18ZMed_leaf sm_goal_1 initSM 6062 (by native_decide) (by native_decide),
    l18ZMed_leaf pm_goal_1 initPM 11066 (by native_decide) (by native_decide),
    l18ZMed_leaf pm_goal_1 initPM 11067 (by native_decide) (by native_decide),
    l18ZMed_leaf pm_goal_1 initPM 11068 (by native_decide) (by native_decide),
    l18ZMed_leaf pm_goal_1 initPM 11069 (by native_decide) (by native_decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 6061) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 6062) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 11066, initPM 11067])
    (allGatherPrimDimN 0 2 0 [initPM 11068, initPM 11069])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

/-- The canonical L18 remote-expert output from the exact L18 attention-residual boundary.
Activation and both routing relations are computed internally, so no graph
intermediate relation is part of the caller contract. -/
theorem l18_zigzag_moe_expert_from_attention_output (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6063)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11070)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11071)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hX := l18_zigzag_moe_activation_from_attention_output initSM initPM hInit hAttention
  have hRouter :=
    l18_zigzag_moe_router_from_attention_output initSM initPM hPM hInit hAttention
  exact l18_zigzag_moe_expert_from_branch_inputs initSM initPM hSM hPM hInit
    hX hRouter.1 hRouter.2

#print axioms l18_zigzag_moe_expert_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
