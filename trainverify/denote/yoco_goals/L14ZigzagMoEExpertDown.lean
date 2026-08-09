/- Canonical Goal 1, layer 14: faithful remote-expert MoE output. -/
import denote.yoco_goals.L14ZigzagMoERouter
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

private theorem l14ZMed_reduce5
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

private theorem l14ZMed_reduce7
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

private def l14ZMedSmMoE : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [8679, 5842, 5843, 5845, 5846], outs := [5847],
    params := [64, 0, 64, 8] }
private def l14ZMedPmMoE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [14396, 10444, 10446, 10450, 10452], outs := [10454],
    params := [64, 0, 32, 8] }
private def l14ZMedPmMoE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [14397, 10445, 10447, 10451, 10453], outs := [10455],
    params := [64, 32, 64, 8] }

private theorem l14ZMed_sm_buddies :
    sm_goal_1.replicaBuddies l14ZMedSmMoE = [l14ZMedSmMoE] := by
  native_decide

private theorem l14ZMed_pm0_buddies :
    pm_goal_1.replicaBuddies l14ZMedPmMoE0 = [l14ZMedPmMoE0, l14ZMedPmMoE1] := by
  native_decide

private theorem l14ZMed_pm1_buddies :
    pm_goal_1.replicaBuddies l14ZMedPmMoE1 = [l14ZMedPmMoE0, l14ZMedPmMoE1] := by
  native_decide

private theorem l14ZMed_red_sm5847 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5847 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm_goal_1 initSM 8679)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5842)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5843)
        [denoteGraphDistributedFaithful sm_goal_1 initSM 5845]
        [denoteGraphDistributedFaithful sm_goal_1 initSM 5846]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l14ZMed_reduce5 sm_goal_1 initSM 667 l14ZMedSmMoE
    8679 5842 5843 5845 5846 5847
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2]
      64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  have hb := l14ZMed_sm_buddies
  unfold l14ZMedSmMoE at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm_goal_1 s 0 8679 5842 5843 5845 5846 5847
    [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l14ZMed_red_pm10454 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10454 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 14396)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10444)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10446)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10450,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10451]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10452,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10453]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l14ZMed_reduce7 pm_goal_1 initPM 1471 l14ZMedPmMoE0
    14396 10444 10446 10450 10452 10451 10453 10454
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := l14ZMed_pm0_buddies
  unfold l14ZMedPmMoE0 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 0 14396 10444 10446 10450 10452
    10454 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l14ZMed_red_pm10455 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10455 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 14397)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10445)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 10447)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10450,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10451]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10452,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10453]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l14ZMed_reduce7 pm_goal_1 initPM 1472 l14ZMedPmMoE1
    14397 10445 10447 10450 10451 10452 10453 10455
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := l14ZMed_pm1_buddies
  unfold l14ZMedPmMoE1 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 1 14397 10445 10447 10451 10453
    10455 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l14ZMed_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l14ZMed_weight_bridge (initSM initPM : Store)
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

private theorem l14ZMed_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hrel : Zigzag2Rel full z0 z1
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) =
      [0, 2 * 2048] := by
  have hleaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 :=
    l14ZMed_leaf pm_goal_1 initPM 6252 (by native_decide) (by native_decide)
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

/-- The real canonical L14 remote-expert node preserves the CP2 zigzag layout.
The three relation premises are its computed activation/routing branch inputs;
the expert output itself is derived using the faithful evaluator and the
`replicaBuddies`-declared full expert-weight gather. -/
theorem l14_zigzag_moe_expert_from_branch_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hX : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8679)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14396)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hRP : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5842)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64])
    (hRM : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5843)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10446)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10447)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5847)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10455)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hdec := l14ZMed_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8679)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14396)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5842)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5843)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10446)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10447)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 5845 = allGatherPrimDimN 0 2 0 [initPM 10450, initPM 10451] :=
    l14ZMed_weight_bridge initSM initPM hInit initGoal_5845 (by native_decide)
      5845 10450 10451 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5846 = allGatherPrimDimN 0 2 0 [initPM 10452, initPM 10453] :=
    l14ZMed_weight_bridge initSM initPM hInit initGoal_5846 (by native_decide)
      5846 10452 10453 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5845).shape = [64, 1024, 1024] :=
    hSM 5845 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5846).shape = [64, 1024, 512] :=
    hSM 5846 [64, 1024, 512] (by native_decide)
  rw [l14ZMed_red_sm5847 initSM, l14ZMed_red_pm10454 initPM,
    l14ZMed_red_pm10455 initPM]
  rw [l14ZMed_leaf sm_goal_1 initSM 5845 (by native_decide) (by native_decide),
    l14ZMed_leaf sm_goal_1 initSM 5846 (by native_decide) (by native_decide),
    l14ZMed_leaf pm_goal_1 initPM 10450 (by native_decide) (by native_decide),
    l14ZMed_leaf pm_goal_1 initPM 10451 (by native_decide) (by native_decide),
    l14ZMed_leaf pm_goal_1 initPM 10452 (by native_decide) (by native_decide),
    l14ZMed_leaf pm_goal_1 initPM 10453 (by native_decide) (by native_decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5845) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5846) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 10450, initPM 10451])
    (allGatherPrimDimN 0 2 0 [initPM 10452, initPM 10453])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

/-- The canonical L14 remote-expert output from the exact L14 attention-residual boundary.
Activation and both routing relations are computed internally, so no graph
intermediate relation is part of the caller contract. -/
theorem l14_zigzag_moe_expert_from_attention_output (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5847)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10455)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hX := l14_zigzag_moe_activation_from_attention_output initSM initPM hInit hAttention
  have hRouter :=
    l14_zigzag_moe_router_from_attention_output initSM initPM hPM hInit hAttention
  exact l14_zigzag_moe_expert_from_branch_inputs initSM initPM hSM hPM hInit
    hX hRouter.1 hRouter.2

#print axioms l14_zigzag_moe_expert_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
