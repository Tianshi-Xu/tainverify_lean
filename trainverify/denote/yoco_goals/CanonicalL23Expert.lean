/- Canonical Goal 1, layer 23: faithful remote-expert MoE output. -/
import denote.yoco_goals.Goal_1
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

private theorem cL23e_reduce5
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

private theorem cL23e_reduce7
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

private def cL23eSmMoE : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [8952, 6220, 6221, 6223, 6224], outs := [6225],
    params := [64, 0, 64, 8] }
private def cL23ePmMoE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [15208, 11522, 11524, 11528, 11530], outs := [11532],
    params := [64, 0, 32, 8] }
private def cL23ePmMoE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [15209, 11523, 11525, 11529, 11531], outs := [11533],
    params := [64, 32, 64, 8] }

private theorem cL23e_buddies :
    sm_goal_1.replicaBuddies cL23eSmMoE = [cL23eSmMoE] ∧
    pm_goal_1.replicaBuddies cL23ePmMoE0 = [cL23ePmMoE0, cL23ePmMoE1] ∧
    pm_goal_1.replicaBuddies cL23ePmMoE1 = [cL23ePmMoE0, cL23ePmMoE1] := by
  native_decide

private theorem cL23e_red_sm6225 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6225 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm_goal_1 initSM 8952)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6220)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6221)
        [denoteGraphDistributedFaithful sm_goal_1 initSM 6223]
        [denoteGraphDistributedFaithful sm_goal_1 initSM 6224]
        64 8 (((10 : Nat) : Scalar)) := by
  refine cL23e_reduce5 sm_goal_1 initSM 912 cL23eSmMoE
    8952 6220 6221 6223 6224 6225
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2]
      64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  have hb := cL23e_buddies.1
  unfold cL23eSmMoE at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm_goal_1 s 0 8952 6220 6221 6223 6224 6225
    [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem cL23e_red_pm11532 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11532 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 15208)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11522)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11524)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11528,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11529]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11530,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11531]
        64 8 (((10 : Nat) : Scalar)) := by
  refine cL23e_reduce7 pm_goal_1 initPM 2003 cL23ePmMoE0
    15208 11522 11524 11528 11530 11529 11531 11532
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := cL23e_buddies.2.1
  unfold cL23ePmMoE0 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 0 15208 11522 11524 11528 11530
    11532 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem cL23e_red_pm11533 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11533 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 15209)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11523)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11525)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11528,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11529]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11530,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11531]
        64 8 (((10 : Nat) : Scalar)) := by
  refine cL23e_reduce7 pm_goal_1 initPM 2004 cL23ePmMoE1
    15209 11523 11525 11528 11529 11530 11531 11533
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := cL23e_buddies.2.2
  unfold cL23ePmMoE1 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 1 15209 11523 11525 11529 11531
    11533 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem cL23e_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem cL23e_weight_bridge (initSM initPM : Store)
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

private theorem cL23e_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hrel : Zigzag2Rel full z0 z1
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) =
      [0, 2 * 2048] := by
  have hleaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 :=
    cL23e_leaf pm_goal_1 initPM 6252 (by native_decide) (by native_decide)
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

/-- The real canonical L23 remote-expert node preserves the CP2 zigzag layout.
The three relation premises are its computed activation/routing branch inputs;
the expert output itself is derived using the faithful evaluator and the
`replicaBuddies`-declared full expert-weight gather. -/
theorem canonical_l23_expert_from_branch_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hX : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8952)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15209)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hRP : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6220)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11522)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11523)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64])
    (hRM : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6221)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11524)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11525)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6225)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11532)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11533)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hdec := cL23e_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8952)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15209)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6220)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11522)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11523)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6221)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11524)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11525)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  have hbW13 : initSM 6223 = allGatherPrimDimN 0 2 0 [initPM 11528, initPM 11529] :=
    cL23e_weight_bridge initSM initPM hInit initGoal_6223 (by native_decide)
      6223 11528 11529 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 6224 = allGatherPrimDimN 0 2 0 [initPM 11530, initPM 11531] :=
    cL23e_weight_bridge initSM initPM hInit initGoal_6224 (by native_decide)
      6224 11530 11531 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 6223).shape = [64, 1024, 1024] :=
    hSM 6223 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 6224).shape = [64, 1024, 512] :=
    hSM 6224 [64, 1024, 512] (by native_decide)
  rw [cL23e_red_sm6225 initSM, cL23e_red_pm11532 initPM,
    cL23e_red_pm11533 initPM]
  rw [cL23e_leaf sm_goal_1 initSM 6223 (by native_decide) (by native_decide),
    cL23e_leaf sm_goal_1 initSM 6224 (by native_decide) (by native_decide),
    cL23e_leaf pm_goal_1 initPM 11528 (by native_decide) (by native_decide),
    cL23e_leaf pm_goal_1 initPM 11529 (by native_decide) (by native_decide),
    cL23e_leaf pm_goal_1 initPM 11530 (by native_decide) (by native_decide),
    cL23e_leaf pm_goal_1 initPM 11531 (by native_decide) (by native_decide)]
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 6223) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 6224) (by rw [hw2shape]; decide)]
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 11528, initPM 11529])
    (allGatherPrimDimN 0 2 0 [initPM 11530, initPM 11531])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

end
end TrainVerify.Denote.GeneratedPatterns
