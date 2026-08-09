/- Canonical Goal 1 cache-source ordinary remote-expert boundary. -/
import denote.yoco_goals.L1OrdinaryMoERouterGate
import denote.MoEFullSplitCommute

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

private theorem l1OMOe_reduce5
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

private theorem l1OMOe_reduce7
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

private def l1OMOeSmMoE : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7832, 5018, 5019, 5021, 5022], outs := [5023],
    params := [64, 0, 64, 8] }
private def l1OMOePmMoE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [12536, 8006, 8008, 8012, 8014], outs := [8016],
    params := [64, 0, 32, 8] }
private def l1OMOePmMoE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [12537, 8007, 8009, 8013, 8015], outs := [8017],
    params := [64, 32, 64, 8] }

private theorem l1OMOe_buddies_sm :
    sm_goal_1.replicaBuddies l1OMOeSmMoE = [l1OMOeSmMoE] := by
  native_decide

private theorem l1OMOe_buddies_pm0 :
    pm_goal_1.replicaBuddies l1OMOePmMoE0 = [l1OMOePmMoE0, l1OMOePmMoE1] := by
  native_decide

private theorem l1OMOe_buddies_pm1 :
    pm_goal_1.replicaBuddies l1OMOePmMoE1 = [l1OMOePmMoE0, l1OMOePmMoE1] := by
  native_decide

private theorem l1OMOe_red_sm5023 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5023 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm_goal_1 initSM 7832)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5018)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5019)
        [denoteGraphDistributedFaithful sm_goal_1 initSM 5021]
        [denoteGraphDistributedFaithful sm_goal_1 initSM 5022]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l1OMOe_reduce5 sm_goal_1 initSM 70 l1OMOeSmMoE
    7832 5018 5019 5021 5022 5023
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2]
      64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  have hb := l1OMOe_buddies_sm
  unfold l1OMOeSmMoE at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm_goal_1 s 0 7832 5018 5019 5021 5022 5023
    [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l1OMOe_red_pm8016 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8016 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 12536)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8006)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8008)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 8012,
         denoteGraphDistributedFaithful pm_goal_1 initPM 8013]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 8014,
         denoteGraphDistributedFaithful pm_goal_1 initPM 8015]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l1OMOe_reduce7 pm_goal_1 initPM 187 l1OMOePmMoE0
    12536 8006 8008 8012 8014 8013 8015 8016
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := l1OMOe_buddies_pm0
  unfold l1OMOePmMoE0 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 0 12536 8006 8008 8012 8014 8016
    [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l1OMOe_red_pm8017 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8017 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm_goal_1 initPM 12537)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8007)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 8009)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 8012,
         denoteGraphDistributedFaithful pm_goal_1 initPM 8013]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 8014,
         denoteGraphDistributedFaithful pm_goal_1 initPM 8015]
        64 8 (((10 : Nat) : Scalar)) := by
  refine l1OMOe_reduce7 pm_goal_1 initPM 188 l1OMOePmMoE1
    12537 8007 8009 8012 8013 8014 8015 8017
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b]
        64 8 (((10 : Nat) : Scalar)))
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  have hb := l1OMOe_buddies_pm1
  unfold l1OMOePmMoE1 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm_goal_1 s 1 12537 8007 8009 8013 8015 8017
    [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

private theorem l1OMOe_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l1OMOe_weight_bridge (initSM initPM : Store)
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

/-- The real cache remote-expert node preserves ordinary dim-0 layout.  The
activation and both router outputs are computed branch facts; expert weights,
faithful node values, buddy topology, and output shapes are discharged here. -/
theorem l1_ordinary_moe_expert_from_branch_inputs (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hX : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 7832)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 12537)
      [4096, 1024] [2048, 1024])
    (hRP : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5018)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8006)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8007)
      [4096, 64] [2048, 64])
    (hRM : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5019)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8008)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8009)
      [4096, 64] [2048, 64]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5023)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8017)
      [4096, 1024] [2048, 1024] := by
  have hbW13 : initSM 5021 = allGatherPrimDimN 0 2 0 [initPM 8012, initPM 8013] :=
    l1OMOe_weight_bridge initSM initPM hInit initGoal_5021 (by native_decide)
      5021 8012 8013 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5022 = allGatherPrimDimN 0 2 0 [initPM 8014, initPM 8015] :=
    l1OMOe_weight_bridge initSM initPM hInit initGoal_5022 (by native_decide)
      5022 8014 8015 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hW13 : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5021)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8013)
      [64, 1024, 1024] [32, 1024, 1024] := by
    rw [l1OMOe_leaf sm_goal_1 initSM 5021 (by native_decide) (by native_decide),
      l1OMOe_leaf pm_goal_1 initPM 8012 (by native_decide) (by native_decide),
      l1OMOe_leaf pm_goal_1 initPM 8013 (by native_decide) (by native_decide)]
    exact ⟨hbW13, hSM 5021 _ (by native_decide), hPM 8012 _ (by native_decide),
      hPM 8013 _ (by native_decide), by decide⟩
  have hW2 : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5022)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8014)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8015)
      [64, 1024, 512] [32, 1024, 512] := by
    rw [l1OMOe_leaf sm_goal_1 initSM 5022 (by native_decide) (by native_decide),
      l1OMOe_leaf pm_goal_1 initPM 8014 (by native_decide) (by native_decide),
      l1OMOe_leaf pm_goal_1 initPM 8015 (by native_decide) (by native_decide)]
    exact ⟨hbW2, hSM 5022 _ (by native_decide), hPM 8014 _ (by native_decide),
      hPM 8015 _ (by native_decide), by decide⟩
  have hfullNode : denoteGraphDistributedFaithful sm_goal_1 initSM 5023 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm_goal_1 initSM 7832)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5018)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5019)
        [denoteGraphDistributedFaithful pm_goal_1 initPM 8012,
         denoteGraphDistributedFaithful pm_goal_1 initPM 8013]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 8014,
         denoteGraphDistributedFaithful pm_goal_1 initPM 8015]
        64 8 (((10 : Nat) : Scalar)) := by
    rw [l1OMOe_red_sm5023 initSM]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [allGatherPrimDimN_singleton_eq 0 _ (by rw [hW13.full_shape]; decide),
      allGatherPrimDimN_singleton_eq 0 _ (by rw [hW2.full_shape]; decide),
      hW13.value, hW2.value]
  have houtShape : (denoteGraphDistributedFaithful sm_goal_1 initSM 5023).shape =
      [4096, 1024] := by
    rw [l1OMOe_red_sm5023 initSM]
    exact fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 4096 1024
      (by rw [hX.full_shape]; rfl) (by rw [hX.full_shape]; rfl)
  have hout0Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 8016).shape =
      [2048, 1024] := by
    rw [l1OMOe_red_pm8016 initPM]
    exact fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hX.shard0_shape]; rfl) (by rw [hX.shard0_shape]; rfl)
  have hout1Shape : (denoteGraphDistributedFaithful pm_goal_1 initPM 8017).shape =
      [2048, 1024] := by
    rw [l1OMOe_red_pm8017 initPM]
    exact fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hX.shard1_shape]; rfl) (by rw [hX.shard1_shape]; rfl)
  exact gather2Rel_fullExpertMoE_boundary
    (input := denoteGraphDistributedFaithful sm_goal_1 initSM 7832)
    (input0 := denoteGraphDistributedFaithful pm_goal_1 initPM 12536)
    (input1 := denoteGraphDistributedFaithful pm_goal_1 initPM 12537)
    (rp := denoteGraphDistributedFaithful sm_goal_1 initSM 5018)
    (rp0 := denoteGraphDistributedFaithful pm_goal_1 initPM 8006)
    (rp1 := denoteGraphDistributedFaithful pm_goal_1 initPM 8007)
    (rm := denoteGraphDistributedFaithful sm_goal_1 initSM 5019)
    (rm0 := denoteGraphDistributedFaithful pm_goal_1 initPM 8008)
    (rm1 := denoteGraphDistributedFaithful pm_goal_1 initPM 8009)
    (w130 := denoteGraphDistributedFaithful pm_goal_1 initPM 8012)
    (w131 := denoteGraphDistributedFaithful pm_goal_1 initPM 8013)
    (w20 := denoteGraphDistributedFaithful pm_goal_1 initPM 8014)
    (w21 := denoteGraphDistributedFaithful pm_goal_1 initPM 8015)
    (out := denoteGraphDistributedFaithful sm_goal_1 initSM 5023)
    (out0 := denoteGraphDistributedFaithful pm_goal_1 initPM 8016)
    (out1 := denoteGraphDistributedFaithful pm_goal_1 initPM 8017)
    (L := 2048) (hM := 1024) (E := 32) (topK := 8)
    (tDim := 1024) (dDim := 512) (swigluLimit := (((10 : Nat) : Scalar)))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    hX hRP hRM (hPM 8012 _ (by native_decide)) (hPM 8013 _ (by native_decide))
    (hPM 8014 _ (by native_decide)) (hPM 8015 _ (by native_decide)) hfullNode
    (l1OMOe_red_pm8016 initPM) (l1OMOe_red_pm8017 initPM)
    houtShape hout0Shape hout1Shape

/-- A single attention-output boundary closes activation, router probabilities,
router map, and the true remote-expert output internally. -/
theorem l1_ordinary_moe_expert_from_attention_output (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7993)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5023)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8017)
      [4096, 1024] [2048, 1024] := by
  have hX := l1_ordinary_moe_activation_from_attention_output
    initSM initPM hInit hAttention
  have hRouter := l1_ordinary_moe_router_from_attention_output
    initSM initPM hPM hInit hAttention
  exact l1_ordinary_moe_expert_from_branch_inputs
    initSM initPM hSM hPM hInit hX hRouter.1 hRouter.2

#print axioms l1_ordinary_moe_expert_from_branch_inputs
#print axioms l1_ordinary_moe_expert_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
