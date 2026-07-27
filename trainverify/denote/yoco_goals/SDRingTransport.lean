/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRingBridge
import denote.yoco_goals.IntermediateReconstruction
import denote.yoco_goals.MoEShardedReconstruction
import denote.yoco_goals.ResidualMoEReconstruction

/-!
# Pre-MoE `_ringAttn` goals on the faithful track

Goals whose final writer precedes the first `FW_all2all_moe_gmm` node
(SM 31 / PM 104), where the ring and distributed evaluators still agree. Past
that point they differ on MoE semantics — the ring reading is the per-rank one,
which is not the production interpretation — so nothing after it is transported.

Two candidates (`7404`, `7408`) were dropped: their `_ringAttn` proofs take
`hWF : WellFormed_YOCOMoE_A04B`, the routing-disjointness contract, and importing
it here would make the faithful track depend on an assumption it does not need.
Both are `FW_multiref` outputs and are instead reduced from their faithful
parents elsewhere.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4696 : ∀ n ∈ sm.nodes.drop 10, (4696 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4696 : ∀ n ∈ sm.nodes.take 10, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7437 : ∀ n ∈ pm.nodes.drop 50, (7437 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7437 : ∀ n ∈ pm.nodes.take 50, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7438 : ∀ n ∈ pm.nodes.drop 51, (7438 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7438 : ∀ n ∈ pm.nodes.take 51, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4696_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4696
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4696 10 (by decide) rgn_sm_4696 rgw_sm_4696
  have hp0 := sd_pm_faithful_eq_ring initPM 7437 50 (by decide) rgn_pm_7437 rgw_pm_7437
  have hp1 := sd_pm_faithful_eq_ring initPM 7438 51 (by decide) rgn_pm_7438 rgw_pm_7438
  have hd := recon_intermediateGoal_4696_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4696, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4697 : ∀ n ∈ sm.nodes.drop 11, (4697 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4697 : ∀ n ∈ sm.nodes.take 11, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7439 : ∀ n ∈ pm.nodes.drop 52, (7439 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7439 : ∀ n ∈ pm.nodes.take 52, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7440 : ∀ n ∈ pm.nodes.drop 53, (7440 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7440 : ∀ n ∈ pm.nodes.take 53, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4697_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4697
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4697 11 (by decide) rgn_sm_4697 rgw_sm_4697
  have hp0 := sd_pm_faithful_eq_ring initPM 7439 52 (by decide) rgn_pm_7439 rgw_pm_7439
  have hp1 := sd_pm_faithful_eq_ring initPM 7440 53 (by decide) rgn_pm_7440 rgw_pm_7440
  have hd := recon_intermediateGoal_4697_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4697, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4698 : ∀ n ∈ sm.nodes.drop 12, (4698 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4698 : ∀ n ∈ sm.nodes.take 12, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4698 : ∀ n ∈ pm.nodes.drop 56, (4698 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4698 : ∀ n ∈ pm.nodes.take 56, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4698_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4698
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4698 12 (by decide) rgn_sm_4698 rgw_sm_4698
  have hp0 := sd_pm_faithful_eq_ring initPM 4698 56 (by decide) rgn_pm_4698 rgw_pm_4698
  have hd := recon_intermediateGoal_4698_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4698, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4700 : ∀ n ∈ sm.nodes.drop 13, (4700 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4700 : ∀ n ∈ sm.nodes.take 13, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4700 : ∀ n ∈ pm.nodes.drop 58, (4700 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4700 : ∀ n ∈ pm.nodes.take 58, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4700_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4700
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4700 13 (by decide) rgn_sm_4700 rgw_sm_4700
  have hp0 := sd_pm_faithful_eq_ring initPM 4700 58 (by decide) rgn_pm_4700 rgw_pm_4700
  have hd := recon_intermediateGoal_4700_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4700, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4701 : ∀ n ∈ sm.nodes.drop 14, (4701 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4701 : ∀ n ∈ sm.nodes.take 14, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4701 : ∀ n ∈ pm.nodes.drop 60, (4701 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4701 : ∀ n ∈ pm.nodes.take 60, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4701_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4701
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4701 14 (by decide) rgn_sm_4701 rgw_sm_4701
  have hp0 := sd_pm_faithful_eq_ring initPM 4701 60 (by decide) rgn_pm_4701 rgw_pm_4701
  have hd := recon_intermediateGoal_4701_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4701, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4702 : ∀ n ∈ sm.nodes.drop 15, (4702 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4702 : ∀ n ∈ sm.nodes.take 15, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4702 : ∀ n ∈ pm.nodes.drop 62, (4702 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4702 : ∀ n ∈ pm.nodes.take 62, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4702_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4702
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4702 15 (by decide) rgn_sm_4702 rgw_sm_4702
  have hp0 := sd_pm_faithful_eq_ring initPM 4702 62 (by decide) rgn_pm_4702 rgw_pm_4702
  have hd := recon_intermediateGoal_4702_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4702, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4703 : ∀ n ∈ sm.nodes.drop 16, (4703 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4703 : ∀ n ∈ sm.nodes.take 16, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4703 : ∀ n ∈ pm.nodes.drop 64, (4703 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4703 : ∀ n ∈ pm.nodes.take 64, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4703_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4703
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4703 16 (by decide) rgn_sm_4703 rgw_sm_4703
  have hp0 := sd_pm_faithful_eq_ring initPM 4703 64 (by decide) rgn_pm_4703 rgw_pm_4703
  have hd := recon_intermediateGoal_4703_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4703, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4705 : ∀ n ∈ sm.nodes.drop 18, (4705 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4705 : ∀ n ∈ sm.nodes.take 18, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4705 : ∀ n ∈ pm.nodes.drop 68, (4705 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4705 : ∀ n ∈ pm.nodes.take 68, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4705_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4705
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4705 18 (by decide) rgn_sm_4705 rgw_sm_4705
  have hp0 := sd_pm_faithful_eq_ring initPM 4705 68 (by decide) rgn_pm_4705 rgw_pm_4705
  have hd := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4705, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4706 : ∀ n ∈ sm.nodes.drop 20, (4706 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4706 : ∀ n ∈ sm.nodes.take 20, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4706 : ∀ n ∈ pm.nodes.drop 76, (4706 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4706 : ∀ n ∈ pm.nodes.take 76, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4706_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4706
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4706 20 (by decide) rgn_sm_4706 rgw_sm_4706
  have hp0 := sd_pm_faithful_eq_ring initPM 4706 76 (by decide) rgn_pm_4706 rgw_pm_4706
  have hd := recon_intermediateGoal_4706_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4706, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4708 : ∀ n ∈ sm.nodes.drop 24, (4708 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4708 : ∀ n ∈ sm.nodes.take 24, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4708 : ∀ n ∈ pm.nodes.drop 82, (4708 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4708 : ∀ n ∈ pm.nodes.take 82, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4708_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4708
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4708 24 (by decide) rgn_sm_4708 rgw_sm_4708
  have hp0 := sd_pm_faithful_eq_ring initPM 4708 82 (by decide) rgn_pm_4708 rgw_pm_4708
  have hd := recon_intermediateGoal_4708_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4708, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4709 : ∀ n ∈ sm.nodes.drop 28, (4709 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4709 : ∀ n ∈ sm.nodes.take 28, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7481 : ∀ n ∈ pm.nodes.drop 97, (7481 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7481 : ∀ n ∈ pm.nodes.take 97, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7482 : ∀ n ∈ pm.nodes.drop 98, (7482 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7482 : ∀ n ∈ pm.nodes.take 98, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4709_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4709
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4709 28 (by decide) rgn_sm_4709 rgw_sm_4709
  have hp0 := sd_pm_faithful_eq_ring initPM 7481 97 (by decide) rgn_pm_7481 rgw_pm_7481
  have hp1 := sd_pm_faithful_eq_ring initPM 7482 98 (by decide) rgn_pm_7482 rgw_pm_7482
  have hd := recon_intermediateGoal_4709_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4709, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4710 : ∀ n ∈ sm.nodes.drop 28, (4710 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4710 : ∀ n ∈ sm.nodes.take 28, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7483 : ∀ n ∈ pm.nodes.drop 97, (7483 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7483 : ∀ n ∈ pm.nodes.take 97, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_7484 : ∀ n ∈ pm.nodes.drop 98, (7484 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_7484 : ∀ n ∈ pm.nodes.take 98, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4710_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4710
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4710 28 (by decide) rgn_sm_4710 rgw_sm_4710
  have hp0 := sd_pm_faithful_eq_ring initPM 7483 97 (by decide) rgn_pm_7483 rgw_pm_7483
  have hp1 := sd_pm_faithful_eq_ring initPM 7484 98 (by decide) rgn_pm_7484 rgw_pm_7484
  have hd := recon_intermediateGoal_4710_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4710, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4715 : ∀ n ∈ sm.nodes.drop 21, (4715 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4715 : ∀ n ∈ sm.nodes.take 21, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4715 : ∀ n ∈ pm.nodes.drop 78, (4715 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4715 : ∀ n ∈ pm.nodes.take 78, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4715_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4715
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4715 21 (by decide) rgn_sm_4715 rgw_sm_4715
  have hp0 := sd_pm_faithful_eq_ring initPM 4715 78 (by decide) rgn_pm_4715 rgw_pm_4715
  have hd := recon_intermediateGoal_4715_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4715, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4717 : ∀ n ∈ sm.nodes.drop 25, (4717 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4717 : ∀ n ∈ sm.nodes.take 25, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4717 : ∀ n ∈ pm.nodes.drop 84, (4717 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4717 : ∀ n ∈ pm.nodes.take 84, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4717_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4717
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4717 25 (by decide) rgn_sm_4717 rgw_sm_4717
  have hp0 := sd_pm_faithful_eq_ring initPM 4717 84 (by decide) rgn_pm_4717 rgw_pm_4717
  have hd := recon_intermediateGoal_4717_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4717, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4718 : ∀ n ∈ sm.nodes.drop 29, (4718 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4718 : ∀ n ∈ sm.nodes.take 29, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4718 : ∀ n ∈ pm.nodes.drop 92, (4718 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4718 : ∀ n ∈ pm.nodes.take 92, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4718_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4718
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4718 29 (by decide) rgn_sm_4718 rgw_sm_4718
  have hp0 := sd_pm_faithful_eq_ring initPM 4718 92 (by decide) rgn_pm_4718 rgw_pm_4718
  have hd := recon_intermediateGoal_4718_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4718, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4720 : ∀ n ∈ sm.nodes.drop 22, (4720 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4720 : ∀ n ∈ sm.nodes.take 22, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4720 : ∀ n ∈ pm.nodes.drop 79, (4720 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4720 : ∀ n ∈ pm.nodes.take 79, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4720_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4720
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4720 22 (by decide) rgn_sm_4720 rgw_sm_4720
  have hp0 := sd_pm_faithful_eq_ring initPM 4720 79 (by decide) rgn_pm_4720 rgw_pm_4720
  have hd := recon_intermediateGoal_4720_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4720, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4722 : ∀ n ∈ sm.nodes.drop 26, (4722 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4722 : ∀ n ∈ sm.nodes.take 26, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4722 : ∀ n ∈ pm.nodes.drop 86, (4722 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4722 : ∀ n ∈ pm.nodes.take 86, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4722_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4722
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4722 26 (by decide) rgn_sm_4722 rgw_sm_4722
  have hp0 := sd_pm_faithful_eq_ring initPM 4722 86 (by decide) rgn_pm_4722 rgw_pm_4722
  have hd := recon_intermediateGoal_4722_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4722, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4723 : ∀ n ∈ sm.nodes.drop 30, (4723 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4723 : ∀ n ∈ sm.nodes.take 30, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4723 : ∀ n ∈ pm.nodes.drop 94, (4723 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4723 : ∀ n ∈ pm.nodes.take 94, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4723_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4723
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4723 30 (by decide) rgn_sm_4723 rgw_sm_4723
  have hp0 := sd_pm_faithful_eq_ring initPM 4723 94 (by decide) rgn_pm_4723 rgw_pm_4723
  have hd := recon_intermediateGoal_4723_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4723, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4724 : ∀ n ∈ sm.nodes.drop 23, (4724 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4724 : ∀ n ∈ sm.nodes.take 23, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4724 : ∀ n ∈ pm.nodes.drop 80, (4724 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4724 : ∀ n ∈ pm.nodes.take 80, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4724_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4724
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4724 23 (by decide) rgn_sm_4724 rgw_sm_4724
  have hp0 := sd_pm_faithful_eq_ring initPM 4724 80 (by decide) rgn_pm_4724 rgw_pm_4724
  have hd := recon_intermediateGoal_4724_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4724, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4726 : ∀ n ∈ sm.nodes.drop 27, (4726 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4726 : ∀ n ∈ sm.nodes.take 27, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4726 : ∀ n ∈ pm.nodes.drop 88, (4726 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4726 : ∀ n ∈ pm.nodes.take 88, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4726_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4726
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4726 27 (by decide) rgn_sm_4726 rgw_sm_4726
  have hp0 := sd_pm_faithful_eq_ring initPM 4726 88 (by decide) rgn_pm_4726 rgw_pm_4726
  have hd := recon_intermediateGoal_4726_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4726, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_4727 : ∀ n ∈ sm.nodes.drop 31, (4727 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_4727 : ∀ n ∈ sm.nodes.take 31, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_4727 : ∀ n ∈ pm.nodes.drop 96, (4727 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_4727 : ∀ n ∈ pm.nodes.take 96, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4727_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4727
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 4727 31 (by decide) rgn_sm_4727 rgw_sm_4727
  have hp0 := sd_pm_faithful_eq_ring initPM 4727 96 (by decide) rgn_pm_4727 rgw_pm_4727
  have hd := recon_intermediateGoal_4727_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4727, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem rgw_sm_7419 : ∀ n ∈ sm.nodes.drop 19, (7419 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_sm_7419 : ∀ n ∈ sm.nodes.take 19, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_11941 : ∀ n ∈ pm.nodes.drop 72, (11941 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_11941 : ∀ n ∈ pm.nodes.take 72, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgw_pm_11942 : ∀ n ∈ pm.nodes.drop 77, (11942 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rgn_pm_11942 : ∀ n ∈ pm.nodes.take 77, n.op ≠ "OpName.FW_all2all_moe_gmm" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7419_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7419
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq_ring initSM 7419 19 (by decide) rgn_sm_7419 rgw_sm_7419
  have hp0 := sd_pm_faithful_eq_ring initPM 11941 72 (by decide) rgn_pm_11941 rgw_pm_11941
  have hp1 := sd_pm_faithful_eq_ring initPM 11942 77 (by decide) rgn_pm_11942 rgw_pm_11942
  have hd := recon_intermediateGoal_7419_ringAttn initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_7419, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

end

end TrainVerify.Denote.GeneratedPatterns
