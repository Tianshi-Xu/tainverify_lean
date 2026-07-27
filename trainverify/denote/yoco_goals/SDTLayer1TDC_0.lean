/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer1TokenDependencyCone

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer1TokenDependencyCone.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4751 : ∀ n ∈ sm.nodes.drop 50, (4751 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7625 : ∀ n ∈ pm.nodes.drop 147, (7625 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7626 : ∀ n ∈ pm.nodes.drop 148, (7626 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4751_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4751
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4751 50 (by decide) sdw_sm_4751
  have hp0 := sd_pm_faithful_eq initPM 7625 147 (by decide) sdw_pm_7625
  have hp1 := sd_pm_faithful_eq initPM 7626 148 (by decide) sdw_pm_7626
  have hd := recon_intermediateGoal_4751_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4751, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4752 : ∀ n ∈ sm.nodes.drop 51, (4752 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4752 : ∀ n ∈ pm.nodes.drop 151, (4752 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4752_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4752
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4752 51 (by decide) sdw_sm_4752
  have hp0 := sd_pm_faithful_eq initPM 4752 151 (by decide) sdw_pm_4752
  have hd := recon_intermediateGoal_4752_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4752, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4754 : ∀ n ∈ sm.nodes.drop 52, (4754 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4754 : ∀ n ∈ pm.nodes.drop 153, (4754 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4754_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4754
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4754 52 (by decide) sdw_sm_4754
  have hp0 := sd_pm_faithful_eq initPM 4754 153 (by decide) sdw_pm_4754
  have hd := recon_intermediateGoal_4754_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4754, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4755 : ∀ n ∈ sm.nodes.drop 53, (4755 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4755 : ∀ n ∈ pm.nodes.drop 155, (4755 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4755_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4755
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4755 53 (by decide) sdw_sm_4755
  have hp0 := sd_pm_faithful_eq initPM 4755 155 (by decide) sdw_pm_4755
  have hd := recon_intermediateGoal_4755_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4755, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4756 : ∀ n ∈ sm.nodes.drop 54, (4756 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4756 : ∀ n ∈ pm.nodes.drop 157, (4756 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4756_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4756
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4756 54 (by decide) sdw_sm_4756
  have hp0 := sd_pm_faithful_eq initPM 4756 157 (by decide) sdw_pm_4756
  have hd := recon_intermediateGoal_4756_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4756, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4757 : ∀ n ∈ sm.nodes.drop 55, (4757 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4757 : ∀ n ∈ pm.nodes.drop 159, (4757 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4757_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4757
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4757 55 (by decide) sdw_sm_4757
  have hp0 := sd_pm_faithful_eq initPM 4757 159 (by decide) sdw_pm_4757
  have hd := recon_intermediateGoal_4757_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4757, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4759 : ∀ n ∈ sm.nodes.drop 57, (4759 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4759 : ∀ n ∈ pm.nodes.drop 164, (4759 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4759_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4759
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4759 57 (by decide) sdw_sm_4759
  have hp0 := sd_pm_faithful_eq initPM 4759 164 (by decide) sdw_pm_4759
  have hd := recon_intermediateGoal_4759_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4759, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4760 : ∀ n ∈ sm.nodes.drop 59, (4760 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4760 : ∀ n ∈ pm.nodes.drop 173, (4760 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4760_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4760
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4760 59 (by decide) sdw_sm_4760
  have hp0 := sd_pm_faithful_eq initPM 4760 173 (by decide) sdw_pm_4760
  have hd := recon_intermediateGoal_4760_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4760, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4762 : ∀ n ∈ sm.nodes.drop 63, (4762 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4762 : ∀ n ∈ pm.nodes.drop 179, (4762 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4762_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4762
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4762 63 (by decide) sdw_sm_4762
  have hp0 := sd_pm_faithful_eq initPM 4762 179 (by decide) sdw_pm_4762
  have hd := recon_intermediateGoal_4762_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4762, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4763 : ∀ n ∈ sm.nodes.drop 67, (4763 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7667 : ∀ n ∈ pm.nodes.drop 194, (7667 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7668 : ∀ n ∈ pm.nodes.drop 195, (7668 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4763_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4763
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4763 67 (by decide) sdw_sm_4763
  have hp0 := sd_pm_faithful_eq initPM 7667 194 (by decide) sdw_pm_7667
  have hp1 := sd_pm_faithful_eq initPM 7668 195 (by decide) sdw_pm_7668
  have hd := recon_intermediateGoal_4763_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4763, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4764 : ∀ n ∈ sm.nodes.drop 67, (4764 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7669 : ∀ n ∈ pm.nodes.drop 194, (7669 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7670 : ∀ n ∈ pm.nodes.drop 195, (7670 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4764_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4764
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4764 67 (by decide) sdw_sm_4764
  have hp0 := sd_pm_faithful_eq initPM 7669 194 (by decide) sdw_pm_7669
  have hp1 := sd_pm_faithful_eq initPM 7670 195 (by decide) sdw_pm_7670
  have hd := recon_intermediateGoal_4764_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4764, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4768 : ∀ n ∈ sm.nodes.drop 71, (4768 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7677 : ∀ n ∈ pm.nodes.drop 202, (7677 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7678 : ∀ n ∈ pm.nodes.drop 203, (7678 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4768_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4768
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4768 71 (by decide) sdw_sm_4768
  have hp0 := sd_pm_faithful_eq initPM 7677 202 (by decide) sdw_pm_7677
  have hp1 := sd_pm_faithful_eq initPM 7678 203 (by decide) sdw_pm_7678
  have hd := recon_intermediateGoal_4768_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_4768, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7471 : ∀ n ∈ sm.nodes.drop 58, (7471 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_11977 : ∀ n ∈ pm.nodes.drop 169, (11977 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_11978 : ∀ n ∈ pm.nodes.drop 174, (11978 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7471_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7471
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7471 58 (by decide) sdw_sm_7471
  have hp0 := sd_pm_faithful_eq initPM 11977 169 (by decide) sdw_pm_11977
  have hp1 := sd_pm_faithful_eq initPM 11978 174 (by decide) sdw_pm_11978
  have hd := recon_intermediateGoal_7471_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_7471, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

end

end TrainVerify.Denote.GeneratedPatterns
