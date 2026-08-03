/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer1DistributedMigration

/-!
# Self-decoder goals transported to the faithful track (pilot batch)

Each theorem here is the existing `_distributed` result read through
`sd_sm_faithful_eq` / `sd_pm_faithful_eq`. The only per-goal obligation is that
nothing writes the tid after its final writer, decided by `native_decide`; the
collective-freeness of the prefix is handled once, region-wide, in
`SDRegionBridge`.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4734 : ∀ n ∈ sm.nodes.drop 39, (4734 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4734 : ∀ n ∈ pm.nodes.drop 120, (4734 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4734_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4734
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4734 39 (by decide) sdw_sm_4734
  have hp0 := sd_pm_faithful_eq initPM 4734 120 (by decide) sdw_pm_4734
  have hd := recon_intermediateGoal_4734_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4734
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4735 : ∀ n ∈ sm.nodes.drop 40, (4735 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4735 : ∀ n ∈ pm.nodes.drop 122, (4735 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4735_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4735
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4735 40 (by decide) sdw_sm_4735
  have hp0 := sd_pm_faithful_eq initPM 4735 122 (by decide) sdw_pm_4735
  have hd := recon_intermediateGoal_4735_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4735
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4736 : ∀ n ∈ sm.nodes.drop 41, (4736 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4736 : ∀ n ∈ pm.nodes.drop 124, (4736 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4736_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4736
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4736 41 (by decide) sdw_sm_4736
  have hp0 := sd_pm_faithful_eq initPM 4736 124 (by decide) sdw_pm_4736
  have hd := recon_intermediateGoal_4736_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4736
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4738 : ∀ n ∈ sm.nodes.drop 43, (4738 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4738 : ∀ n ∈ pm.nodes.drop 128, (4738 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4738_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4738
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4738 43 (by decide) sdw_sm_4738
  have hp0 := sd_pm_faithful_eq initPM 4738 128 (by decide) sdw_pm_4738
  have hd := recon_intermediateGoal_4738_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4738
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4740 : ∀ n ∈ sm.nodes.drop 45, (4740 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4740 : ∀ n ∈ pm.nodes.drop 134, (4740 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4740_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4740
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4740 45 (by decide) sdw_sm_4740
  have hp0 := sd_pm_faithful_eq initPM 4740 134 (by decide) sdw_pm_4740
  have hd := recon_intermediateGoal_4740_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4740
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4742 : ∀ n ∈ sm.nodes.drop 46, (4742 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4742 : ∀ n ∈ pm.nodes.drop 135, (4742 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4742_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4742
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4742 46 (by decide) sdw_sm_4742
  have hp0 := sd_pm_faithful_eq initPM 4742 135 (by decide) sdw_pm_4742
  have hd := recon_intermediateGoal_4742_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4742
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4744 : ∀ n ∈ sm.nodes.drop 47, (4744 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4744 : ∀ n ∈ pm.nodes.drop 136, (4744 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4744_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4744
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4744 47 (by decide) sdw_sm_4744
  have hp0 := sd_pm_faithful_eq initPM 4744 136 (by decide) sdw_pm_4744
  have hd := recon_intermediateGoal_4744_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4744
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4746 : ∀ n ∈ sm.nodes.drop 48, (4746 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4746 : ∀ n ∈ pm.nodes.drop 138, (4746 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4746_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4746
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4746 48 (by decide) sdw_sm_4746
  have hp0 := sd_pm_faithful_eq initPM 4746 138 (by decide) sdw_pm_4746
  have hd := recon_intermediateGoal_4746_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4746
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4747 : ∀ n ∈ sm.nodes.drop 48, (4747 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4747 : ∀ n ∈ pm.nodes.drop 138, (4747 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4747_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4747
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4747 48 (by decide) sdw_sm_4747
  have hp0 := sd_pm_faithful_eq initPM 4747 138 (by decide) sdw_pm_4747
  have hd := recon_intermediateGoal_4747_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4747
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4750 : ∀ n ∈ sm.nodes.drop 49, (4750 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7623 : ∀ n ∈ pm.nodes.drop 145, (7623 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7624 : ∀ n ∈ pm.nodes.drop 146, (7624 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4750_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4750
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4750 49 (by decide) sdw_sm_4750
  have hp0 := sd_pm_faithful_eq initPM 7623 145 (by decide) sdw_pm_7623
  have hp1 := sd_pm_faithful_eq initPM 7624 146 (by decide) sdw_pm_7624
  have hd := recon_intermediateGoal_4750_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4750
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
