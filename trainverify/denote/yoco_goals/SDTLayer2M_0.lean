/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer2DistributedMigration

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer2DistributedMigration.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4769 : ∀ n ∈ sm.nodes.drop 60, (4769 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4769 : ∀ n ∈ pm.nodes.drop 175, (4769 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4769_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4769
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4769 60 (by decide) sdw_sm_4769
  have hp0 := sd_pm_faithful_eq initPM 4769 175 (by decide) sdw_pm_4769
  have hd := recon_intermediateGoal_4769_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4769
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4771 : ∀ n ∈ sm.nodes.drop 64, (4771 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4771 : ∀ n ∈ pm.nodes.drop 181, (4771 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4771_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4771
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4771 64 (by decide) sdw_sm_4771
  have hp0 := sd_pm_faithful_eq initPM 4771 181 (by decide) sdw_pm_4771
  have hd := recon_intermediateGoal_4771_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4771
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4772 : ∀ n ∈ sm.nodes.drop 68, (4772 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_4772 : ∀ n ∈ pm.nodes.drop 189, (4772 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4772_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4772
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4772 68 (by decide) sdw_sm_4772
  have hp0 := sd_pm_faithful_eq initPM 4772 189 (by decide) sdw_pm_4772
  have hd := recon_intermediateGoal_4772_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4772
    rfl hs hp0 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4773 : ∀ n ∈ sm.nodes.drop 72, (4773 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7691 : ∀ n ∈ pm.nodes.drop 204, (7691 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7692 : ∀ n ∈ pm.nodes.drop 205, (7692 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4773_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4773
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4773 72 (by decide) sdw_sm_4773
  have hp0 := sd_pm_faithful_eq initPM 7691 204 (by decide) sdw_pm_7691
  have hp1 := sd_pm_faithful_eq initPM 7692 205 (by decide) sdw_pm_7692
  have hd := recon_intermediateGoal_4773_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4773
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4782 : ∀ n ∈ sm.nodes.drop 73, (4782 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7729 : ∀ n ∈ pm.nodes.drop 206, (7729 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7730 : ∀ n ∈ pm.nodes.drop 207, (7730 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4782_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4782
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4782 73 (by decide) sdw_sm_4782
  have hp0 := sd_pm_faithful_eq initPM 7729 206 (by decide) sdw_pm_7729
  have hp1 := sd_pm_faithful_eq initPM 7730 207 (by decide) sdw_pm_7730
  have hd := recon_intermediateGoal_4782_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4782
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4783 : ∀ n ∈ sm.nodes.drop 74, (4783 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7731 : ∀ n ∈ pm.nodes.drop 208, (7731 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7732 : ∀ n ∈ pm.nodes.drop 209, (7732 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4783_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4783
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4783 74 (by decide) sdw_sm_4783
  have hp0 := sd_pm_faithful_eq initPM 7731 208 (by decide) sdw_pm_7731
  have hp1 := sd_pm_faithful_eq initPM 7732 209 (by decide) sdw_pm_7732
  have hd := recon_intermediateGoal_4783_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4783
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4785 : ∀ n ∈ sm.nodes.drop 75, (4785 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7737 : ∀ n ∈ pm.nodes.drop 210, (7737 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7738 : ∀ n ∈ pm.nodes.drop 211, (7738 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4785_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4785
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4785 75 (by decide) sdw_sm_4785
  have hp0 := sd_pm_faithful_eq initPM 7737 210 (by decide) sdw_pm_7737
  have hp1 := sd_pm_faithful_eq initPM 7738 211 (by decide) sdw_pm_7738
  have hd := recon_intermediateGoal_4785_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4785
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4786 : ∀ n ∈ sm.nodes.drop 76, (4786 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7747 : ∀ n ∈ pm.nodes.drop 212, (7747 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7748 : ∀ n ∈ pm.nodes.drop 213, (7748 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4786_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4786
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4786 76 (by decide) sdw_sm_4786
  have hp0 := sd_pm_faithful_eq initPM 7747 212 (by decide) sdw_pm_7747
  have hp1 := sd_pm_faithful_eq initPM 7748 213 (by decide) sdw_pm_7748
  have hd := recon_intermediateGoal_4786_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4786
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4787 : ∀ n ∈ sm.nodes.drop 77, (4787 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7751 : ∀ n ∈ pm.nodes.drop 214, (7751 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7752 : ∀ n ∈ pm.nodes.drop 215, (7752 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4787_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4787
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4787 77 (by decide) sdw_sm_4787
  have hp0 := sd_pm_faithful_eq initPM 7751 214 (by decide) sdw_pm_7751
  have hp1 := sd_pm_faithful_eq initPM 7752 215 (by decide) sdw_pm_7752
  have hd := recon_intermediateGoal_4787_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4787
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4788 : ∀ n ∈ sm.nodes.drop 78, (4788 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7755 : ∀ n ∈ pm.nodes.drop 216, (7755 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7756 : ∀ n ∈ pm.nodes.drop 217, (7756 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4788_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4788
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4788 78 (by decide) sdw_sm_4788
  have hp0 := sd_pm_faithful_eq initPM 7755 216 (by decide) sdw_pm_7755
  have hp1 := sd_pm_faithful_eq initPM 7756 217 (by decide) sdw_pm_7756
  have hd := recon_intermediateGoal_4788_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4788
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4789 : ∀ n ∈ sm.nodes.drop 79, (4789 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7761 : ∀ n ∈ pm.nodes.drop 218, (7761 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7762 : ∀ n ∈ pm.nodes.drop 219, (7762 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4789_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4789
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4789 79 (by decide) sdw_sm_4789
  have hp0 := sd_pm_faithful_eq initPM 7761 218 (by decide) sdw_pm_7761
  have hp1 := sd_pm_faithful_eq initPM 7762 219 (by decide) sdw_pm_7762
  have hd := recon_intermediateGoal_4789_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4789
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4790 : ∀ n ∈ sm.nodes.drop 80, (4790 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7765 : ∀ n ∈ pm.nodes.drop 220, (7765 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7766 : ∀ n ∈ pm.nodes.drop 221, (7766 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4790_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4790
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4790 80 (by decide) sdw_sm_4790
  have hp0 := sd_pm_faithful_eq initPM 7765 220 (by decide) sdw_pm_7765
  have hp1 := sd_pm_faithful_eq initPM 7766 221 (by decide) sdw_pm_7766
  have hd := recon_intermediateGoal_4790_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4790
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4792 : ∀ n ∈ sm.nodes.drop 82, (4792 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7769 : ∀ n ∈ pm.nodes.drop 224, (7769 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7770 : ∀ n ∈ pm.nodes.drop 225, (7770 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4792_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4792
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4792 82 (by decide) sdw_sm_4792
  have hp0 := sd_pm_faithful_eq initPM 7769 224 (by decide) sdw_pm_7769
  have hp1 := sd_pm_faithful_eq initPM 7770 225 (by decide) sdw_pm_7770
  have hd := recon_intermediateGoal_4792_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4792
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4794 : ∀ n ∈ sm.nodes.drop 84, (4794 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7771 : ∀ n ∈ pm.nodes.drop 228, (7771 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7772 : ∀ n ∈ pm.nodes.drop 231, (7772 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4794_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4794
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4794 84 (by decide) sdw_sm_4794
  have hp0 := sd_pm_faithful_eq initPM 7771 228 (by decide) sdw_pm_7771
  have hp1 := sd_pm_faithful_eq initPM 7772 231 (by decide) sdw_pm_7772
  have hd := recon_intermediateGoal_4794_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4794
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4796 : ∀ n ∈ sm.nodes.drop 85, (4796 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7783 : ∀ n ∈ pm.nodes.drop 229, (7783 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7784 : ∀ n ∈ pm.nodes.drop 232, (7784 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4796_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4796
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4796 85 (by decide) sdw_sm_4796
  have hp0 := sd_pm_faithful_eq initPM 7783 229 (by decide) sdw_pm_7783
  have hp1 := sd_pm_faithful_eq initPM 7784 232 (by decide) sdw_pm_7784
  have hd := recon_intermediateGoal_4796_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4796
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4798 : ∀ n ∈ sm.nodes.drop 86, (4798 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7793 : ∀ n ∈ pm.nodes.drop 230, (7793 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7794 : ∀ n ∈ pm.nodes.drop 233, (7794 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4798_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4798
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4798 86 (by decide) sdw_sm_4798
  have hp0 := sd_pm_faithful_eq initPM 7793 230 (by decide) sdw_pm_7793
  have hp1 := sd_pm_faithful_eq initPM 7794 233 (by decide) sdw_pm_7794
  have hd := recon_intermediateGoal_4798_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4798
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4800 : ∀ n ∈ sm.nodes.drop 87, (4800 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7805 : ∀ n ∈ pm.nodes.drop 234, (7805 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7806 : ∀ n ∈ pm.nodes.drop 235, (7806 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4800_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4800
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4800 87 (by decide) sdw_sm_4800
  have hp0 := sd_pm_faithful_eq initPM 7805 234 (by decide) sdw_pm_7805
  have hp1 := sd_pm_faithful_eq initPM 7806 235 (by decide) sdw_pm_7806
  have hd := recon_intermediateGoal_4800_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4800
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4801 : ∀ n ∈ sm.nodes.drop 87, (4801 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7807 : ∀ n ∈ pm.nodes.drop 234, (7807 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7808 : ∀ n ∈ pm.nodes.drop 235, (7808 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4801_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4801
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4801 87 (by decide) sdw_sm_4801
  have hp0 := sd_pm_faithful_eq initPM 7807 234 (by decide) sdw_pm_7807
  have hp1 := sd_pm_faithful_eq initPM 7808 235 (by decide) sdw_pm_7808
  have hd := recon_intermediateGoal_4801_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4801
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4804 : ∀ n ∈ sm.nodes.drop 88, (4804 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7809 : ∀ n ∈ pm.nodes.drop 236, (7809 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7810 : ∀ n ∈ pm.nodes.drop 237, (7810 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4804_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4804
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4804 88 (by decide) sdw_sm_4804
  have hp0 := sd_pm_faithful_eq initPM 7809 236 (by decide) sdw_pm_7809
  have hp1 := sd_pm_faithful_eq initPM 7810 237 (by decide) sdw_pm_7810
  have hd := recon_intermediateGoal_4804_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4804
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4805 : ∀ n ∈ sm.nodes.drop 89, (4805 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7811 : ∀ n ∈ pm.nodes.drop 238, (7811 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7812 : ∀ n ∈ pm.nodes.drop 239, (7812 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4805_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4805
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4805 89 (by decide) sdw_sm_4805
  have hp0 := sd_pm_faithful_eq initPM 7811 238 (by decide) sdw_pm_7811
  have hp1 := sd_pm_faithful_eq initPM 7812 239 (by decide) sdw_pm_7812
  have hd := recon_intermediateGoal_4805_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4805
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4806 : ∀ n ∈ sm.nodes.drop 90, (4806 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7817 : ∀ n ∈ pm.nodes.drop 240, (7817 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7818 : ∀ n ∈ pm.nodes.drop 241, (7818 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4806_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4806
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4806 90 (by decide) sdw_sm_4806
  have hp0 := sd_pm_faithful_eq initPM 7817 240 (by decide) sdw_pm_7817
  have hp1 := sd_pm_faithful_eq initPM 7818 241 (by decide) sdw_pm_7818
  have hd := recon_intermediateGoal_4806_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4806
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4808 : ∀ n ∈ sm.nodes.drop 91, (4808 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7821 : ∀ n ∈ pm.nodes.drop 242, (7821 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7822 : ∀ n ∈ pm.nodes.drop 243, (7822 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4808_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4808
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4808 91 (by decide) sdw_sm_4808
  have hp0 := sd_pm_faithful_eq initPM 7821 242 (by decide) sdw_pm_7821
  have hp1 := sd_pm_faithful_eq initPM 7822 243 (by decide) sdw_pm_7822
  have hd := recon_intermediateGoal_4808_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4808
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4809 : ∀ n ∈ sm.nodes.drop 92, (4809 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7831 : ∀ n ∈ pm.nodes.drop 244, (7831 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7832 : ∀ n ∈ pm.nodes.drop 245, (7832 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4809_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4809
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4809 92 (by decide) sdw_sm_4809
  have hp0 := sd_pm_faithful_eq initPM 7831 244 (by decide) sdw_pm_7831
  have hp1 := sd_pm_faithful_eq initPM 7832 245 (by decide) sdw_pm_7832
  have hd := recon_intermediateGoal_4809_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4809
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4810 : ∀ n ∈ sm.nodes.drop 93, (4810 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7835 : ∀ n ∈ pm.nodes.drop 246, (7835 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7836 : ∀ n ∈ pm.nodes.drop 247, (7836 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4810_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4810
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4810 93 (by decide) sdw_sm_4810
  have hp0 := sd_pm_faithful_eq initPM 7835 246 (by decide) sdw_pm_7835
  have hp1 := sd_pm_faithful_eq initPM 7836 247 (by decide) sdw_pm_7836
  have hd := recon_intermediateGoal_4810_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4810
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4811 : ∀ n ∈ sm.nodes.drop 94, (4811 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7839 : ∀ n ∈ pm.nodes.drop 248, (7839 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7840 : ∀ n ∈ pm.nodes.drop 249, (7840 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4811_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4811
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4811 94 (by decide) sdw_sm_4811
  have hp0 := sd_pm_faithful_eq initPM 7839 248 (by decide) sdw_pm_7839
  have hp1 := sd_pm_faithful_eq initPM 7840 249 (by decide) sdw_pm_7840
  have hd := recon_intermediateGoal_4811_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4811
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4813 : ∀ n ∈ sm.nodes.drop 96, (4813 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7843 : ∀ n ∈ pm.nodes.drop 252, (7843 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7844 : ∀ n ∈ pm.nodes.drop 253, (7844 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4813_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4813
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4813 96 (by decide) sdw_sm_4813
  have hp0 := sd_pm_faithful_eq initPM 7843 252 (by decide) sdw_pm_7843
  have hp1 := sd_pm_faithful_eq initPM 7844 253 (by decide) sdw_pm_7844
  have hd := recon_intermediateGoal_4813_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4813
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4814 : ∀ n ∈ sm.nodes.drop 98, (4814 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7845 : ∀ n ∈ pm.nodes.drop 256, (7845 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7846 : ∀ n ∈ pm.nodes.drop 260, (7846 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4814_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4814
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4814 98 (by decide) sdw_sm_4814
  have hp0 := sd_pm_faithful_eq initPM 7845 256 (by decide) sdw_pm_7845
  have hp1 := sd_pm_faithful_eq initPM 7846 260 (by decide) sdw_pm_7846
  have hd := recon_intermediateGoal_4814_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4814
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4816 : ∀ n ∈ sm.nodes.drop 102, (4816 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7851 : ∀ n ∈ pm.nodes.drop 264, (7851 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7852 : ∀ n ∈ pm.nodes.drop 268, (7852 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4816_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4816
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4816 102 (by decide) sdw_sm_4816
  have hp0 := sd_pm_faithful_eq initPM 7851 264 (by decide) sdw_pm_7851
  have hp1 := sd_pm_faithful_eq initPM 7852 268 (by decide) sdw_pm_7852
  have hd := recon_intermediateGoal_4816_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4816
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4817 : ∀ n ∈ sm.nodes.drop 106, (4817 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7853 : ∀ n ∈ pm.nodes.drop 272, (7853 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7854 : ∀ n ∈ pm.nodes.drop 276, (7854 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4817_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4817
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4817 106 (by decide) sdw_sm_4817
  have hp0 := sd_pm_faithful_eq initPM 7853 272 (by decide) sdw_pm_7853
  have hp1 := sd_pm_faithful_eq initPM 7854 276 (by decide) sdw_pm_7854
  have hd := recon_intermediateGoal_4817_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4817
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4818 : ∀ n ∈ sm.nodes.drop 106, (4818 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7855 : ∀ n ∈ pm.nodes.drop 272, (7855 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7856 : ∀ n ∈ pm.nodes.drop 276, (7856 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4818_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4818
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4818 106 (by decide) sdw_sm_4818
  have hp0 := sd_pm_faithful_eq initPM 7855 272 (by decide) sdw_pm_7855
  have hp1 := sd_pm_faithful_eq initPM 7856 276 (by decide) sdw_pm_7856
  have hd := recon_intermediateGoal_4818_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4818
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4822 : ∀ n ∈ sm.nodes.drop 110, (4822 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7863 : ∀ n ∈ pm.nodes.drop 280, (7863 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7864 : ∀ n ∈ pm.nodes.drop 283, (7864 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4822_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4822
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4822 110 (by decide) sdw_sm_4822
  have hp0 := sd_pm_faithful_eq initPM 7863 280 (by decide) sdw_pm_7863
  have hp1 := sd_pm_faithful_eq initPM 7864 283 (by decide) sdw_pm_7864
  have hd := recon_intermediateGoal_4822_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4822
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4823 : ∀ n ∈ sm.nodes.drop 99, (4823 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7865 : ∀ n ∈ pm.nodes.drop 257, (7865 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7866 : ∀ n ∈ pm.nodes.drop 261, (7866 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4823_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4823
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4823 99 (by decide) sdw_sm_4823
  have hp0 := sd_pm_faithful_eq initPM 7865 257 (by decide) sdw_pm_7865
  have hp1 := sd_pm_faithful_eq initPM 7866 261 (by decide) sdw_pm_7866
  have hd := recon_intermediateGoal_4823_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4823
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4825 : ∀ n ∈ sm.nodes.drop 103, (4825 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7869 : ∀ n ∈ pm.nodes.drop 265, (7869 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7870 : ∀ n ∈ pm.nodes.drop 269, (7870 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4825_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4825
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4825 103 (by decide) sdw_sm_4825
  have hp0 := sd_pm_faithful_eq initPM 7869 265 (by decide) sdw_pm_7869
  have hp1 := sd_pm_faithful_eq initPM 7870 269 (by decide) sdw_pm_7870
  have hd := recon_intermediateGoal_4825_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4825
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4826 : ∀ n ∈ sm.nodes.drop 107, (4826 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7875 : ∀ n ∈ pm.nodes.drop 273, (7875 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7876 : ∀ n ∈ pm.nodes.drop 277, (7876 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4826_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4826
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4826 107 (by decide) sdw_sm_4826
  have hp0 := sd_pm_faithful_eq initPM 7875 273 (by decide) sdw_pm_7875
  have hp1 := sd_pm_faithful_eq initPM 7876 277 (by decide) sdw_pm_7876
  have hd := recon_intermediateGoal_4826_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4826
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4827 : ∀ n ∈ sm.nodes.drop 111, (4827 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7877 : ∀ n ∈ pm.nodes.drop 281, (7877 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7878 : ∀ n ∈ pm.nodes.drop 284, (7878 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4827_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4827
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4827 111 (by decide) sdw_sm_4827
  have hp0 := sd_pm_faithful_eq initPM 7877 281 (by decide) sdw_pm_7877
  have hp1 := sd_pm_faithful_eq initPM 7878 284 (by decide) sdw_pm_7878
  have hd := recon_intermediateGoal_4827_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4827
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4828 : ∀ n ∈ sm.nodes.drop 100, (4828 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7879 : ∀ n ∈ pm.nodes.drop 258, (7879 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7880 : ∀ n ∈ pm.nodes.drop 262, (7880 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4828_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4828
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4828 100 (by decide) sdw_sm_4828
  have hp0 := sd_pm_faithful_eq initPM 7879 258 (by decide) sdw_pm_7879
  have hp1 := sd_pm_faithful_eq initPM 7880 262 (by decide) sdw_pm_7880
  have hd := recon_intermediateGoal_4828_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4828
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4830 : ∀ n ∈ sm.nodes.drop 104, (4830 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7883 : ∀ n ∈ pm.nodes.drop 266, (7883 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7884 : ∀ n ∈ pm.nodes.drop 270, (7884 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4830_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4830
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4830 104 (by decide) sdw_sm_4830
  have hp0 := sd_pm_faithful_eq initPM 7883 266 (by decide) sdw_pm_7883
  have hp1 := sd_pm_faithful_eq initPM 7884 270 (by decide) sdw_pm_7884
  have hd := recon_intermediateGoal_4830_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4830
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4831 : ∀ n ∈ sm.nodes.drop 108, (4831 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7893 : ∀ n ∈ pm.nodes.drop 274, (7893 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7894 : ∀ n ∈ pm.nodes.drop 278, (7894 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4831_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4831
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4831 108 (by decide) sdw_sm_4831
  have hp0 := sd_pm_faithful_eq initPM 7893 274 (by decide) sdw_pm_7893
  have hp1 := sd_pm_faithful_eq initPM 7894 278 (by decide) sdw_pm_7894
  have hd := recon_intermediateGoal_4831_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4831
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4832 : ∀ n ∈ sm.nodes.drop 101, (4832 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7897 : ∀ n ∈ pm.nodes.drop 259, (7897 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7898 : ∀ n ∈ pm.nodes.drop 263, (7898 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4832_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4832
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4832 101 (by decide) sdw_sm_4832
  have hp0 := sd_pm_faithful_eq initPM 7897 259 (by decide) sdw_pm_7897
  have hp1 := sd_pm_faithful_eq initPM 7898 263 (by decide) sdw_pm_7898
  have hd := recon_intermediateGoal_4832_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4832
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4834 : ∀ n ∈ sm.nodes.drop 105, (4834 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7901 : ∀ n ∈ pm.nodes.drop 267, (7901 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7902 : ∀ n ∈ pm.nodes.drop 271, (7902 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4834_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4834
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4834 105 (by decide) sdw_sm_4834
  have hp0 := sd_pm_faithful_eq initPM 7901 267 (by decide) sdw_pm_7901
  have hp1 := sd_pm_faithful_eq initPM 7902 271 (by decide) sdw_pm_7902
  have hd := recon_intermediateGoal_4834_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4834
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4835 : ∀ n ∈ sm.nodes.drop 109, (4835 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7911 : ∀ n ∈ pm.nodes.drop 275, (7911 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7912 : ∀ n ∈ pm.nodes.drop 279, (7912 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4835_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4835
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4835 109 (by decide) sdw_sm_4835
  have hp0 := sd_pm_faithful_eq initPM 7911 275 (by decide) sdw_pm_7911
  have hp1 := sd_pm_faithful_eq initPM 7912 279 (by decide) sdw_pm_7912
  have hd := recon_intermediateGoal_4835_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4835
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4836 : ∀ n ∈ sm.nodes.drop 112, (4836 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7915 : ∀ n ∈ pm.nodes.drop 282, (7915 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7916 : ∀ n ∈ pm.nodes.drop 285, (7916 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4836_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4836
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4836 112 (by decide) sdw_sm_4836
  have hp0 := sd_pm_faithful_eq initPM 7915 282 (by decide) sdw_pm_7915
  have hp1 := sd_pm_faithful_eq initPM 7916 285 (by decide) sdw_pm_7916
  have hd := recon_intermediateGoal_4836_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4836
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4837 : ∀ n ∈ sm.nodes.drop 113, (4837 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7917 : ∀ n ∈ pm.nodes.drop 286, (7917 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7918 : ∀ n ∈ pm.nodes.drop 287, (7918 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4837_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4837
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4837 113 (by decide) sdw_sm_4837
  have hp0 := sd_pm_faithful_eq initPM 7917 286 (by decide) sdw_pm_7917
  have hp1 := sd_pm_faithful_eq initPM 7918 287 (by decide) sdw_pm_7918
  have hd := recon_intermediateGoal_4837_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4837
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4839 : ∀ n ∈ sm.nodes.drop 114, (4839 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7923 : ∀ n ∈ pm.nodes.drop 288, (7923 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7924 : ∀ n ∈ pm.nodes.drop 289, (7924 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4839_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4839
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4839 114 (by decide) sdw_sm_4839
  have hp0 := sd_pm_faithful_eq initPM 7923 288 (by decide) sdw_pm_7923
  have hp1 := sd_pm_faithful_eq initPM 7924 289 (by decide) sdw_pm_7924
  have hd := recon_intermediateGoal_4839_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4839
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4840 : ∀ n ∈ sm.nodes.drop 115, (4840 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7933 : ∀ n ∈ pm.nodes.drop 290, (7933 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7934 : ∀ n ∈ pm.nodes.drop 291, (7934 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4840_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4840
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4840 115 (by decide) sdw_sm_4840
  have hp0 := sd_pm_faithful_eq initPM 7933 290 (by decide) sdw_pm_7933
  have hp1 := sd_pm_faithful_eq initPM 7934 291 (by decide) sdw_pm_7934
  have hd := recon_intermediateGoal_4840_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4840
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4841 : ∀ n ∈ sm.nodes.drop 116, (4841 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7937 : ∀ n ∈ pm.nodes.drop 292, (7937 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7938 : ∀ n ∈ pm.nodes.drop 293, (7938 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4841_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4841
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4841 116 (by decide) sdw_sm_4841
  have hp0 := sd_pm_faithful_eq initPM 7937 292 (by decide) sdw_pm_7937
  have hp1 := sd_pm_faithful_eq initPM 7938 293 (by decide) sdw_pm_7938
  have hd := recon_intermediateGoal_4841_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4841
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4842 : ∀ n ∈ sm.nodes.drop 117, (4842 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7941 : ∀ n ∈ pm.nodes.drop 294, (7941 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7942 : ∀ n ∈ pm.nodes.drop 295, (7942 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4842_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4842
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4842 117 (by decide) sdw_sm_4842
  have hp0 := sd_pm_faithful_eq initPM 7941 294 (by decide) sdw_pm_7941
  have hp1 := sd_pm_faithful_eq initPM 7942 295 (by decide) sdw_pm_7942
  have hd := recon_intermediateGoal_4842_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4842
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4843 : ∀ n ∈ sm.nodes.drop 118, (4843 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7947 : ∀ n ∈ pm.nodes.drop 296, (7947 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7948 : ∀ n ∈ pm.nodes.drop 297, (7948 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4843_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4843
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4843 118 (by decide) sdw_sm_4843
  have hp0 := sd_pm_faithful_eq initPM 7947 296 (by decide) sdw_pm_7947
  have hp1 := sd_pm_faithful_eq initPM 7948 297 (by decide) sdw_pm_7948
  have hd := recon_intermediateGoal_4843_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4843
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4844 : ∀ n ∈ sm.nodes.drop 119, (4844 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7951 : ∀ n ∈ pm.nodes.drop 298, (7951 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7952 : ∀ n ∈ pm.nodes.drop 299, (7952 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4844_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4844
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4844 119 (by decide) sdw_sm_4844
  have hp0 := sd_pm_faithful_eq initPM 7951 298 (by decide) sdw_pm_7951
  have hp1 := sd_pm_faithful_eq initPM 7952 299 (by decide) sdw_pm_7952
  have hd := recon_intermediateGoal_4844_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4844
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4846 : ∀ n ∈ sm.nodes.drop 121, (4846 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7955 : ∀ n ∈ pm.nodes.drop 302, (7955 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7956 : ∀ n ∈ pm.nodes.drop 303, (7956 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4846_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4846
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4846 121 (by decide) sdw_sm_4846
  have hp0 := sd_pm_faithful_eq initPM 7955 302 (by decide) sdw_pm_7955
  have hp1 := sd_pm_faithful_eq initPM 7956 303 (by decide) sdw_pm_7956
  have hd := recon_intermediateGoal_4846_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4846
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4848 : ∀ n ∈ sm.nodes.drop 123, (4848 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7957 : ∀ n ∈ pm.nodes.drop 306, (7957 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7958 : ∀ n ∈ pm.nodes.drop 309, (7958 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4848_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4848
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4848 123 (by decide) sdw_sm_4848
  have hp0 := sd_pm_faithful_eq initPM 7957 306 (by decide) sdw_pm_7957
  have hp1 := sd_pm_faithful_eq initPM 7958 309 (by decide) sdw_pm_7958
  have hd := recon_intermediateGoal_4848_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4848
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4850 : ∀ n ∈ sm.nodes.drop 124, (4850 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7969 : ∀ n ∈ pm.nodes.drop 307, (7969 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7970 : ∀ n ∈ pm.nodes.drop 310, (7970 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4850_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4850
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4850 124 (by decide) sdw_sm_4850
  have hp0 := sd_pm_faithful_eq initPM 7969 307 (by decide) sdw_pm_7969
  have hp1 := sd_pm_faithful_eq initPM 7970 310 (by decide) sdw_pm_7970
  have hd := recon_intermediateGoal_4850_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4850
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4852 : ∀ n ∈ sm.nodes.drop 125, (4852 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7979 : ∀ n ∈ pm.nodes.drop 308, (7979 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7980 : ∀ n ∈ pm.nodes.drop 311, (7980 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4852_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4852
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4852 125 (by decide) sdw_sm_4852
  have hp0 := sd_pm_faithful_eq initPM 7979 308 (by decide) sdw_pm_7979
  have hp1 := sd_pm_faithful_eq initPM 7980 311 (by decide) sdw_pm_7980
  have hd := recon_intermediateGoal_4852_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4852
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4854 : ∀ n ∈ sm.nodes.drop 126, (4854 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7991 : ∀ n ∈ pm.nodes.drop 312, (7991 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7992 : ∀ n ∈ pm.nodes.drop 313, (7992 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4854_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4854
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4854 126 (by decide) sdw_sm_4854
  have hp0 := sd_pm_faithful_eq initPM 7991 312 (by decide) sdw_pm_7991
  have hp1 := sd_pm_faithful_eq initPM 7992 313 (by decide) sdw_pm_7992
  have hd := recon_intermediateGoal_4854_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4854
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4855 : ∀ n ∈ sm.nodes.drop 126, (4855 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7993 : ∀ n ∈ pm.nodes.drop 312, (7993 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7994 : ∀ n ∈ pm.nodes.drop 313, (7994 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4855_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4855
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4855 126 (by decide) sdw_sm_4855
  have hp0 := sd_pm_faithful_eq initPM 7993 312 (by decide) sdw_pm_7993
  have hp1 := sd_pm_faithful_eq initPM 7994 313 (by decide) sdw_pm_7994
  have hd := recon_intermediateGoal_4855_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4855
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4858 : ∀ n ∈ sm.nodes.drop 127, (4858 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7995 : ∀ n ∈ pm.nodes.drop 314, (7995 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7996 : ∀ n ∈ pm.nodes.drop 315, (7996 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4858_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4858
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4858 127 (by decide) sdw_sm_4858
  have hp0 := sd_pm_faithful_eq initPM 7995 314 (by decide) sdw_pm_7995
  have hp1 := sd_pm_faithful_eq initPM 7996 315 (by decide) sdw_pm_7996
  have hd := recon_intermediateGoal_4858_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4858
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4859 : ∀ n ∈ sm.nodes.drop 128, (4859 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7997 : ∀ n ∈ pm.nodes.drop 316, (7997 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_7998 : ∀ n ∈ pm.nodes.drop 317, (7998 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4859_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4859
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4859 128 (by decide) sdw_sm_4859
  have hp0 := sd_pm_faithful_eq initPM 7997 316 (by decide) sdw_pm_7997
  have hp1 := sd_pm_faithful_eq initPM 7998 317 (by decide) sdw_pm_7998
  have hd := recon_intermediateGoal_4859_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4859
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4860 : ∀ n ∈ sm.nodes.drop 129, (4860 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8003 : ∀ n ∈ pm.nodes.drop 318, (8003 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8004 : ∀ n ∈ pm.nodes.drop 319, (8004 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4860_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4860
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4860 129 (by decide) sdw_sm_4860
  have hp0 := sd_pm_faithful_eq initPM 8003 318 (by decide) sdw_pm_8003
  have hp1 := sd_pm_faithful_eq initPM 8004 319 (by decide) sdw_pm_8004
  have hd := recon_intermediateGoal_4860_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4860
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4862 : ∀ n ∈ sm.nodes.drop 130, (4862 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8007 : ∀ n ∈ pm.nodes.drop 320, (8007 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8008 : ∀ n ∈ pm.nodes.drop 321, (8008 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4862_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4862
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4862 130 (by decide) sdw_sm_4862
  have hp0 := sd_pm_faithful_eq initPM 8007 320 (by decide) sdw_pm_8007
  have hp1 := sd_pm_faithful_eq initPM 8008 321 (by decide) sdw_pm_8008
  have hd := recon_intermediateGoal_4862_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4862
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4863 : ∀ n ∈ sm.nodes.drop 131, (4863 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8017 : ∀ n ∈ pm.nodes.drop 322, (8017 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8018 : ∀ n ∈ pm.nodes.drop 323, (8018 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4863_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4863
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4863 131 (by decide) sdw_sm_4863
  have hp0 := sd_pm_faithful_eq initPM 8017 322 (by decide) sdw_pm_8017
  have hp1 := sd_pm_faithful_eq initPM 8018 323 (by decide) sdw_pm_8018
  have hd := recon_intermediateGoal_4863_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4863
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
