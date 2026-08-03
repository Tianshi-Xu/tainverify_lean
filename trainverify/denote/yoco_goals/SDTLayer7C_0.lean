/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer7DistributedContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer7DistributedContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5062 : ∀ n ∈ sm.nodes.drop 277, (5062 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8699 : ∀ n ∈ pm.nodes.drop 614, (8699 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8700 : ∀ n ∈ pm.nodes.drop 615, (8700 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5062_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5062
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5062 277 (by decide) sdw_sm_5062
  have hp0 := sd_pm_faithful_eq initPM 8699 614 (by decide) sdw_pm_8699
  have hp1 := sd_pm_faithful_eq initPM 8700 615 (by decide) sdw_pm_8700
  have hd := recon_intermediateGoal_5062_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5062
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5064 : ∀ n ∈ sm.nodes.drop 279, (5064 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8701 : ∀ n ∈ pm.nodes.drop 618, (8701 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8702 : ∀ n ∈ pm.nodes.drop 621, (8702 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5064_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5064
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5064 279 (by decide) sdw_sm_5064
  have hp0 := sd_pm_faithful_eq initPM 8701 618 (by decide) sdw_pm_8701
  have hp1 := sd_pm_faithful_eq initPM 8702 621 (by decide) sdw_pm_8702
  have hd := recon_intermediateGoal_5064_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5064
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5066 : ∀ n ∈ sm.nodes.drop 280, (5066 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8713 : ∀ n ∈ pm.nodes.drop 619, (8713 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8714 : ∀ n ∈ pm.nodes.drop 622, (8714 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5066_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5066
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5066 280 (by decide) sdw_sm_5066
  have hp0 := sd_pm_faithful_eq initPM 8713 619 (by decide) sdw_pm_8713
  have hp1 := sd_pm_faithful_eq initPM 8714 622 (by decide) sdw_pm_8714
  have hd := recon_intermediateGoal_5066_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5066
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5068 : ∀ n ∈ sm.nodes.drop 281, (5068 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8723 : ∀ n ∈ pm.nodes.drop 620, (8723 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8724 : ∀ n ∈ pm.nodes.drop 623, (8724 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5068_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5068
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5068 281 (by decide) sdw_sm_5068
  have hp0 := sd_pm_faithful_eq initPM 8723 620 (by decide) sdw_pm_8723
  have hp1 := sd_pm_faithful_eq initPM 8724 623 (by decide) sdw_pm_8724
  have hd := recon_intermediateGoal_5068_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5068
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5070 : ∀ n ∈ sm.nodes.drop 282, (5070 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8735 : ∀ n ∈ pm.nodes.drop 624, (8735 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8736 : ∀ n ∈ pm.nodes.drop 625, (8736 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5070_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5070
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5070 282 (by decide) sdw_sm_5070
  have hp0 := sd_pm_faithful_eq initPM 8735 624 (by decide) sdw_pm_8735
  have hp1 := sd_pm_faithful_eq initPM 8736 625 (by decide) sdw_pm_8736
  have hd := recon_intermediateGoal_5070_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5070
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5071 : ∀ n ∈ sm.nodes.drop 282, (5071 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8737 : ∀ n ∈ pm.nodes.drop 624, (8737 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8738 : ∀ n ∈ pm.nodes.drop 625, (8738 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5071_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5071
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5071 282 (by decide) sdw_sm_5071
  have hp0 := sd_pm_faithful_eq initPM 8737 624 (by decide) sdw_pm_8737
  have hp1 := sd_pm_faithful_eq initPM 8738 625 (by decide) sdw_pm_8738
  have hd := recon_intermediateGoal_5071_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5071
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5074 : ∀ n ∈ sm.nodes.drop 283, (5074 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8739 : ∀ n ∈ pm.nodes.drop 626, (8739 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8740 : ∀ n ∈ pm.nodes.drop 627, (8740 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5074_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5074
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5074 283 (by decide) sdw_sm_5074
  have hp0 := sd_pm_faithful_eq initPM 8739 626 (by decide) sdw_pm_8739
  have hp1 := sd_pm_faithful_eq initPM 8740 627 (by decide) sdw_pm_8740
  have hd := recon_intermediateGoal_5074_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5074
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5075 : ∀ n ∈ sm.nodes.drop 284, (5075 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8741 : ∀ n ∈ pm.nodes.drop 628, (8741 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8742 : ∀ n ∈ pm.nodes.drop 629, (8742 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5075_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5075
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5075 284 (by decide) sdw_sm_5075
  have hp0 := sd_pm_faithful_eq initPM 8741 628 (by decide) sdw_pm_8741
  have hp1 := sd_pm_faithful_eq initPM 8742 629 (by decide) sdw_pm_8742
  have hd := recon_intermediateGoal_5075_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5075
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5076 : ∀ n ∈ sm.nodes.drop 285, (5076 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8747 : ∀ n ∈ pm.nodes.drop 630, (8747 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8748 : ∀ n ∈ pm.nodes.drop 631, (8748 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5076_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5076
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5076 285 (by decide) sdw_sm_5076
  have hp0 := sd_pm_faithful_eq initPM 8747 630 (by decide) sdw_pm_8747
  have hp1 := sd_pm_faithful_eq initPM 8748 631 (by decide) sdw_pm_8748
  have hd := recon_intermediateGoal_5076_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5076
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5078 : ∀ n ∈ sm.nodes.drop 286, (5078 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8751 : ∀ n ∈ pm.nodes.drop 632, (8751 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8752 : ∀ n ∈ pm.nodes.drop 633, (8752 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5078_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5078
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5078 286 (by decide) sdw_sm_5078
  have hp0 := sd_pm_faithful_eq initPM 8751 632 (by decide) sdw_pm_8751
  have hp1 := sd_pm_faithful_eq initPM 8752 633 (by decide) sdw_pm_8752
  have hd := recon_intermediateGoal_5078_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5078
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5079 : ∀ n ∈ sm.nodes.drop 287, (5079 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8761 : ∀ n ∈ pm.nodes.drop 634, (8761 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8762 : ∀ n ∈ pm.nodes.drop 635, (8762 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5079_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5079
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5079 287 (by decide) sdw_sm_5079
  have hp0 := sd_pm_faithful_eq initPM 8761 634 (by decide) sdw_pm_8761
  have hp1 := sd_pm_faithful_eq initPM 8762 635 (by decide) sdw_pm_8762
  have hd := recon_intermediateGoal_5079_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5079
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5080 : ∀ n ∈ sm.nodes.drop 288, (5080 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8765 : ∀ n ∈ pm.nodes.drop 636, (8765 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8766 : ∀ n ∈ pm.nodes.drop 637, (8766 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5080_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5080
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5080 288 (by decide) sdw_sm_5080
  have hp0 := sd_pm_faithful_eq initPM 8765 636 (by decide) sdw_pm_8765
  have hp1 := sd_pm_faithful_eq initPM 8766 637 (by decide) sdw_pm_8766
  have hd := recon_intermediateGoal_5080_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5080
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5081 : ∀ n ∈ sm.nodes.drop 289, (5081 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8769 : ∀ n ∈ pm.nodes.drop 638, (8769 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8770 : ∀ n ∈ pm.nodes.drop 639, (8770 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5081_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5081
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5081 289 (by decide) sdw_sm_5081
  have hp0 := sd_pm_faithful_eq initPM 8769 638 (by decide) sdw_pm_8769
  have hp1 := sd_pm_faithful_eq initPM 8770 639 (by decide) sdw_pm_8770
  have hd := recon_intermediateGoal_5081_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5081
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5083 : ∀ n ∈ sm.nodes.drop 291, (5083 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8773 : ∀ n ∈ pm.nodes.drop 642, (8773 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8774 : ∀ n ∈ pm.nodes.drop 643, (8774 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5083_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5083
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5083 291 (by decide) sdw_sm_5083
  have hp0 := sd_pm_faithful_eq initPM 8773 642 (by decide) sdw_pm_8773
  have hp1 := sd_pm_faithful_eq initPM 8774 643 (by decide) sdw_pm_8774
  have hd := recon_intermediateGoal_5083_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5083
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5084 : ∀ n ∈ sm.nodes.drop 293, (5084 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8775 : ∀ n ∈ pm.nodes.drop 646, (8775 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8776 : ∀ n ∈ pm.nodes.drop 650, (8776 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5084_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5084
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5084 293 (by decide) sdw_sm_5084
  have hp0 := sd_pm_faithful_eq initPM 8775 646 (by decide) sdw_pm_8775
  have hp1 := sd_pm_faithful_eq initPM 8776 650 (by decide) sdw_pm_8776
  have hd := recon_intermediateGoal_5084_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5084
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5086 : ∀ n ∈ sm.nodes.drop 297, (5086 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8781 : ∀ n ∈ pm.nodes.drop 654, (8781 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8782 : ∀ n ∈ pm.nodes.drop 658, (8782 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5086_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5086
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5086 297 (by decide) sdw_sm_5086
  have hp0 := sd_pm_faithful_eq initPM 8781 654 (by decide) sdw_pm_8781
  have hp1 := sd_pm_faithful_eq initPM 8782 658 (by decide) sdw_pm_8782
  have hd := recon_intermediateGoal_5086_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5086
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5087 : ∀ n ∈ sm.nodes.drop 301, (5087 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8783 : ∀ n ∈ pm.nodes.drop 662, (8783 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8784 : ∀ n ∈ pm.nodes.drop 666, (8784 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5087_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5087
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5087 301 (by decide) sdw_sm_5087
  have hp0 := sd_pm_faithful_eq initPM 8783 662 (by decide) sdw_pm_8783
  have hp1 := sd_pm_faithful_eq initPM 8784 666 (by decide) sdw_pm_8784
  have hd := recon_intermediateGoal_5087_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5087
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5088 : ∀ n ∈ sm.nodes.drop 301, (5088 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8785 : ∀ n ∈ pm.nodes.drop 662, (8785 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8786 : ∀ n ∈ pm.nodes.drop 666, (8786 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5088_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5088
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5088 301 (by decide) sdw_sm_5088
  have hp0 := sd_pm_faithful_eq initPM 8785 662 (by decide) sdw_pm_8785
  have hp1 := sd_pm_faithful_eq initPM 8786 666 (by decide) sdw_pm_8786
  have hd := recon_intermediateGoal_5088_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5088
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5092 : ∀ n ∈ sm.nodes.drop 305, (5092 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8793 : ∀ n ∈ pm.nodes.drop 670, (8793 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8794 : ∀ n ∈ pm.nodes.drop 673, (8794 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5092_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5092
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5092 305 (by decide) sdw_sm_5092
  have hp0 := sd_pm_faithful_eq initPM 8793 670 (by decide) sdw_pm_8793
  have hp1 := sd_pm_faithful_eq initPM 8794 673 (by decide) sdw_pm_8794
  have hd := recon_intermediateGoal_5092_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5092
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5093 : ∀ n ∈ sm.nodes.drop 294, (5093 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8795 : ∀ n ∈ pm.nodes.drop 647, (8795 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8796 : ∀ n ∈ pm.nodes.drop 651, (8796 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5093_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5093
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5093 294 (by decide) sdw_sm_5093
  have hp0 := sd_pm_faithful_eq initPM 8795 647 (by decide) sdw_pm_8795
  have hp1 := sd_pm_faithful_eq initPM 8796 651 (by decide) sdw_pm_8796
  have hd := recon_intermediateGoal_5093_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5093
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5095 : ∀ n ∈ sm.nodes.drop 298, (5095 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8799 : ∀ n ∈ pm.nodes.drop 655, (8799 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8800 : ∀ n ∈ pm.nodes.drop 659, (8800 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5095_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5095
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5095 298 (by decide) sdw_sm_5095
  have hp0 := sd_pm_faithful_eq initPM 8799 655 (by decide) sdw_pm_8799
  have hp1 := sd_pm_faithful_eq initPM 8800 659 (by decide) sdw_pm_8800
  have hd := recon_intermediateGoal_5095_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5095
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5096 : ∀ n ∈ sm.nodes.drop 302, (5096 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8805 : ∀ n ∈ pm.nodes.drop 663, (8805 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8806 : ∀ n ∈ pm.nodes.drop 667, (8806 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5096_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5096
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5096 302 (by decide) sdw_sm_5096
  have hp0 := sd_pm_faithful_eq initPM 8805 663 (by decide) sdw_pm_8805
  have hp1 := sd_pm_faithful_eq initPM 8806 667 (by decide) sdw_pm_8806
  have hd := recon_intermediateGoal_5096_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5096
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5097 : ∀ n ∈ sm.nodes.drop 306, (5097 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8807 : ∀ n ∈ pm.nodes.drop 671, (8807 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8808 : ∀ n ∈ pm.nodes.drop 674, (8808 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5097_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5097
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5097 306 (by decide) sdw_sm_5097
  have hp0 := sd_pm_faithful_eq initPM 8807 671 (by decide) sdw_pm_8807
  have hp1 := sd_pm_faithful_eq initPM 8808 674 (by decide) sdw_pm_8808
  have hd := recon_intermediateGoal_5097_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5097
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5098 : ∀ n ∈ sm.nodes.drop 295, (5098 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8809 : ∀ n ∈ pm.nodes.drop 648, (8809 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8810 : ∀ n ∈ pm.nodes.drop 652, (8810 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5098_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5098
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5098 295 (by decide) sdw_sm_5098
  have hp0 := sd_pm_faithful_eq initPM 8809 648 (by decide) sdw_pm_8809
  have hp1 := sd_pm_faithful_eq initPM 8810 652 (by decide) sdw_pm_8810
  have hd := recon_intermediateGoal_5098_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5098
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5100 : ∀ n ∈ sm.nodes.drop 299, (5100 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8813 : ∀ n ∈ pm.nodes.drop 656, (8813 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8814 : ∀ n ∈ pm.nodes.drop 660, (8814 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5100_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5100
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5100 299 (by decide) sdw_sm_5100
  have hp0 := sd_pm_faithful_eq initPM 8813 656 (by decide) sdw_pm_8813
  have hp1 := sd_pm_faithful_eq initPM 8814 660 (by decide) sdw_pm_8814
  have hd := recon_intermediateGoal_5100_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5100
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5101 : ∀ n ∈ sm.nodes.drop 303, (5101 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8823 : ∀ n ∈ pm.nodes.drop 664, (8823 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8824 : ∀ n ∈ pm.nodes.drop 668, (8824 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5101_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5101
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5101 303 (by decide) sdw_sm_5101
  have hp0 := sd_pm_faithful_eq initPM 8823 664 (by decide) sdw_pm_8823
  have hp1 := sd_pm_faithful_eq initPM 8824 668 (by decide) sdw_pm_8824
  have hd := recon_intermediateGoal_5101_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5101
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5102 : ∀ n ∈ sm.nodes.drop 296, (5102 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8827 : ∀ n ∈ pm.nodes.drop 649, (8827 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8828 : ∀ n ∈ pm.nodes.drop 653, (8828 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5102_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5102
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5102 296 (by decide) sdw_sm_5102
  have hp0 := sd_pm_faithful_eq initPM 8827 649 (by decide) sdw_pm_8827
  have hp1 := sd_pm_faithful_eq initPM 8828 653 (by decide) sdw_pm_8828
  have hd := recon_intermediateGoal_5102_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5102
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5104 : ∀ n ∈ sm.nodes.drop 300, (5104 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8831 : ∀ n ∈ pm.nodes.drop 657, (8831 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8832 : ∀ n ∈ pm.nodes.drop 661, (8832 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5104_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5104
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5104 300 (by decide) sdw_sm_5104
  have hp0 := sd_pm_faithful_eq initPM 8831 657 (by decide) sdw_pm_8831
  have hp1 := sd_pm_faithful_eq initPM 8832 661 (by decide) sdw_pm_8832
  have hd := recon_intermediateGoal_5104_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5104
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5105 : ∀ n ∈ sm.nodes.drop 304, (5105 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8841 : ∀ n ∈ pm.nodes.drop 665, (8841 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8842 : ∀ n ∈ pm.nodes.drop 669, (8842 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5105_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5105
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5105 304 (by decide) sdw_sm_5105
  have hp0 := sd_pm_faithful_eq initPM 8841 665 (by decide) sdw_pm_8841
  have hp1 := sd_pm_faithful_eq initPM 8842 669 (by decide) sdw_pm_8842
  have hd := recon_intermediateGoal_5105_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5105
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5106 : ∀ n ∈ sm.nodes.drop 307, (5106 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8845 : ∀ n ∈ pm.nodes.drop 672, (8845 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8846 : ∀ n ∈ pm.nodes.drop 675, (8846 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5106_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5106
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5106 307 (by decide) sdw_sm_5106
  have hp0 := sd_pm_faithful_eq initPM 8845 672 (by decide) sdw_pm_8845
  have hp1 := sd_pm_faithful_eq initPM 8846 675 (by decide) sdw_pm_8846
  have hd := recon_intermediateGoal_5106_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5106
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5107 : ∀ n ∈ sm.nodes.drop 308, (5107 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8847 : ∀ n ∈ pm.nodes.drop 676, (8847 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8848 : ∀ n ∈ pm.nodes.drop 677, (8848 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5107_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5107
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5107 308 (by decide) sdw_sm_5107
  have hp0 := sd_pm_faithful_eq initPM 8847 676 (by decide) sdw_pm_8847
  have hp1 := sd_pm_faithful_eq initPM 8848 677 (by decide) sdw_pm_8848
  have hd := recon_intermediateGoal_5107_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5107
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5109 : ∀ n ∈ sm.nodes.drop 309, (5109 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8853 : ∀ n ∈ pm.nodes.drop 678, (8853 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8854 : ∀ n ∈ pm.nodes.drop 679, (8854 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5109_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5109
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5109 309 (by decide) sdw_sm_5109
  have hp0 := sd_pm_faithful_eq initPM 8853 678 (by decide) sdw_pm_8853
  have hp1 := sd_pm_faithful_eq initPM 8854 679 (by decide) sdw_pm_8854
  have hd := recon_intermediateGoal_5109_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5109
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5110 : ∀ n ∈ sm.nodes.drop 310, (5110 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8863 : ∀ n ∈ pm.nodes.drop 680, (8863 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8864 : ∀ n ∈ pm.nodes.drop 681, (8864 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5110_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5110
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5110 310 (by decide) sdw_sm_5110
  have hp0 := sd_pm_faithful_eq initPM 8863 680 (by decide) sdw_pm_8863
  have hp1 := sd_pm_faithful_eq initPM 8864 681 (by decide) sdw_pm_8864
  have hd := recon_intermediateGoal_5110_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5110
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5111 : ∀ n ∈ sm.nodes.drop 311, (5111 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8867 : ∀ n ∈ pm.nodes.drop 682, (8867 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8868 : ∀ n ∈ pm.nodes.drop 683, (8868 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5111_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5111
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5111 311 (by decide) sdw_sm_5111
  have hp0 := sd_pm_faithful_eq initPM 8867 682 (by decide) sdw_pm_8867
  have hp1 := sd_pm_faithful_eq initPM 8868 683 (by decide) sdw_pm_8868
  have hd := recon_intermediateGoal_5111_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5111
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5112 : ∀ n ∈ sm.nodes.drop 312, (5112 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8871 : ∀ n ∈ pm.nodes.drop 684, (8871 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8872 : ∀ n ∈ pm.nodes.drop 685, (8872 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5112_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5112
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5112 312 (by decide) sdw_sm_5112
  have hp0 := sd_pm_faithful_eq initPM 8871 684 (by decide) sdw_pm_8871
  have hp1 := sd_pm_faithful_eq initPM 8872 685 (by decide) sdw_pm_8872
  have hd := recon_intermediateGoal_5112_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5112
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5113 : ∀ n ∈ sm.nodes.drop 313, (5113 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8877 : ∀ n ∈ pm.nodes.drop 686, (8877 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8878 : ∀ n ∈ pm.nodes.drop 687, (8878 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5113_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5113
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5113 313 (by decide) sdw_sm_5113
  have hp0 := sd_pm_faithful_eq initPM 8877 686 (by decide) sdw_pm_8877
  have hp1 := sd_pm_faithful_eq initPM 8878 687 (by decide) sdw_pm_8878
  have hd := recon_intermediateGoal_5113_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5113
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5114 : ∀ n ∈ sm.nodes.drop 314, (5114 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8881 : ∀ n ∈ pm.nodes.drop 688, (8881 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8882 : ∀ n ∈ pm.nodes.drop 689, (8882 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5114_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5114
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5114 314 (by decide) sdw_sm_5114
  have hp0 := sd_pm_faithful_eq initPM 8881 688 (by decide) sdw_pm_8881
  have hp1 := sd_pm_faithful_eq initPM 8882 689 (by decide) sdw_pm_8882
  have hd := recon_intermediateGoal_5114_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5114
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7751 : ∀ n ∈ sm.nodes.drop 276, (7751 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15225 : ∀ n ∈ pm.nodes.drop 612, (15225 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15233 : ∀ n ∈ pm.nodes.drop 613, (15233 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7751_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7751
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7751 276 (by decide) sdw_sm_7751
  have hp0 := sd_pm_faithful_eq initPM 15225 612 (by decide) sdw_pm_15225
  have hp1 := sd_pm_faithful_eq initPM 15233 613 (by decide) sdw_pm_15233
  have hd := recon_intermediateGoal_7751_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7751
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7772 : ∀ n ∈ sm.nodes.drop 290, (7772 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15267 : ∀ n ∈ pm.nodes.drop 640, (15267 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15275 : ∀ n ∈ pm.nodes.drop 641, (15275 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7772_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7772
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7772 290 (by decide) sdw_sm_7772
  have hp0 := sd_pm_faithful_eq initPM 15267 640 (by decide) sdw_pm_15267
  have hp1 := sd_pm_faithful_eq initPM 15275 641 (by decide) sdw_pm_15275
  have hd := recon_intermediateGoal_7772_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7772
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7783 : ∀ n ∈ sm.nodes.drop 292, (7783 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15286 : ∀ n ∈ pm.nodes.drop 644, (15286 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15309 : ∀ n ∈ pm.nodes.drop 645, (15309 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7783_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7783
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7783 292 (by decide) sdw_sm_7783
  have hp0 := sd_pm_faithful_eq initPM 15286 644 (by decide) sdw_pm_15286
  have hp1 := sd_pm_faithful_eq initPM 15309 645 (by decide) sdw_pm_15309
  have hd := recon_intermediateGoal_7783_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7783
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
