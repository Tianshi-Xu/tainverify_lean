/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer6DistributedContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer6DistributedContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4984 : ∀ n ∈ sm.nodes.drop 227, (4984 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8421 : ∀ n ∈ pm.nodes.drop 514, (8421 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8422 : ∀ n ∈ pm.nodes.drop 517, (8422 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4984_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4984
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4984 227 (by decide) sdw_sm_4984
  have hp0 := sd_pm_faithful_eq initPM 8421 514 (by decide) sdw_pm_8421
  have hp1 := sd_pm_faithful_eq initPM 8422 517 (by decide) sdw_pm_8422
  have hd := recon_intermediateGoal_4984_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4984
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5004 : ∀ n ∈ sm.nodes.drop 234, (5004 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8499 : ∀ n ∈ pm.nodes.drop 528, (8499 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8500 : ∀ n ∈ pm.nodes.drop 529, (8500 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5004_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5004
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5004 234 (by decide) sdw_sm_5004
  have hp0 := sd_pm_faithful_eq initPM 8499 528 (by decide) sdw_pm_8499
  have hp1 := sd_pm_faithful_eq initPM 8500 529 (by decide) sdw_pm_8500
  have hd := recon_intermediateGoal_5004_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5004
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5005 : ∀ n ∈ sm.nodes.drop 235, (5005 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8505 : ∀ n ∈ pm.nodes.drop 530, (8505 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8506 : ∀ n ∈ pm.nodes.drop 531, (8506 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5005_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5005
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5005 235 (by decide) sdw_sm_5005
  have hp0 := sd_pm_faithful_eq initPM 8505 530 (by decide) sdw_pm_8505
  have hp1 := sd_pm_faithful_eq initPM 8506 531 (by decide) sdw_pm_8506
  have hd := recon_intermediateGoal_5005_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5005
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5006 : ∀ n ∈ sm.nodes.drop 236, (5006 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8509 : ∀ n ∈ pm.nodes.drop 532, (8509 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8510 : ∀ n ∈ pm.nodes.drop 533, (8510 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5006_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5006
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5006 236 (by decide) sdw_sm_5006
  have hp0 := sd_pm_faithful_eq initPM 8509 532 (by decide) sdw_pm_8509
  have hp1 := sd_pm_faithful_eq initPM 8510 533 (by decide) sdw_pm_8510
  have hd := recon_intermediateGoal_5006_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5006
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5008 : ∀ n ∈ sm.nodes.drop 238, (5008 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8513 : ∀ n ∈ pm.nodes.drop 536, (8513 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8514 : ∀ n ∈ pm.nodes.drop 537, (8514 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5008_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5008
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5008 238 (by decide) sdw_sm_5008
  have hp0 := sd_pm_faithful_eq initPM 8513 536 (by decide) sdw_pm_8513
  have hp1 := sd_pm_faithful_eq initPM 8514 537 (by decide) sdw_pm_8514
  have hd := recon_intermediateGoal_5008_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5008
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5010 : ∀ n ∈ sm.nodes.drop 240, (5010 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8515 : ∀ n ∈ pm.nodes.drop 540, (8515 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8516 : ∀ n ∈ pm.nodes.drop 543, (8516 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5010_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5010
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5010 240 (by decide) sdw_sm_5010
  have hp0 := sd_pm_faithful_eq initPM 8515 540 (by decide) sdw_pm_8515
  have hp1 := sd_pm_faithful_eq initPM 8516 543 (by decide) sdw_pm_8516
  have hd := recon_intermediateGoal_5010_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5010
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5012 : ∀ n ∈ sm.nodes.drop 241, (5012 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8527 : ∀ n ∈ pm.nodes.drop 541, (8527 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8528 : ∀ n ∈ pm.nodes.drop 544, (8528 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5012_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5012
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5012 241 (by decide) sdw_sm_5012
  have hp0 := sd_pm_faithful_eq initPM 8527 541 (by decide) sdw_pm_8527
  have hp1 := sd_pm_faithful_eq initPM 8528 544 (by decide) sdw_pm_8528
  have hd := recon_intermediateGoal_5012_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5012
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5014 : ∀ n ∈ sm.nodes.drop 242, (5014 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8537 : ∀ n ∈ pm.nodes.drop 542, (8537 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8538 : ∀ n ∈ pm.nodes.drop 545, (8538 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5014_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5014
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5014 242 (by decide) sdw_sm_5014
  have hp0 := sd_pm_faithful_eq initPM 8537 542 (by decide) sdw_pm_8537
  have hp1 := sd_pm_faithful_eq initPM 8538 545 (by decide) sdw_pm_8538
  have hd := recon_intermediateGoal_5014_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5014
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5016 : ∀ n ∈ sm.nodes.drop 243, (5016 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8549 : ∀ n ∈ pm.nodes.drop 546, (8549 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8550 : ∀ n ∈ pm.nodes.drop 547, (8550 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5016_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5016
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5016 243 (by decide) sdw_sm_5016
  have hp0 := sd_pm_faithful_eq initPM 8549 546 (by decide) sdw_pm_8549
  have hp1 := sd_pm_faithful_eq initPM 8550 547 (by decide) sdw_pm_8550
  have hd := recon_intermediateGoal_5016_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5016
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5017 : ∀ n ∈ sm.nodes.drop 243, (5017 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8551 : ∀ n ∈ pm.nodes.drop 546, (8551 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8552 : ∀ n ∈ pm.nodes.drop 547, (8552 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5017_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5017
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5017 243 (by decide) sdw_sm_5017
  have hp0 := sd_pm_faithful_eq initPM 8551 546 (by decide) sdw_pm_8551
  have hp1 := sd_pm_faithful_eq initPM 8552 547 (by decide) sdw_pm_8552
  have hd := recon_intermediateGoal_5017_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5017
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5020 : ∀ n ∈ sm.nodes.drop 244, (5020 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8553 : ∀ n ∈ pm.nodes.drop 548, (8553 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8554 : ∀ n ∈ pm.nodes.drop 549, (8554 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5020_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5020
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5020 244 (by decide) sdw_sm_5020
  have hp0 := sd_pm_faithful_eq initPM 8553 548 (by decide) sdw_pm_8553
  have hp1 := sd_pm_faithful_eq initPM 8554 549 (by decide) sdw_pm_8554
  have hd := recon_intermediateGoal_5020_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5020
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5021 : ∀ n ∈ sm.nodes.drop 245, (5021 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8555 : ∀ n ∈ pm.nodes.drop 550, (8555 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8556 : ∀ n ∈ pm.nodes.drop 551, (8556 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5021_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5021
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5021 245 (by decide) sdw_sm_5021
  have hp0 := sd_pm_faithful_eq initPM 8555 550 (by decide) sdw_pm_8555
  have hp1 := sd_pm_faithful_eq initPM 8556 551 (by decide) sdw_pm_8556
  have hd := recon_intermediateGoal_5021_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5021
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5022 : ∀ n ∈ sm.nodes.drop 246, (5022 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8561 : ∀ n ∈ pm.nodes.drop 552, (8561 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8562 : ∀ n ∈ pm.nodes.drop 553, (8562 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5022_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5022
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5022 246 (by decide) sdw_sm_5022
  have hp0 := sd_pm_faithful_eq initPM 8561 552 (by decide) sdw_pm_8561
  have hp1 := sd_pm_faithful_eq initPM 8562 553 (by decide) sdw_pm_8562
  have hd := recon_intermediateGoal_5022_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5022
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5024 : ∀ n ∈ sm.nodes.drop 247, (5024 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8565 : ∀ n ∈ pm.nodes.drop 554, (8565 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8566 : ∀ n ∈ pm.nodes.drop 555, (8566 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5024_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5024
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5024 247 (by decide) sdw_sm_5024
  have hp0 := sd_pm_faithful_eq initPM 8565 554 (by decide) sdw_pm_8565
  have hp1 := sd_pm_faithful_eq initPM 8566 555 (by decide) sdw_pm_8566
  have hd := recon_intermediateGoal_5024_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5024
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5025 : ∀ n ∈ sm.nodes.drop 248, (5025 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8575 : ∀ n ∈ pm.nodes.drop 556, (8575 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8576 : ∀ n ∈ pm.nodes.drop 557, (8576 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5025_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5025
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5025 248 (by decide) sdw_sm_5025
  have hp0 := sd_pm_faithful_eq initPM 8575 556 (by decide) sdw_pm_8575
  have hp1 := sd_pm_faithful_eq initPM 8576 557 (by decide) sdw_pm_8576
  have hd := recon_intermediateGoal_5025_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5025
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5026 : ∀ n ∈ sm.nodes.drop 249, (5026 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8579 : ∀ n ∈ pm.nodes.drop 558, (8579 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8580 : ∀ n ∈ pm.nodes.drop 559, (8580 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5026_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5026
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5026 249 (by decide) sdw_sm_5026
  have hp0 := sd_pm_faithful_eq initPM 8579 558 (by decide) sdw_pm_8579
  have hp1 := sd_pm_faithful_eq initPM 8580 559 (by decide) sdw_pm_8580
  have hd := recon_intermediateGoal_5026_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5026
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5027 : ∀ n ∈ sm.nodes.drop 250, (5027 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8583 : ∀ n ∈ pm.nodes.drop 560, (8583 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8584 : ∀ n ∈ pm.nodes.drop 561, (8584 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5027_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5027
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5027 250 (by decide) sdw_sm_5027
  have hp0 := sd_pm_faithful_eq initPM 8583 560 (by decide) sdw_pm_8583
  have hp1 := sd_pm_faithful_eq initPM 8584 561 (by decide) sdw_pm_8584
  have hd := recon_intermediateGoal_5027_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5027
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5029 : ∀ n ∈ sm.nodes.drop 252, (5029 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8587 : ∀ n ∈ pm.nodes.drop 564, (8587 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8588 : ∀ n ∈ pm.nodes.drop 565, (8588 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5029_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5029
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5029 252 (by decide) sdw_sm_5029
  have hp0 := sd_pm_faithful_eq initPM 8587 564 (by decide) sdw_pm_8587
  have hp1 := sd_pm_faithful_eq initPM 8588 565 (by decide) sdw_pm_8588
  have hd := recon_intermediateGoal_5029_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5029
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5030 : ∀ n ∈ sm.nodes.drop 254, (5030 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8589 : ∀ n ∈ pm.nodes.drop 568, (8589 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8590 : ∀ n ∈ pm.nodes.drop 572, (8590 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5030_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5030
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5030 254 (by decide) sdw_sm_5030
  have hp0 := sd_pm_faithful_eq initPM 8589 568 (by decide) sdw_pm_8589
  have hp1 := sd_pm_faithful_eq initPM 8590 572 (by decide) sdw_pm_8590
  have hd := recon_intermediateGoal_5030_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5030
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5032 : ∀ n ∈ sm.nodes.drop 258, (5032 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8595 : ∀ n ∈ pm.nodes.drop 576, (8595 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8596 : ∀ n ∈ pm.nodes.drop 580, (8596 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5032_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5032
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5032 258 (by decide) sdw_sm_5032
  have hp0 := sd_pm_faithful_eq initPM 8595 576 (by decide) sdw_pm_8595
  have hp1 := sd_pm_faithful_eq initPM 8596 580 (by decide) sdw_pm_8596
  have hd := recon_intermediateGoal_5032_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5032
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5033 : ∀ n ∈ sm.nodes.drop 262, (5033 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8597 : ∀ n ∈ pm.nodes.drop 584, (8597 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8598 : ∀ n ∈ pm.nodes.drop 588, (8598 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5033_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5033
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5033 262 (by decide) sdw_sm_5033
  have hp0 := sd_pm_faithful_eq initPM 8597 584 (by decide) sdw_pm_8597
  have hp1 := sd_pm_faithful_eq initPM 8598 588 (by decide) sdw_pm_8598
  have hd := recon_intermediateGoal_5033_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5033
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5034 : ∀ n ∈ sm.nodes.drop 262, (5034 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8599 : ∀ n ∈ pm.nodes.drop 584, (8599 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8600 : ∀ n ∈ pm.nodes.drop 588, (8600 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5034_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5034
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5034 262 (by decide) sdw_sm_5034
  have hp0 := sd_pm_faithful_eq initPM 8599 584 (by decide) sdw_pm_8599
  have hp1 := sd_pm_faithful_eq initPM 8600 588 (by decide) sdw_pm_8600
  have hd := recon_intermediateGoal_5034_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5034
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5038 : ∀ n ∈ sm.nodes.drop 266, (5038 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8607 : ∀ n ∈ pm.nodes.drop 592, (8607 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8608 : ∀ n ∈ pm.nodes.drop 595, (8608 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5038_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5038
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5038 266 (by decide) sdw_sm_5038
  have hp0 := sd_pm_faithful_eq initPM 8607 592 (by decide) sdw_pm_8607
  have hp1 := sd_pm_faithful_eq initPM 8608 595 (by decide) sdw_pm_8608
  have hd := recon_intermediateGoal_5038_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5038
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5039 : ∀ n ∈ sm.nodes.drop 255, (5039 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8609 : ∀ n ∈ pm.nodes.drop 569, (8609 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8610 : ∀ n ∈ pm.nodes.drop 573, (8610 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5039_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5039
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5039 255 (by decide) sdw_sm_5039
  have hp0 := sd_pm_faithful_eq initPM 8609 569 (by decide) sdw_pm_8609
  have hp1 := sd_pm_faithful_eq initPM 8610 573 (by decide) sdw_pm_8610
  have hd := recon_intermediateGoal_5039_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5039
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5041 : ∀ n ∈ sm.nodes.drop 259, (5041 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8613 : ∀ n ∈ pm.nodes.drop 577, (8613 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8614 : ∀ n ∈ pm.nodes.drop 581, (8614 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5041_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5041
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5041 259 (by decide) sdw_sm_5041
  have hp0 := sd_pm_faithful_eq initPM 8613 577 (by decide) sdw_pm_8613
  have hp1 := sd_pm_faithful_eq initPM 8614 581 (by decide) sdw_pm_8614
  have hd := recon_intermediateGoal_5041_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5041
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5042 : ∀ n ∈ sm.nodes.drop 263, (5042 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8619 : ∀ n ∈ pm.nodes.drop 585, (8619 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8620 : ∀ n ∈ pm.nodes.drop 589, (8620 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5042_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5042
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5042 263 (by decide) sdw_sm_5042
  have hp0 := sd_pm_faithful_eq initPM 8619 585 (by decide) sdw_pm_8619
  have hp1 := sd_pm_faithful_eq initPM 8620 589 (by decide) sdw_pm_8620
  have hd := recon_intermediateGoal_5042_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5042
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5043 : ∀ n ∈ sm.nodes.drop 267, (5043 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8621 : ∀ n ∈ pm.nodes.drop 593, (8621 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8622 : ∀ n ∈ pm.nodes.drop 596, (8622 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5043_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5043
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5043 267 (by decide) sdw_sm_5043
  have hp0 := sd_pm_faithful_eq initPM 8621 593 (by decide) sdw_pm_8621
  have hp1 := sd_pm_faithful_eq initPM 8622 596 (by decide) sdw_pm_8622
  have hd := recon_intermediateGoal_5043_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5043
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5044 : ∀ n ∈ sm.nodes.drop 256, (5044 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8623 : ∀ n ∈ pm.nodes.drop 570, (8623 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8624 : ∀ n ∈ pm.nodes.drop 574, (8624 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5044_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5044
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5044 256 (by decide) sdw_sm_5044
  have hp0 := sd_pm_faithful_eq initPM 8623 570 (by decide) sdw_pm_8623
  have hp1 := sd_pm_faithful_eq initPM 8624 574 (by decide) sdw_pm_8624
  have hd := recon_intermediateGoal_5044_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5044
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5046 : ∀ n ∈ sm.nodes.drop 260, (5046 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8627 : ∀ n ∈ pm.nodes.drop 578, (8627 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8628 : ∀ n ∈ pm.nodes.drop 582, (8628 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5046_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5046
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5046 260 (by decide) sdw_sm_5046
  have hp0 := sd_pm_faithful_eq initPM 8627 578 (by decide) sdw_pm_8627
  have hp1 := sd_pm_faithful_eq initPM 8628 582 (by decide) sdw_pm_8628
  have hd := recon_intermediateGoal_5046_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5046
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5047 : ∀ n ∈ sm.nodes.drop 264, (5047 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8637 : ∀ n ∈ pm.nodes.drop 586, (8637 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8638 : ∀ n ∈ pm.nodes.drop 590, (8638 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5047_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5047
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5047 264 (by decide) sdw_sm_5047
  have hp0 := sd_pm_faithful_eq initPM 8637 586 (by decide) sdw_pm_8637
  have hp1 := sd_pm_faithful_eq initPM 8638 590 (by decide) sdw_pm_8638
  have hd := recon_intermediateGoal_5047_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5047
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5048 : ∀ n ∈ sm.nodes.drop 257, (5048 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8641 : ∀ n ∈ pm.nodes.drop 571, (8641 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8642 : ∀ n ∈ pm.nodes.drop 575, (8642 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5048_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5048
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5048 257 (by decide) sdw_sm_5048
  have hp0 := sd_pm_faithful_eq initPM 8641 571 (by decide) sdw_pm_8641
  have hp1 := sd_pm_faithful_eq initPM 8642 575 (by decide) sdw_pm_8642
  have hd := recon_intermediateGoal_5048_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5048
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5050 : ∀ n ∈ sm.nodes.drop 261, (5050 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8645 : ∀ n ∈ pm.nodes.drop 579, (8645 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8646 : ∀ n ∈ pm.nodes.drop 583, (8646 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5050_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5050
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5050 261 (by decide) sdw_sm_5050
  have hp0 := sd_pm_faithful_eq initPM 8645 579 (by decide) sdw_pm_8645
  have hp1 := sd_pm_faithful_eq initPM 8646 583 (by decide) sdw_pm_8646
  have hd := recon_intermediateGoal_5050_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5050
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5051 : ∀ n ∈ sm.nodes.drop 265, (5051 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8655 : ∀ n ∈ pm.nodes.drop 587, (8655 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8656 : ∀ n ∈ pm.nodes.drop 591, (8656 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5051_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5051
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5051 265 (by decide) sdw_sm_5051
  have hp0 := sd_pm_faithful_eq initPM 8655 587 (by decide) sdw_pm_8655
  have hp1 := sd_pm_faithful_eq initPM 8656 591 (by decide) sdw_pm_8656
  have hd := recon_intermediateGoal_5051_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5051
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5052 : ∀ n ∈ sm.nodes.drop 268, (5052 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8659 : ∀ n ∈ pm.nodes.drop 594, (8659 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8660 : ∀ n ∈ pm.nodes.drop 597, (8660 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5052_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5052
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5052 268 (by decide) sdw_sm_5052
  have hp0 := sd_pm_faithful_eq initPM 8659 594 (by decide) sdw_pm_8659
  have hp1 := sd_pm_faithful_eq initPM 8660 597 (by decide) sdw_pm_8660
  have hd := recon_intermediateGoal_5052_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5052
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5053 : ∀ n ∈ sm.nodes.drop 269, (5053 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8661 : ∀ n ∈ pm.nodes.drop 598, (8661 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8662 : ∀ n ∈ pm.nodes.drop 599, (8662 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5053_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5053
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5053 269 (by decide) sdw_sm_5053
  have hp0 := sd_pm_faithful_eq initPM 8661 598 (by decide) sdw_pm_8661
  have hp1 := sd_pm_faithful_eq initPM 8662 599 (by decide) sdw_pm_8662
  have hd := recon_intermediateGoal_5053_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5053
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5055 : ∀ n ∈ sm.nodes.drop 270, (5055 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8667 : ∀ n ∈ pm.nodes.drop 600, (8667 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8668 : ∀ n ∈ pm.nodes.drop 601, (8668 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5055_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5055
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5055 270 (by decide) sdw_sm_5055
  have hp0 := sd_pm_faithful_eq initPM 8667 600 (by decide) sdw_pm_8667
  have hp1 := sd_pm_faithful_eq initPM 8668 601 (by decide) sdw_pm_8668
  have hd := recon_intermediateGoal_5055_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5055
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5056 : ∀ n ∈ sm.nodes.drop 271, (5056 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8677 : ∀ n ∈ pm.nodes.drop 602, (8677 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8678 : ∀ n ∈ pm.nodes.drop 603, (8678 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5056_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5056
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5056 271 (by decide) sdw_sm_5056
  have hp0 := sd_pm_faithful_eq initPM 8677 602 (by decide) sdw_pm_8677
  have hp1 := sd_pm_faithful_eq initPM 8678 603 (by decide) sdw_pm_8678
  have hd := recon_intermediateGoal_5056_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5056
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5057 : ∀ n ∈ sm.nodes.drop 272, (5057 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8681 : ∀ n ∈ pm.nodes.drop 604, (8681 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8682 : ∀ n ∈ pm.nodes.drop 605, (8682 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5057_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5057
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5057 272 (by decide) sdw_sm_5057
  have hp0 := sd_pm_faithful_eq initPM 8681 604 (by decide) sdw_pm_8681
  have hp1 := sd_pm_faithful_eq initPM 8682 605 (by decide) sdw_pm_8682
  have hd := recon_intermediateGoal_5057_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5057
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5058 : ∀ n ∈ sm.nodes.drop 273, (5058 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8685 : ∀ n ∈ pm.nodes.drop 606, (8685 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8686 : ∀ n ∈ pm.nodes.drop 607, (8686 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5058_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5058
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5058 273 (by decide) sdw_sm_5058
  have hp0 := sd_pm_faithful_eq initPM 8685 606 (by decide) sdw_pm_8685
  have hp1 := sd_pm_faithful_eq initPM 8686 607 (by decide) sdw_pm_8686
  have hd := recon_intermediateGoal_5058_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5058
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5059 : ∀ n ∈ sm.nodes.drop 274, (5059 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8691 : ∀ n ∈ pm.nodes.drop 608, (8691 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8692 : ∀ n ∈ pm.nodes.drop 609, (8692 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5059_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5059
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5059 274 (by decide) sdw_sm_5059
  have hp0 := sd_pm_faithful_eq initPM 8691 608 (by decide) sdw_pm_8691
  have hp1 := sd_pm_faithful_eq initPM 8692 609 (by decide) sdw_pm_8692
  have hd := recon_intermediateGoal_5059_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5059
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5060 : ∀ n ∈ sm.nodes.drop 275, (5060 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8695 : ∀ n ∈ pm.nodes.drop 610, (8695 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8696 : ∀ n ∈ pm.nodes.drop 611, (8696 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5060_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5060
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5060 275 (by decide) sdw_sm_5060
  have hp0 := sd_pm_faithful_eq initPM 8695 610 (by decide) sdw_pm_8695
  have hp1 := sd_pm_faithful_eq initPM 8696 611 (by decide) sdw_pm_8696
  have hd := recon_intermediateGoal_5060_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5060
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7668 : ∀ n ∈ sm.nodes.drop 212, (7668 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15059 : ∀ n ∈ pm.nodes.drop 484, (15059 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15067 : ∀ n ∈ pm.nodes.drop 485, (15067 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7668_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7668
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7668 212 (by decide) sdw_sm_7668
  have hp0 := sd_pm_faithful_eq initPM 15059 484 (by decide) sdw_pm_15059
  have hp1 := sd_pm_faithful_eq initPM 15067 485 (by decide) sdw_pm_15067
  have hd := recon_intermediateGoal_7668_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7668
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7679 : ∀ n ∈ sm.nodes.drop 214, (7679 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15078 : ∀ n ∈ pm.nodes.drop 488, (15078 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15101 : ∀ n ∈ pm.nodes.drop 489, (15101 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7679_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7679
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7679 214 (by decide) sdw_sm_7679
  have hp0 := sd_pm_faithful_eq initPM 15078 488 (by decide) sdw_pm_15078
  have hp1 := sd_pm_faithful_eq initPM 15101 489 (by decide) sdw_pm_15101
  have hd := recon_intermediateGoal_7679_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7679
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7699 : ∀ n ∈ sm.nodes.drop 237, (7699 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15121 : ∀ n ∈ pm.nodes.drop 534, (15121 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15129 : ∀ n ∈ pm.nodes.drop 535, (15129 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7699_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7699
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7699 237 (by decide) sdw_sm_7699
  have hp0 := sd_pm_faithful_eq initPM 15121 534 (by decide) sdw_pm_15121
  have hp1 := sd_pm_faithful_eq initPM 15129 535 (by decide) sdw_pm_15129
  have hd := recon_intermediateGoal_7699_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7699
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7720 : ∀ n ∈ sm.nodes.drop 251, (7720 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15163 : ∀ n ∈ pm.nodes.drop 562, (15163 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15171 : ∀ n ∈ pm.nodes.drop 563, (15171 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7720_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7720
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7720 251 (by decide) sdw_sm_7720
  have hp0 := sd_pm_faithful_eq initPM 15163 562 (by decide) sdw_pm_15163
  have hp1 := sd_pm_faithful_eq initPM 15171 563 (by decide) sdw_pm_15171
  have hd := recon_intermediateGoal_7720_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7720
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7731 : ∀ n ∈ sm.nodes.drop 253, (7731 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15182 : ∀ n ∈ pm.nodes.drop 566, (15182 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15205 : ∀ n ∈ pm.nodes.drop 567, (15205 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7731_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7731
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7731 253 (by decide) sdw_sm_7731
  have hp0 := sd_pm_faithful_eq initPM 15182 566 (by decide) sdw_pm_15182
  have hp1 := sd_pm_faithful_eq initPM 15205 567 (by decide) sdw_pm_15205
  have hd := recon_intermediateGoal_7731_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7731
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
