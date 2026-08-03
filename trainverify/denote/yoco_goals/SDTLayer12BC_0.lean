/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer12DistributedBoundaryContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer12DistributedBoundaryContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5308 : ∀ n ∈ sm.nodes.drop 461, (5308 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9537 : ∀ n ∈ pm.nodes.drop 982, (9537 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9538 : ∀ n ∈ pm.nodes.drop 985, (9538 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5308_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5308
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5308 461 (by decide) sdw_sm_5308
  have hp0 := sd_pm_faithful_eq initPM 9537 982 (by decide) sdw_pm_9537
  have hp1 := sd_pm_faithful_eq initPM 9538 985 (by decide) sdw_pm_9538
  have hd := recon_intermediateGoal_5308_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5308
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5309 : ∀ n ∈ sm.nodes.drop 450, (5309 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9539 : ∀ n ∈ pm.nodes.drop 959, (9539 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9540 : ∀ n ∈ pm.nodes.drop 963, (9540 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5309_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5309
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5309 450 (by decide) sdw_sm_5309
  have hp0 := sd_pm_faithful_eq initPM 9539 959 (by decide) sdw_pm_9539
  have hp1 := sd_pm_faithful_eq initPM 9540 963 (by decide) sdw_pm_9540
  have hd := recon_intermediateGoal_5309_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5309
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5311 : ∀ n ∈ sm.nodes.drop 454, (5311 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9543 : ∀ n ∈ pm.nodes.drop 967, (9543 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9544 : ∀ n ∈ pm.nodes.drop 971, (9544 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5311_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5311
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5311 454 (by decide) sdw_sm_5311
  have hp0 := sd_pm_faithful_eq initPM 9543 967 (by decide) sdw_pm_9543
  have hp1 := sd_pm_faithful_eq initPM 9544 971 (by decide) sdw_pm_9544
  have hd := recon_intermediateGoal_5311_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5311
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5312 : ∀ n ∈ sm.nodes.drop 458, (5312 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9549 : ∀ n ∈ pm.nodes.drop 975, (9549 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9550 : ∀ n ∈ pm.nodes.drop 979, (9550 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5312_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5312
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5312 458 (by decide) sdw_sm_5312
  have hp0 := sd_pm_faithful_eq initPM 9549 975 (by decide) sdw_pm_9549
  have hp1 := sd_pm_faithful_eq initPM 9550 979 (by decide) sdw_pm_9550
  have hd := recon_intermediateGoal_5312_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5312
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5313 : ∀ n ∈ sm.nodes.drop 462, (5313 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9551 : ∀ n ∈ pm.nodes.drop 983, (9551 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9552 : ∀ n ∈ pm.nodes.drop 986, (9552 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5313_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5313
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5313 462 (by decide) sdw_sm_5313
  have hp0 := sd_pm_faithful_eq initPM 9551 983 (by decide) sdw_pm_9551
  have hp1 := sd_pm_faithful_eq initPM 9552 986 (by decide) sdw_pm_9552
  have hd := recon_intermediateGoal_5313_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5313
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5314 : ∀ n ∈ sm.nodes.drop 451, (5314 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9553 : ∀ n ∈ pm.nodes.drop 960, (9553 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9554 : ∀ n ∈ pm.nodes.drop 964, (9554 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5314_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5314
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5314 451 (by decide) sdw_sm_5314
  have hp0 := sd_pm_faithful_eq initPM 9553 960 (by decide) sdw_pm_9553
  have hp1 := sd_pm_faithful_eq initPM 9554 964 (by decide) sdw_pm_9554
  have hd := recon_intermediateGoal_5314_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5314
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5316 : ∀ n ∈ sm.nodes.drop 455, (5316 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9557 : ∀ n ∈ pm.nodes.drop 968, (9557 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9558 : ∀ n ∈ pm.nodes.drop 972, (9558 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5316_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5316
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5316 455 (by decide) sdw_sm_5316
  have hp0 := sd_pm_faithful_eq initPM 9557 968 (by decide) sdw_pm_9557
  have hp1 := sd_pm_faithful_eq initPM 9558 972 (by decide) sdw_pm_9558
  have hd := recon_intermediateGoal_5316_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5316
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5317 : ∀ n ∈ sm.nodes.drop 459, (5317 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9567 : ∀ n ∈ pm.nodes.drop 976, (9567 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9568 : ∀ n ∈ pm.nodes.drop 980, (9568 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5317_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5317
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5317 459 (by decide) sdw_sm_5317
  have hp0 := sd_pm_faithful_eq initPM 9567 976 (by decide) sdw_pm_9567
  have hp1 := sd_pm_faithful_eq initPM 9568 980 (by decide) sdw_pm_9568
  have hd := recon_intermediateGoal_5317_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5317
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5318 : ∀ n ∈ sm.nodes.drop 452, (5318 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9571 : ∀ n ∈ pm.nodes.drop 961, (9571 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9572 : ∀ n ∈ pm.nodes.drop 965, (9572 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5318_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5318
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5318 452 (by decide) sdw_sm_5318
  have hp0 := sd_pm_faithful_eq initPM 9571 961 (by decide) sdw_pm_9571
  have hp1 := sd_pm_faithful_eq initPM 9572 965 (by decide) sdw_pm_9572
  have hd := recon_intermediateGoal_5318_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5318
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5320 : ∀ n ∈ sm.nodes.drop 456, (5320 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9575 : ∀ n ∈ pm.nodes.drop 969, (9575 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9576 : ∀ n ∈ pm.nodes.drop 973, (9576 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5320_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5320
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5320 456 (by decide) sdw_sm_5320
  have hp0 := sd_pm_faithful_eq initPM 9575 969 (by decide) sdw_pm_9575
  have hp1 := sd_pm_faithful_eq initPM 9576 973 (by decide) sdw_pm_9576
  have hd := recon_intermediateGoal_5320_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5320
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5321 : ∀ n ∈ sm.nodes.drop 460, (5321 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9585 : ∀ n ∈ pm.nodes.drop 977, (9585 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9586 : ∀ n ∈ pm.nodes.drop 981, (9586 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5321_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5321
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5321 460 (by decide) sdw_sm_5321
  have hp0 := sd_pm_faithful_eq initPM 9585 977 (by decide) sdw_pm_9585
  have hp1 := sd_pm_faithful_eq initPM 9586 981 (by decide) sdw_pm_9586
  have hd := recon_intermediateGoal_5321_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5321
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5322 : ∀ n ∈ sm.nodes.drop 463, (5322 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9589 : ∀ n ∈ pm.nodes.drop 984, (9589 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9590 : ∀ n ∈ pm.nodes.drop 987, (9590 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5322_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5322
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5322 463 (by decide) sdw_sm_5322
  have hp0 := sd_pm_faithful_eq initPM 9589 984 (by decide) sdw_pm_9589
  have hp1 := sd_pm_faithful_eq initPM 9590 987 (by decide) sdw_pm_9590
  have hd := recon_intermediateGoal_5322_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5322
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5323 : ∀ n ∈ sm.nodes.drop 464, (5323 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9591 : ∀ n ∈ pm.nodes.drop 988, (9591 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9592 : ∀ n ∈ pm.nodes.drop 989, (9592 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5323_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5323
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5323 464 (by decide) sdw_sm_5323
  have hp0 := sd_pm_faithful_eq initPM 9591 988 (by decide) sdw_pm_9591
  have hp1 := sd_pm_faithful_eq initPM 9592 989 (by decide) sdw_pm_9592
  have hd := recon_intermediateGoal_5323_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5323
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5325 : ∀ n ∈ sm.nodes.drop 465, (5325 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9597 : ∀ n ∈ pm.nodes.drop 990, (9597 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9598 : ∀ n ∈ pm.nodes.drop 991, (9598 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5325_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5325
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5325 465 (by decide) sdw_sm_5325
  have hp0 := sd_pm_faithful_eq initPM 9597 990 (by decide) sdw_pm_9597
  have hp1 := sd_pm_faithful_eq initPM 9598 991 (by decide) sdw_pm_9598
  have hd := recon_intermediateGoal_5325_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5325
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5326 : ∀ n ∈ sm.nodes.drop 466, (5326 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9607 : ∀ n ∈ pm.nodes.drop 992, (9607 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9608 : ∀ n ∈ pm.nodes.drop 993, (9608 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5326_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5326
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5326 466 (by decide) sdw_sm_5326
  have hp0 := sd_pm_faithful_eq initPM 9607 992 (by decide) sdw_pm_9607
  have hp1 := sd_pm_faithful_eq initPM 9608 993 (by decide) sdw_pm_9608
  have hd := recon_intermediateGoal_5326_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5326
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5327 : ∀ n ∈ sm.nodes.drop 467, (5327 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9611 : ∀ n ∈ pm.nodes.drop 994, (9611 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9612 : ∀ n ∈ pm.nodes.drop 995, (9612 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5327_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5327
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5327 467 (by decide) sdw_sm_5327
  have hp0 := sd_pm_faithful_eq initPM 9611 994 (by decide) sdw_pm_9611
  have hp1 := sd_pm_faithful_eq initPM 9612 995 (by decide) sdw_pm_9612
  have hd := recon_intermediateGoal_5327_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5327
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5328 : ∀ n ∈ sm.nodes.drop 468, (5328 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9615 : ∀ n ∈ pm.nodes.drop 996, (9615 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9616 : ∀ n ∈ pm.nodes.drop 997, (9616 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5328_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5328
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5328 468 (by decide) sdw_sm_5328
  have hp0 := sd_pm_faithful_eq initPM 9615 996 (by decide) sdw_pm_9615
  have hp1 := sd_pm_faithful_eq initPM 9616 997 (by decide) sdw_pm_9616
  have hd := recon_intermediateGoal_5328_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5328
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5329 : ∀ n ∈ sm.nodes.drop 469, (5329 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9621 : ∀ n ∈ pm.nodes.drop 998, (9621 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9622 : ∀ n ∈ pm.nodes.drop 999, (9622 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5329_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5329
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5329 469 (by decide) sdw_sm_5329
  have hp0 := sd_pm_faithful_eq initPM 9621 998 (by decide) sdw_pm_9621
  have hp1 := sd_pm_faithful_eq initPM 9622 999 (by decide) sdw_pm_9622
  have hd := recon_intermediateGoal_5329_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5329
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5330 : ∀ n ∈ sm.nodes.drop 470, (5330 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9625 : ∀ n ∈ pm.nodes.drop 1000, (9625 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9626 : ∀ n ∈ pm.nodes.drop 1001, (9626 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5330_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5330
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5330 470 (by decide) sdw_sm_5330
  have hp0 := sd_pm_faithful_eq initPM 9625 1000 (by decide) sdw_pm_9625
  have hp1 := sd_pm_faithful_eq initPM 9626 1001 (by decide) sdw_pm_9626
  have hd := recon_intermediateGoal_5330_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5330
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7980 : ∀ n ∈ sm.nodes.drop 446, (7980 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15683 : ∀ n ∈ pm.nodes.drop 952, (15683 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15691 : ∀ n ∈ pm.nodes.drop 953, (15691 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7980_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7980
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7980 446 (by decide) sdw_sm_7980
  have hp0 := sd_pm_faithful_eq initPM 15683 952 (by decide) sdw_pm_15683
  have hp1 := sd_pm_faithful_eq initPM 15691 953 (by decide) sdw_pm_15691
  have hd := recon_intermediateGoal_7980_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7980
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7991 : ∀ n ∈ sm.nodes.drop 448, (7991 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15702 : ∀ n ∈ pm.nodes.drop 956, (15702 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15725 : ∀ n ∈ pm.nodes.drop 957, (15725 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7991_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7991
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7991 448 (by decide) sdw_sm_7991
  have hp0 := sd_pm_faithful_eq initPM 15702 956 (by decide) sdw_pm_15702
  have hp1 := sd_pm_faithful_eq initPM 15725 957 (by decide) sdw_pm_15725
  have hd := recon_intermediateGoal_7991_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7991
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
