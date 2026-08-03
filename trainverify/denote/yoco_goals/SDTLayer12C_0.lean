/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer12DistributedContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer12DistributedContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5278 : ∀ n ∈ sm.nodes.drop 433, (5278 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9443 : ∀ n ∈ pm.nodes.drop 926, (9443 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9444 : ∀ n ∈ pm.nodes.drop 927, (9444 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5278_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5278
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5278 433 (by decide) sdw_sm_5278
  have hp0 := sd_pm_faithful_eq initPM 9443 926 (by decide) sdw_pm_9443
  have hp1 := sd_pm_faithful_eq initPM 9444 927 (by decide) sdw_pm_9444
  have hd := recon_intermediateGoal_5278_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5278
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5280 : ∀ n ∈ sm.nodes.drop 435, (5280 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9445 : ∀ n ∈ pm.nodes.drop 930, (9445 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9446 : ∀ n ∈ pm.nodes.drop 933, (9446 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5280_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5280
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5280 435 (by decide) sdw_sm_5280
  have hp0 := sd_pm_faithful_eq initPM 9445 930 (by decide) sdw_pm_9445
  have hp1 := sd_pm_faithful_eq initPM 9446 933 (by decide) sdw_pm_9446
  have hd := recon_intermediateGoal_5280_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5280
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5282 : ∀ n ∈ sm.nodes.drop 436, (5282 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9457 : ∀ n ∈ pm.nodes.drop 931, (9457 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9458 : ∀ n ∈ pm.nodes.drop 934, (9458 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5282_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5282
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5282 436 (by decide) sdw_sm_5282
  have hp0 := sd_pm_faithful_eq initPM 9457 931 (by decide) sdw_pm_9457
  have hp1 := sd_pm_faithful_eq initPM 9458 934 (by decide) sdw_pm_9458
  have hd := recon_intermediateGoal_5282_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5282
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5284 : ∀ n ∈ sm.nodes.drop 437, (5284 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9467 : ∀ n ∈ pm.nodes.drop 932, (9467 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9468 : ∀ n ∈ pm.nodes.drop 935, (9468 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5284_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5284
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5284 437 (by decide) sdw_sm_5284
  have hp0 := sd_pm_faithful_eq initPM 9467 932 (by decide) sdw_pm_9467
  have hp1 := sd_pm_faithful_eq initPM 9468 935 (by decide) sdw_pm_9468
  have hd := recon_intermediateGoal_5284_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5284
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5286 : ∀ n ∈ sm.nodes.drop 438, (5286 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9479 : ∀ n ∈ pm.nodes.drop 936, (9479 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9480 : ∀ n ∈ pm.nodes.drop 937, (9480 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5286_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5286
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5286 438 (by decide) sdw_sm_5286
  have hp0 := sd_pm_faithful_eq initPM 9479 936 (by decide) sdw_pm_9479
  have hp1 := sd_pm_faithful_eq initPM 9480 937 (by decide) sdw_pm_9480
  have hd := recon_intermediateGoal_5286_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5286
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5287 : ∀ n ∈ sm.nodes.drop 438, (5287 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9481 : ∀ n ∈ pm.nodes.drop 936, (9481 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9482 : ∀ n ∈ pm.nodes.drop 937, (9482 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5287_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5287
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5287 438 (by decide) sdw_sm_5287
  have hp0 := sd_pm_faithful_eq initPM 9481 936 (by decide) sdw_pm_9481
  have hp1 := sd_pm_faithful_eq initPM 9482 937 (by decide) sdw_pm_9482
  have hd := recon_intermediateGoal_5287_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5287
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5290 : ∀ n ∈ sm.nodes.drop 439, (5290 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9483 : ∀ n ∈ pm.nodes.drop 938, (9483 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9484 : ∀ n ∈ pm.nodes.drop 939, (9484 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5290_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5290
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5290 439 (by decide) sdw_sm_5290
  have hp0 := sd_pm_faithful_eq initPM 9483 938 (by decide) sdw_pm_9483
  have hp1 := sd_pm_faithful_eq initPM 9484 939 (by decide) sdw_pm_9484
  have hd := recon_intermediateGoal_5290_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5290
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5291 : ∀ n ∈ sm.nodes.drop 440, (5291 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9485 : ∀ n ∈ pm.nodes.drop 940, (9485 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9486 : ∀ n ∈ pm.nodes.drop 941, (9486 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5291_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5291
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5291 440 (by decide) sdw_sm_5291
  have hp0 := sd_pm_faithful_eq initPM 9485 940 (by decide) sdw_pm_9485
  have hp1 := sd_pm_faithful_eq initPM 9486 941 (by decide) sdw_pm_9486
  have hd := recon_intermediateGoal_5291_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5291
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5292 : ∀ n ∈ sm.nodes.drop 441, (5292 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9491 : ∀ n ∈ pm.nodes.drop 942, (9491 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9492 : ∀ n ∈ pm.nodes.drop 943, (9492 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5292_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5292
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5292 441 (by decide) sdw_sm_5292
  have hp0 := sd_pm_faithful_eq initPM 9491 942 (by decide) sdw_pm_9491
  have hp1 := sd_pm_faithful_eq initPM 9492 943 (by decide) sdw_pm_9492
  have hd := recon_intermediateGoal_5292_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5292
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5294 : ∀ n ∈ sm.nodes.drop 442, (5294 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9495 : ∀ n ∈ pm.nodes.drop 944, (9495 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9496 : ∀ n ∈ pm.nodes.drop 945, (9496 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5294_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5294
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5294 442 (by decide) sdw_sm_5294
  have hp0 := sd_pm_faithful_eq initPM 9495 944 (by decide) sdw_pm_9495
  have hp1 := sd_pm_faithful_eq initPM 9496 945 (by decide) sdw_pm_9496
  have hd := recon_intermediateGoal_5294_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5294
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5295 : ∀ n ∈ sm.nodes.drop 443, (5295 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9505 : ∀ n ∈ pm.nodes.drop 946, (9505 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9506 : ∀ n ∈ pm.nodes.drop 947, (9506 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5295_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5295
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5295 443 (by decide) sdw_sm_5295
  have hp0 := sd_pm_faithful_eq initPM 9505 946 (by decide) sdw_pm_9505
  have hp1 := sd_pm_faithful_eq initPM 9506 947 (by decide) sdw_pm_9506
  have hd := recon_intermediateGoal_5295_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5295
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5296 : ∀ n ∈ sm.nodes.drop 444, (5296 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9509 : ∀ n ∈ pm.nodes.drop 948, (9509 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9510 : ∀ n ∈ pm.nodes.drop 949, (9510 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5296_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5296
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5296 444 (by decide) sdw_sm_5296
  have hp0 := sd_pm_faithful_eq initPM 9509 948 (by decide) sdw_pm_9509
  have hp1 := sd_pm_faithful_eq initPM 9510 949 (by decide) sdw_pm_9510
  have hd := recon_intermediateGoal_5296_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5296
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5297 : ∀ n ∈ sm.nodes.drop 445, (5297 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9513 : ∀ n ∈ pm.nodes.drop 950, (9513 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9514 : ∀ n ∈ pm.nodes.drop 951, (9514 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5297_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5297
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5297 445 (by decide) sdw_sm_5297
  have hp0 := sd_pm_faithful_eq initPM 9513 950 (by decide) sdw_pm_9513
  have hp1 := sd_pm_faithful_eq initPM 9514 951 (by decide) sdw_pm_9514
  have hd := recon_intermediateGoal_5297_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5297
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5299 : ∀ n ∈ sm.nodes.drop 447, (5299 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9517 : ∀ n ∈ pm.nodes.drop 954, (9517 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9518 : ∀ n ∈ pm.nodes.drop 955, (9518 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5299_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5299
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5299 447 (by decide) sdw_sm_5299
  have hp0 := sd_pm_faithful_eq initPM 9517 954 (by decide) sdw_pm_9517
  have hp1 := sd_pm_faithful_eq initPM 9518 955 (by decide) sdw_pm_9518
  have hd := recon_intermediateGoal_5299_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5299
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5300 : ∀ n ∈ sm.nodes.drop 449, (5300 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9519 : ∀ n ∈ pm.nodes.drop 958, (9519 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9520 : ∀ n ∈ pm.nodes.drop 962, (9520 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5300_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5300
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5300 449 (by decide) sdw_sm_5300
  have hp0 := sd_pm_faithful_eq initPM 9519 958 (by decide) sdw_pm_9519
  have hp1 := sd_pm_faithful_eq initPM 9520 962 (by decide) sdw_pm_9520
  have hd := recon_intermediateGoal_5300_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5300
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5302 : ∀ n ∈ sm.nodes.drop 453, (5302 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9525 : ∀ n ∈ pm.nodes.drop 966, (9525 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9526 : ∀ n ∈ pm.nodes.drop 970, (9526 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5302_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5302
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5302 453 (by decide) sdw_sm_5302
  have hp0 := sd_pm_faithful_eq initPM 9525 966 (by decide) sdw_pm_9525
  have hp1 := sd_pm_faithful_eq initPM 9526 970 (by decide) sdw_pm_9526
  have hd := recon_intermediateGoal_5302_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5302
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5303 : ∀ n ∈ sm.nodes.drop 457, (5303 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9527 : ∀ n ∈ pm.nodes.drop 974, (9527 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9528 : ∀ n ∈ pm.nodes.drop 978, (9528 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5303_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5303
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5303 457 (by decide) sdw_sm_5303
  have hp0 := sd_pm_faithful_eq initPM 9527 974 (by decide) sdw_pm_9527
  have hp1 := sd_pm_faithful_eq initPM 9528 978 (by decide) sdw_pm_9528
  have hd := recon_intermediateGoal_5303_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5303
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5304 : ∀ n ∈ sm.nodes.drop 457, (5304 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9529 : ∀ n ∈ pm.nodes.drop 974, (9529 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9530 : ∀ n ∈ pm.nodes.drop 978, (9530 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5304_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5304
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5304 457 (by decide) sdw_sm_5304
  have hp0 := sd_pm_faithful_eq initPM 9529 974 (by decide) sdw_pm_9529
  have hp1 := sd_pm_faithful_eq initPM 9530 978 (by decide) sdw_pm_9530
  have hd := recon_intermediateGoal_5304_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5304
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7959 : ∀ n ∈ sm.nodes.drop 432, (7959 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15641 : ∀ n ∈ pm.nodes.drop 924, (15641 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15649 : ∀ n ∈ pm.nodes.drop 925, (15649 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7959_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7959
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7959 432 (by decide) sdw_sm_7959
  have hp0 := sd_pm_faithful_eq initPM 15641 924 (by decide) sdw_pm_15641
  have hp1 := sd_pm_faithful_eq initPM 15649 925 (by decide) sdw_pm_15649
  have hd := recon_intermediateGoal_7959_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7959
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
