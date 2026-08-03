/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer2DistributedMigration

/-!
# Self-decoder goals transported to the faithful track

Batch 2 of the goals originally proved in `Layer2DistributedMigration.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4950 : ∀ n ∈ sm.nodes.drop 195, (4950 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8313 : ∀ n ∈ pm.nodes.drop 450, (8313 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8314 : ∀ n ∈ pm.nodes.drop 451, (8314 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4950_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4950
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4950 195 (by decide) sdw_sm_4950
  have hp0 := sd_pm_faithful_eq initPM 8313 450 (by decide) sdw_pm_8313
  have hp1 := sd_pm_faithful_eq initPM 8314 451 (by decide) sdw_pm_8314
  have hd := recon_intermediateGoal_4950_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4950
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4951 : ∀ n ∈ sm.nodes.drop 196, (4951 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8319 : ∀ n ∈ pm.nodes.drop 452, (8319 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8320 : ∀ n ∈ pm.nodes.drop 453, (8320 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4951_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4951
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4951 196 (by decide) sdw_sm_4951
  have hp0 := sd_pm_faithful_eq initPM 8319 452 (by decide) sdw_pm_8319
  have hp1 := sd_pm_faithful_eq initPM 8320 453 (by decide) sdw_pm_8320
  have hd := recon_intermediateGoal_4951_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4951
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4952 : ∀ n ∈ sm.nodes.drop 197, (4952 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8323 : ∀ n ∈ pm.nodes.drop 454, (8323 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8324 : ∀ n ∈ pm.nodes.drop 455, (8324 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4952_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4952
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4952 197 (by decide) sdw_sm_4952
  have hp0 := sd_pm_faithful_eq initPM 8323 454 (by decide) sdw_pm_8323
  have hp1 := sd_pm_faithful_eq initPM 8324 455 (by decide) sdw_pm_8324
  have hd := recon_intermediateGoal_4952_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4952
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4954 : ∀ n ∈ sm.nodes.drop 199, (4954 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8327 : ∀ n ∈ pm.nodes.drop 458, (8327 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8328 : ∀ n ∈ pm.nodes.drop 459, (8328 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4954_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4954
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4954 199 (by decide) sdw_sm_4954
  have hp0 := sd_pm_faithful_eq initPM 8327 458 (by decide) sdw_pm_8327
  have hp1 := sd_pm_faithful_eq initPM 8328 459 (by decide) sdw_pm_8328
  have hd := recon_intermediateGoal_4954_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4954
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4956 : ∀ n ∈ sm.nodes.drop 201, (4956 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8329 : ∀ n ∈ pm.nodes.drop 462, (8329 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8330 : ∀ n ∈ pm.nodes.drop 465, (8330 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4956_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4956
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4956 201 (by decide) sdw_sm_4956
  have hp0 := sd_pm_faithful_eq initPM 8329 462 (by decide) sdw_pm_8329
  have hp1 := sd_pm_faithful_eq initPM 8330 465 (by decide) sdw_pm_8330
  have hd := recon_intermediateGoal_4956_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4956
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4958 : ∀ n ∈ sm.nodes.drop 202, (4958 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8341 : ∀ n ∈ pm.nodes.drop 463, (8341 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8342 : ∀ n ∈ pm.nodes.drop 466, (8342 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4958_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4958
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4958 202 (by decide) sdw_sm_4958
  have hp0 := sd_pm_faithful_eq initPM 8341 463 (by decide) sdw_pm_8341
  have hp1 := sd_pm_faithful_eq initPM 8342 466 (by decide) sdw_pm_8342
  have hd := recon_intermediateGoal_4958_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4958
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4960 : ∀ n ∈ sm.nodes.drop 203, (4960 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8351 : ∀ n ∈ pm.nodes.drop 464, (8351 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8352 : ∀ n ∈ pm.nodes.drop 467, (8352 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4960_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4960
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4960 203 (by decide) sdw_sm_4960
  have hp0 := sd_pm_faithful_eq initPM 8351 464 (by decide) sdw_pm_8351
  have hp1 := sd_pm_faithful_eq initPM 8352 467 (by decide) sdw_pm_8352
  have hd := recon_intermediateGoal_4960_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4960
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4962 : ∀ n ∈ sm.nodes.drop 204, (4962 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8363 : ∀ n ∈ pm.nodes.drop 468, (8363 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8364 : ∀ n ∈ pm.nodes.drop 469, (8364 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4962_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4962
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4962 204 (by decide) sdw_sm_4962
  have hp0 := sd_pm_faithful_eq initPM 8363 468 (by decide) sdw_pm_8363
  have hp1 := sd_pm_faithful_eq initPM 8364 469 (by decide) sdw_pm_8364
  have hd := recon_intermediateGoal_4962_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4962
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4963 : ∀ n ∈ sm.nodes.drop 204, (4963 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8365 : ∀ n ∈ pm.nodes.drop 468, (8365 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8366 : ∀ n ∈ pm.nodes.drop 469, (8366 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4963_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4963
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4963 204 (by decide) sdw_sm_4963
  have hp0 := sd_pm_faithful_eq initPM 8365 468 (by decide) sdw_pm_8365
  have hp1 := sd_pm_faithful_eq initPM 8366 469 (by decide) sdw_pm_8366
  have hd := recon_intermediateGoal_4963_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4963
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4966 : ∀ n ∈ sm.nodes.drop 205, (4966 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8367 : ∀ n ∈ pm.nodes.drop 470, (8367 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8368 : ∀ n ∈ pm.nodes.drop 471, (8368 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4966_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4966
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4966 205 (by decide) sdw_sm_4966
  have hp0 := sd_pm_faithful_eq initPM 8367 470 (by decide) sdw_pm_8367
  have hp1 := sd_pm_faithful_eq initPM 8368 471 (by decide) sdw_pm_8368
  have hd := recon_intermediateGoal_4966_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4966
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4967 : ∀ n ∈ sm.nodes.drop 206, (4967 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8369 : ∀ n ∈ pm.nodes.drop 472, (8369 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8370 : ∀ n ∈ pm.nodes.drop 473, (8370 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4967_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4967
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4967 206 (by decide) sdw_sm_4967
  have hp0 := sd_pm_faithful_eq initPM 8369 472 (by decide) sdw_pm_8369
  have hp1 := sd_pm_faithful_eq initPM 8370 473 (by decide) sdw_pm_8370
  have hd := recon_intermediateGoal_4967_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4967
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4968 : ∀ n ∈ sm.nodes.drop 207, (4968 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8375 : ∀ n ∈ pm.nodes.drop 474, (8375 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8376 : ∀ n ∈ pm.nodes.drop 475, (8376 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4968_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4968
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4968 207 (by decide) sdw_sm_4968
  have hp0 := sd_pm_faithful_eq initPM 8375 474 (by decide) sdw_pm_8375
  have hp1 := sd_pm_faithful_eq initPM 8376 475 (by decide) sdw_pm_8376
  have hd := recon_intermediateGoal_4968_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4968
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4970 : ∀ n ∈ sm.nodes.drop 208, (4970 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8379 : ∀ n ∈ pm.nodes.drop 476, (8379 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8380 : ∀ n ∈ pm.nodes.drop 477, (8380 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4970_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4970
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4970 208 (by decide) sdw_sm_4970
  have hp0 := sd_pm_faithful_eq initPM 8379 476 (by decide) sdw_pm_8379
  have hp1 := sd_pm_faithful_eq initPM 8380 477 (by decide) sdw_pm_8380
  have hd := recon_intermediateGoal_4970_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4970
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4971 : ∀ n ∈ sm.nodes.drop 209, (4971 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8389 : ∀ n ∈ pm.nodes.drop 478, (8389 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8390 : ∀ n ∈ pm.nodes.drop 479, (8390 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4971_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4971
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4971 209 (by decide) sdw_sm_4971
  have hp0 := sd_pm_faithful_eq initPM 8389 478 (by decide) sdw_pm_8389
  have hp1 := sd_pm_faithful_eq initPM 8390 479 (by decide) sdw_pm_8390
  have hd := recon_intermediateGoal_4971_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4971
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4972 : ∀ n ∈ sm.nodes.drop 210, (4972 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8393 : ∀ n ∈ pm.nodes.drop 480, (8393 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8394 : ∀ n ∈ pm.nodes.drop 481, (8394 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4972_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4972
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4972 210 (by decide) sdw_sm_4972
  have hp0 := sd_pm_faithful_eq initPM 8393 480 (by decide) sdw_pm_8393
  have hp1 := sd_pm_faithful_eq initPM 8394 481 (by decide) sdw_pm_8394
  have hd := recon_intermediateGoal_4972_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4972
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4973 : ∀ n ∈ sm.nodes.drop 211, (4973 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8397 : ∀ n ∈ pm.nodes.drop 482, (8397 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8398 : ∀ n ∈ pm.nodes.drop 483, (8398 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4973_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4973
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4973 211 (by decide) sdw_sm_4973
  have hp0 := sd_pm_faithful_eq initPM 8397 482 (by decide) sdw_pm_8397
  have hp1 := sd_pm_faithful_eq initPM 8398 483 (by decide) sdw_pm_8398
  have hd := recon_intermediateGoal_4973_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4973
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4975 : ∀ n ∈ sm.nodes.drop 213, (4975 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8401 : ∀ n ∈ pm.nodes.drop 486, (8401 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8402 : ∀ n ∈ pm.nodes.drop 487, (8402 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4975_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4975
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4975 213 (by decide) sdw_sm_4975
  have hp0 := sd_pm_faithful_eq initPM 8401 486 (by decide) sdw_pm_8401
  have hp1 := sd_pm_faithful_eq initPM 8402 487 (by decide) sdw_pm_8402
  have hd := recon_intermediateGoal_4975_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4975
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4976 : ∀ n ∈ sm.nodes.drop 215, (4976 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8403 : ∀ n ∈ pm.nodes.drop 490, (8403 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8404 : ∀ n ∈ pm.nodes.drop 494, (8404 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4976_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4976
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4976 215 (by decide) sdw_sm_4976
  have hp0 := sd_pm_faithful_eq initPM 8403 490 (by decide) sdw_pm_8403
  have hp1 := sd_pm_faithful_eq initPM 8404 494 (by decide) sdw_pm_8404
  have hd := recon_intermediateGoal_4976_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4976
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4978 : ∀ n ∈ sm.nodes.drop 219, (4978 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8409 : ∀ n ∈ pm.nodes.drop 498, (8409 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8410 : ∀ n ∈ pm.nodes.drop 502, (8410 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4978_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4978
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4978 219 (by decide) sdw_sm_4978
  have hp0 := sd_pm_faithful_eq initPM 8409 498 (by decide) sdw_pm_8409
  have hp1 := sd_pm_faithful_eq initPM 8410 502 (by decide) sdw_pm_8410
  have hd := recon_intermediateGoal_4978_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4978
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4979 : ∀ n ∈ sm.nodes.drop 223, (4979 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8411 : ∀ n ∈ pm.nodes.drop 506, (8411 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8412 : ∀ n ∈ pm.nodes.drop 510, (8412 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4979_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4979
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4979 223 (by decide) sdw_sm_4979
  have hp0 := sd_pm_faithful_eq initPM 8411 506 (by decide) sdw_pm_8411
  have hp1 := sd_pm_faithful_eq initPM 8412 510 (by decide) sdw_pm_8412
  have hd := recon_intermediateGoal_4979_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4979
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4980 : ∀ n ∈ sm.nodes.drop 223, (4980 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8413 : ∀ n ∈ pm.nodes.drop 506, (8413 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8414 : ∀ n ∈ pm.nodes.drop 510, (8414 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4980_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4980
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4980 223 (by decide) sdw_sm_4980
  have hp0 := sd_pm_faithful_eq initPM 8413 506 (by decide) sdw_pm_8413
  have hp1 := sd_pm_faithful_eq initPM 8414 510 (by decide) sdw_pm_8414
  have hd := recon_intermediateGoal_4980_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4980
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4985 : ∀ n ∈ sm.nodes.drop 216, (4985 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8423 : ∀ n ∈ pm.nodes.drop 491, (8423 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8424 : ∀ n ∈ pm.nodes.drop 495, (8424 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4985_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4985
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4985 216 (by decide) sdw_sm_4985
  have hp0 := sd_pm_faithful_eq initPM 8423 491 (by decide) sdw_pm_8423
  have hp1 := sd_pm_faithful_eq initPM 8424 495 (by decide) sdw_pm_8424
  have hd := recon_intermediateGoal_4985_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4985
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4987 : ∀ n ∈ sm.nodes.drop 220, (4987 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8427 : ∀ n ∈ pm.nodes.drop 499, (8427 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8428 : ∀ n ∈ pm.nodes.drop 503, (8428 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4987_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4987
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4987 220 (by decide) sdw_sm_4987
  have hp0 := sd_pm_faithful_eq initPM 8427 499 (by decide) sdw_pm_8427
  have hp1 := sd_pm_faithful_eq initPM 8428 503 (by decide) sdw_pm_8428
  have hd := recon_intermediateGoal_4987_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4987
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4988 : ∀ n ∈ sm.nodes.drop 224, (4988 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8433 : ∀ n ∈ pm.nodes.drop 507, (8433 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8434 : ∀ n ∈ pm.nodes.drop 511, (8434 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4988_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4988
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4988 224 (by decide) sdw_sm_4988
  have hp0 := sd_pm_faithful_eq initPM 8433 507 (by decide) sdw_pm_8433
  have hp1 := sd_pm_faithful_eq initPM 8434 511 (by decide) sdw_pm_8434
  have hd := recon_intermediateGoal_4988_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4988
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4989 : ∀ n ∈ sm.nodes.drop 228, (4989 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8435 : ∀ n ∈ pm.nodes.drop 515, (8435 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8436 : ∀ n ∈ pm.nodes.drop 518, (8436 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4989_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4989
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4989 228 (by decide) sdw_sm_4989
  have hp0 := sd_pm_faithful_eq initPM 8435 515 (by decide) sdw_pm_8435
  have hp1 := sd_pm_faithful_eq initPM 8436 518 (by decide) sdw_pm_8436
  have hd := recon_intermediateGoal_4989_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4989
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4990 : ∀ n ∈ sm.nodes.drop 217, (4990 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8437 : ∀ n ∈ pm.nodes.drop 492, (8437 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8438 : ∀ n ∈ pm.nodes.drop 496, (8438 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4990_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4990
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4990 217 (by decide) sdw_sm_4990
  have hp0 := sd_pm_faithful_eq initPM 8437 492 (by decide) sdw_pm_8437
  have hp1 := sd_pm_faithful_eq initPM 8438 496 (by decide) sdw_pm_8438
  have hd := recon_intermediateGoal_4990_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4990
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4992 : ∀ n ∈ sm.nodes.drop 221, (4992 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8441 : ∀ n ∈ pm.nodes.drop 500, (8441 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8442 : ∀ n ∈ pm.nodes.drop 504, (8442 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4992_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4992
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4992 221 (by decide) sdw_sm_4992
  have hp0 := sd_pm_faithful_eq initPM 8441 500 (by decide) sdw_pm_8441
  have hp1 := sd_pm_faithful_eq initPM 8442 504 (by decide) sdw_pm_8442
  have hd := recon_intermediateGoal_4992_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4992
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4993 : ∀ n ∈ sm.nodes.drop 225, (4993 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8451 : ∀ n ∈ pm.nodes.drop 508, (8451 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8452 : ∀ n ∈ pm.nodes.drop 512, (8452 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4993_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4993
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4993 225 (by decide) sdw_sm_4993
  have hp0 := sd_pm_faithful_eq initPM 8451 508 (by decide) sdw_pm_8451
  have hp1 := sd_pm_faithful_eq initPM 8452 512 (by decide) sdw_pm_8452
  have hd := recon_intermediateGoal_4993_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4993
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4994 : ∀ n ∈ sm.nodes.drop 218, (4994 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8455 : ∀ n ∈ pm.nodes.drop 493, (8455 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8456 : ∀ n ∈ pm.nodes.drop 497, (8456 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4994_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4994
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4994 218 (by decide) sdw_sm_4994
  have hp0 := sd_pm_faithful_eq initPM 8455 493 (by decide) sdw_pm_8455
  have hp1 := sd_pm_faithful_eq initPM 8456 497 (by decide) sdw_pm_8456
  have hd := recon_intermediateGoal_4994_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4994
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4996 : ∀ n ∈ sm.nodes.drop 222, (4996 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8459 : ∀ n ∈ pm.nodes.drop 501, (8459 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8460 : ∀ n ∈ pm.nodes.drop 505, (8460 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4996_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4996
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4996 222 (by decide) sdw_sm_4996
  have hp0 := sd_pm_faithful_eq initPM 8459 501 (by decide) sdw_pm_8459
  have hp1 := sd_pm_faithful_eq initPM 8460 505 (by decide) sdw_pm_8460
  have hd := recon_intermediateGoal_4996_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4996
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4997 : ∀ n ∈ sm.nodes.drop 226, (4997 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8469 : ∀ n ∈ pm.nodes.drop 509, (8469 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8470 : ∀ n ∈ pm.nodes.drop 513, (8470 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4997_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4997
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4997 226 (by decide) sdw_sm_4997
  have hp0 := sd_pm_faithful_eq initPM 8469 509 (by decide) sdw_pm_8469
  have hp1 := sd_pm_faithful_eq initPM 8470 513 (by decide) sdw_pm_8470
  have hd := recon_intermediateGoal_4997_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4997
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4998 : ∀ n ∈ sm.nodes.drop 229, (4998 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8473 : ∀ n ∈ pm.nodes.drop 516, (8473 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8474 : ∀ n ∈ pm.nodes.drop 519, (8474 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4998_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4998
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4998 229 (by decide) sdw_sm_4998
  have hp0 := sd_pm_faithful_eq initPM 8473 516 (by decide) sdw_pm_8473
  have hp1 := sd_pm_faithful_eq initPM 8474 519 (by decide) sdw_pm_8474
  have hd := recon_intermediateGoal_4998_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4998
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4999 : ∀ n ∈ sm.nodes.drop 230, (4999 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8475 : ∀ n ∈ pm.nodes.drop 520, (8475 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8476 : ∀ n ∈ pm.nodes.drop 521, (8476 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4999_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4999
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4999 230 (by decide) sdw_sm_4999
  have hp0 := sd_pm_faithful_eq initPM 8475 520 (by decide) sdw_pm_8475
  have hp1 := sd_pm_faithful_eq initPM 8476 521 (by decide) sdw_pm_8476
  have hd := recon_intermediateGoal_4999_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4999
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5001 : ∀ n ∈ sm.nodes.drop 231, (5001 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8481 : ∀ n ∈ pm.nodes.drop 522, (8481 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8482 : ∀ n ∈ pm.nodes.drop 523, (8482 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5001_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5001
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5001 231 (by decide) sdw_sm_5001
  have hp0 := sd_pm_faithful_eq initPM 8481 522 (by decide) sdw_pm_8481
  have hp1 := sd_pm_faithful_eq initPM 8482 523 (by decide) sdw_pm_8482
  have hd := recon_intermediateGoal_5001_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5001
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5002 : ∀ n ∈ sm.nodes.drop 232, (5002 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8491 : ∀ n ∈ pm.nodes.drop 524, (8491 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8492 : ∀ n ∈ pm.nodes.drop 525, (8492 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5002_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5002
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5002 232 (by decide) sdw_sm_5002
  have hp0 := sd_pm_faithful_eq initPM 8491 524 (by decide) sdw_pm_8491
  have hp1 := sd_pm_faithful_eq initPM 8492 525 (by decide) sdw_pm_8492
  have hd := recon_intermediateGoal_5002_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5002
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5003 : ∀ n ∈ sm.nodes.drop 233, (5003 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8495 : ∀ n ∈ pm.nodes.drop 526, (8495 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8496 : ∀ n ∈ pm.nodes.drop 527, (8496 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5003_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5003
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5003 233 (by decide) sdw_sm_5003
  have hp0 := sd_pm_faithful_eq initPM 8495 526 (by decide) sdw_pm_8495
  have hp1 := sd_pm_faithful_eq initPM 8496 527 (by decide) sdw_pm_8496
  have hd := recon_intermediateGoal_5003_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5003
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7491 : ∀ n ∈ sm.nodes.drop 81, (7491 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14705 : ∀ n ∈ pm.nodes.drop 222, (14705 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14713 : ∀ n ∈ pm.nodes.drop 223, (14713 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7491_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7491
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7491 81 (by decide) sdw_sm_7491
  have hp0 := sd_pm_faithful_eq initPM 14705 222 (by decide) sdw_pm_14705
  have hp1 := sd_pm_faithful_eq initPM 14713 223 (by decide) sdw_pm_14713
  have hd := recon_intermediateGoal_7491_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7491
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7512 : ∀ n ∈ sm.nodes.drop 95, (7512 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14747 : ∀ n ∈ pm.nodes.drop 250, (14747 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14755 : ∀ n ∈ pm.nodes.drop 251, (14755 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7512_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7512
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7512 95 (by decide) sdw_sm_7512
  have hp0 := sd_pm_faithful_eq initPM 14747 250 (by decide) sdw_pm_14747
  have hp1 := sd_pm_faithful_eq initPM 14755 251 (by decide) sdw_pm_14755
  have hd := recon_intermediateGoal_7512_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7512
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7523 : ∀ n ∈ sm.nodes.drop 97, (7523 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14766 : ∀ n ∈ pm.nodes.drop 254, (14766 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14789 : ∀ n ∈ pm.nodes.drop 255, (14789 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7523_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7523
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7523 97 (by decide) sdw_sm_7523
  have hp0 := sd_pm_faithful_eq initPM 14766 254 (by decide) sdw_pm_14766
  have hp1 := sd_pm_faithful_eq initPM 14789 255 (by decide) sdw_pm_14789
  have hd := recon_intermediateGoal_7523_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7523
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7543 : ∀ n ∈ sm.nodes.drop 120, (7543 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14809 : ∀ n ∈ pm.nodes.drop 300, (14809 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14817 : ∀ n ∈ pm.nodes.drop 301, (14817 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7543_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7543
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7543 120 (by decide) sdw_sm_7543
  have hp0 := sd_pm_faithful_eq initPM 14809 300 (by decide) sdw_pm_14809
  have hp1 := sd_pm_faithful_eq initPM 14817 301 (by decide) sdw_pm_14817
  have hd := recon_intermediateGoal_7543_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7543
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7564 : ∀ n ∈ sm.nodes.drop 134, (7564 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14851 : ∀ n ∈ pm.nodes.drop 328, (14851 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14859 : ∀ n ∈ pm.nodes.drop 329, (14859 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7564_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7564
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7564 134 (by decide) sdw_sm_7564
  have hp0 := sd_pm_faithful_eq initPM 14851 328 (by decide) sdw_pm_14851
  have hp1 := sd_pm_faithful_eq initPM 14859 329 (by decide) sdw_pm_14859
  have hd := recon_intermediateGoal_7564_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7564
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7575 : ∀ n ∈ sm.nodes.drop 136, (7575 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14870 : ∀ n ∈ pm.nodes.drop 332, (14870 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14893 : ∀ n ∈ pm.nodes.drop 333, (14893 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7575_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7575
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7575 136 (by decide) sdw_sm_7575
  have hp0 := sd_pm_faithful_eq initPM 14870 332 (by decide) sdw_pm_14870
  have hp1 := sd_pm_faithful_eq initPM 14893 333 (by decide) sdw_pm_14893
  have hd := recon_intermediateGoal_7575_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7575
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7595 : ∀ n ∈ sm.nodes.drop 159, (7595 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14913 : ∀ n ∈ pm.nodes.drop 378, (14913 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14921 : ∀ n ∈ pm.nodes.drop 379, (14921 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7595_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7595
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7595 159 (by decide) sdw_sm_7595
  have hp0 := sd_pm_faithful_eq initPM 14913 378 (by decide) sdw_pm_14913
  have hp1 := sd_pm_faithful_eq initPM 14921 379 (by decide) sdw_pm_14921
  have hd := recon_intermediateGoal_7595_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7595
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7616 : ∀ n ∈ sm.nodes.drop 173, (7616 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14955 : ∀ n ∈ pm.nodes.drop 406, (14955 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14963 : ∀ n ∈ pm.nodes.drop 407, (14963 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7616_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7616
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7616 173 (by decide) sdw_sm_7616
  have hp0 := sd_pm_faithful_eq initPM 14955 406 (by decide) sdw_pm_14955
  have hp1 := sd_pm_faithful_eq initPM 14963 407 (by decide) sdw_pm_14963
  have hd := recon_intermediateGoal_7616_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7616
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7627 : ∀ n ∈ sm.nodes.drop 175, (7627 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14974 : ∀ n ∈ pm.nodes.drop 410, (14974 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_14997 : ∀ n ∈ pm.nodes.drop 411, (14997 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7627_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7627
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7627 175 (by decide) sdw_sm_7627
  have hp0 := sd_pm_faithful_eq initPM 14974 410 (by decide) sdw_pm_14974
  have hp1 := sd_pm_faithful_eq initPM 14997 411 (by decide) sdw_pm_14997
  have hd := recon_intermediateGoal_7627_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7627
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7647 : ∀ n ∈ sm.nodes.drop 198, (7647 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15017 : ∀ n ∈ pm.nodes.drop 456, (15017 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15025 : ∀ n ∈ pm.nodes.drop 457, (15025 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7647_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7647
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7647 198 (by decide) sdw_sm_7647
  have hp0 := sd_pm_faithful_eq initPM 15017 456 (by decide) sdw_pm_15017
  have hp1 := sd_pm_faithful_eq initPM 15025 457 (by decide) sdw_pm_15025
  have hd := recon_intermediateGoal_7647_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7647
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
