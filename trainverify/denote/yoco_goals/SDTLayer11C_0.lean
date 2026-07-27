/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer11DistributedContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer11DistributedContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5237 : ∀ n ∈ sm.nodes.drop 401, (5237 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9299 : ∀ n ∈ pm.nodes.drop 862, (9299 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9300 : ∀ n ∈ pm.nodes.drop 863, (9300 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5237_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5237
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5237 401 (by decide) sdw_sm_5237
  have hp0 := sd_pm_faithful_eq initPM 9299 862 (by decide) sdw_pm_9299
  have hp1 := sd_pm_faithful_eq initPM 9300 863 (by decide) sdw_pm_9300
  have hd := recon_intermediateGoal_5237_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5237, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5238 : ∀ n ∈ sm.nodes.drop 402, (5238 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9305 : ∀ n ∈ pm.nodes.drop 864, (9305 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9306 : ∀ n ∈ pm.nodes.drop 865, (9306 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5238_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5238
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5238 402 (by decide) sdw_sm_5238
  have hp0 := sd_pm_faithful_eq initPM 9305 864 (by decide) sdw_pm_9305
  have hp1 := sd_pm_faithful_eq initPM 9306 865 (by decide) sdw_pm_9306
  have hd := recon_intermediateGoal_5238_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5238, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5240 : ∀ n ∈ sm.nodes.drop 403, (5240 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9309 : ∀ n ∈ pm.nodes.drop 866, (9309 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9310 : ∀ n ∈ pm.nodes.drop 867, (9310 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5240_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5240
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5240 403 (by decide) sdw_sm_5240
  have hp0 := sd_pm_faithful_eq initPM 9309 866 (by decide) sdw_pm_9309
  have hp1 := sd_pm_faithful_eq initPM 9310 867 (by decide) sdw_pm_9310
  have hd := recon_intermediateGoal_5240_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5240, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5241 : ∀ n ∈ sm.nodes.drop 404, (5241 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9319 : ∀ n ∈ pm.nodes.drop 868, (9319 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9320 : ∀ n ∈ pm.nodes.drop 869, (9320 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5241_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5241
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5241 404 (by decide) sdw_sm_5241
  have hp0 := sd_pm_faithful_eq initPM 9319 868 (by decide) sdw_pm_9319
  have hp1 := sd_pm_faithful_eq initPM 9320 869 (by decide) sdw_pm_9320
  have hd := recon_intermediateGoal_5241_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5241, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5242 : ∀ n ∈ sm.nodes.drop 405, (5242 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9323 : ∀ n ∈ pm.nodes.drop 870, (9323 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9324 : ∀ n ∈ pm.nodes.drop 871, (9324 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5242_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5242
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5242 405 (by decide) sdw_sm_5242
  have hp0 := sd_pm_faithful_eq initPM 9323 870 (by decide) sdw_pm_9323
  have hp1 := sd_pm_faithful_eq initPM 9324 871 (by decide) sdw_pm_9324
  have hd := recon_intermediateGoal_5242_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5242, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5243 : ∀ n ∈ sm.nodes.drop 406, (5243 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9327 : ∀ n ∈ pm.nodes.drop 872, (9327 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9328 : ∀ n ∈ pm.nodes.drop 873, (9328 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5243_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5243
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5243 406 (by decide) sdw_sm_5243
  have hp0 := sd_pm_faithful_eq initPM 9327 872 (by decide) sdw_pm_9327
  have hp1 := sd_pm_faithful_eq initPM 9328 873 (by decide) sdw_pm_9328
  have hd := recon_intermediateGoal_5243_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5243, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5245 : ∀ n ∈ sm.nodes.drop 408, (5245 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9331 : ∀ n ∈ pm.nodes.drop 876, (9331 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9332 : ∀ n ∈ pm.nodes.drop 877, (9332 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5245_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5245
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5245 408 (by decide) sdw_sm_5245
  have hp0 := sd_pm_faithful_eq initPM 9331 876 (by decide) sdw_pm_9331
  have hp1 := sd_pm_faithful_eq initPM 9332 877 (by decide) sdw_pm_9332
  have hd := recon_intermediateGoal_5245_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5245, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5246 : ∀ n ∈ sm.nodes.drop 410, (5246 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9333 : ∀ n ∈ pm.nodes.drop 880, (9333 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9334 : ∀ n ∈ pm.nodes.drop 884, (9334 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5246_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5246
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5246 410 (by decide) sdw_sm_5246
  have hp0 := sd_pm_faithful_eq initPM 9333 880 (by decide) sdw_pm_9333
  have hp1 := sd_pm_faithful_eq initPM 9334 884 (by decide) sdw_pm_9334
  have hd := recon_intermediateGoal_5246_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5246, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5248 : ∀ n ∈ sm.nodes.drop 414, (5248 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9339 : ∀ n ∈ pm.nodes.drop 888, (9339 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9340 : ∀ n ∈ pm.nodes.drop 892, (9340 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5248_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5248
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5248 414 (by decide) sdw_sm_5248
  have hp0 := sd_pm_faithful_eq initPM 9339 888 (by decide) sdw_pm_9339
  have hp1 := sd_pm_faithful_eq initPM 9340 892 (by decide) sdw_pm_9340
  have hd := recon_intermediateGoal_5248_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5248, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5249 : ∀ n ∈ sm.nodes.drop 418, (5249 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9341 : ∀ n ∈ pm.nodes.drop 896, (9341 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9342 : ∀ n ∈ pm.nodes.drop 900, (9342 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5249_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5249
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5249 418 (by decide) sdw_sm_5249
  have hp0 := sd_pm_faithful_eq initPM 9341 896 (by decide) sdw_pm_9341
  have hp1 := sd_pm_faithful_eq initPM 9342 900 (by decide) sdw_pm_9342
  have hd := recon_intermediateGoal_5249_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5249, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5250 : ∀ n ∈ sm.nodes.drop 418, (5250 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9343 : ∀ n ∈ pm.nodes.drop 896, (9343 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9344 : ∀ n ∈ pm.nodes.drop 900, (9344 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5250_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5250
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5250 418 (by decide) sdw_sm_5250
  have hp0 := sd_pm_faithful_eq initPM 9343 896 (by decide) sdw_pm_9343
  have hp1 := sd_pm_faithful_eq initPM 9344 900 (by decide) sdw_pm_9344
  have hd := recon_intermediateGoal_5250_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5250, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5254 : ∀ n ∈ sm.nodes.drop 422, (5254 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9351 : ∀ n ∈ pm.nodes.drop 904, (9351 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9352 : ∀ n ∈ pm.nodes.drop 907, (9352 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5254_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5254
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5254 422 (by decide) sdw_sm_5254
  have hp0 := sd_pm_faithful_eq initPM 9351 904 (by decide) sdw_pm_9351
  have hp1 := sd_pm_faithful_eq initPM 9352 907 (by decide) sdw_pm_9352
  have hd := recon_intermediateGoal_5254_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5254, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5255 : ∀ n ∈ sm.nodes.drop 411, (5255 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9353 : ∀ n ∈ pm.nodes.drop 881, (9353 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9354 : ∀ n ∈ pm.nodes.drop 885, (9354 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5255_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5255
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5255 411 (by decide) sdw_sm_5255
  have hp0 := sd_pm_faithful_eq initPM 9353 881 (by decide) sdw_pm_9353
  have hp1 := sd_pm_faithful_eq initPM 9354 885 (by decide) sdw_pm_9354
  have hd := recon_intermediateGoal_5255_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5255, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5257 : ∀ n ∈ sm.nodes.drop 415, (5257 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9357 : ∀ n ∈ pm.nodes.drop 889, (9357 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9358 : ∀ n ∈ pm.nodes.drop 893, (9358 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5257_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5257
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5257 415 (by decide) sdw_sm_5257
  have hp0 := sd_pm_faithful_eq initPM 9357 889 (by decide) sdw_pm_9357
  have hp1 := sd_pm_faithful_eq initPM 9358 893 (by decide) sdw_pm_9358
  have hd := recon_intermediateGoal_5257_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5257, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5258 : ∀ n ∈ sm.nodes.drop 419, (5258 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9363 : ∀ n ∈ pm.nodes.drop 897, (9363 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9364 : ∀ n ∈ pm.nodes.drop 901, (9364 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5258_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5258
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5258 419 (by decide) sdw_sm_5258
  have hp0 := sd_pm_faithful_eq initPM 9363 897 (by decide) sdw_pm_9363
  have hp1 := sd_pm_faithful_eq initPM 9364 901 (by decide) sdw_pm_9364
  have hd := recon_intermediateGoal_5258_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5258, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5259 : ∀ n ∈ sm.nodes.drop 423, (5259 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9365 : ∀ n ∈ pm.nodes.drop 905, (9365 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9366 : ∀ n ∈ pm.nodes.drop 908, (9366 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5259_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5259
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5259 423 (by decide) sdw_sm_5259
  have hp0 := sd_pm_faithful_eq initPM 9365 905 (by decide) sdw_pm_9365
  have hp1 := sd_pm_faithful_eq initPM 9366 908 (by decide) sdw_pm_9366
  have hd := recon_intermediateGoal_5259_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5259, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5260 : ∀ n ∈ sm.nodes.drop 412, (5260 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9367 : ∀ n ∈ pm.nodes.drop 882, (9367 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9368 : ∀ n ∈ pm.nodes.drop 886, (9368 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5260_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5260
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5260 412 (by decide) sdw_sm_5260
  have hp0 := sd_pm_faithful_eq initPM 9367 882 (by decide) sdw_pm_9367
  have hp1 := sd_pm_faithful_eq initPM 9368 886 (by decide) sdw_pm_9368
  have hd := recon_intermediateGoal_5260_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5260, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5262 : ∀ n ∈ sm.nodes.drop 416, (5262 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9371 : ∀ n ∈ pm.nodes.drop 890, (9371 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9372 : ∀ n ∈ pm.nodes.drop 894, (9372 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5262_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5262
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5262 416 (by decide) sdw_sm_5262
  have hp0 := sd_pm_faithful_eq initPM 9371 890 (by decide) sdw_pm_9371
  have hp1 := sd_pm_faithful_eq initPM 9372 894 (by decide) sdw_pm_9372
  have hd := recon_intermediateGoal_5262_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5262, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5263 : ∀ n ∈ sm.nodes.drop 420, (5263 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9381 : ∀ n ∈ pm.nodes.drop 898, (9381 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9382 : ∀ n ∈ pm.nodes.drop 902, (9382 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5263_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5263
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5263 420 (by decide) sdw_sm_5263
  have hp0 := sd_pm_faithful_eq initPM 9381 898 (by decide) sdw_pm_9381
  have hp1 := sd_pm_faithful_eq initPM 9382 902 (by decide) sdw_pm_9382
  have hd := recon_intermediateGoal_5263_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5263, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5264 : ∀ n ∈ sm.nodes.drop 413, (5264 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9385 : ∀ n ∈ pm.nodes.drop 883, (9385 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9386 : ∀ n ∈ pm.nodes.drop 887, (9386 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5264_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5264
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5264 413 (by decide) sdw_sm_5264
  have hp0 := sd_pm_faithful_eq initPM 9385 883 (by decide) sdw_pm_9385
  have hp1 := sd_pm_faithful_eq initPM 9386 887 (by decide) sdw_pm_9386
  have hd := recon_intermediateGoal_5264_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5264, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5266 : ∀ n ∈ sm.nodes.drop 417, (5266 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9389 : ∀ n ∈ pm.nodes.drop 891, (9389 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9390 : ∀ n ∈ pm.nodes.drop 895, (9390 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5266_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5266
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5266 417 (by decide) sdw_sm_5266
  have hp0 := sd_pm_faithful_eq initPM 9389 891 (by decide) sdw_pm_9389
  have hp1 := sd_pm_faithful_eq initPM 9390 895 (by decide) sdw_pm_9390
  have hd := recon_intermediateGoal_5266_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5266, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5267 : ∀ n ∈ sm.nodes.drop 421, (5267 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9399 : ∀ n ∈ pm.nodes.drop 899, (9399 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9400 : ∀ n ∈ pm.nodes.drop 903, (9400 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5267_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5267
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5267 421 (by decide) sdw_sm_5267
  have hp0 := sd_pm_faithful_eq initPM 9399 899 (by decide) sdw_pm_9399
  have hp1 := sd_pm_faithful_eq initPM 9400 903 (by decide) sdw_pm_9400
  have hd := recon_intermediateGoal_5267_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5267, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5268 : ∀ n ∈ sm.nodes.drop 424, (5268 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9403 : ∀ n ∈ pm.nodes.drop 906, (9403 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9404 : ∀ n ∈ pm.nodes.drop 909, (9404 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5268_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5268
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5268 424 (by decide) sdw_sm_5268
  have hp0 := sd_pm_faithful_eq initPM 9403 906 (by decide) sdw_pm_9403
  have hp1 := sd_pm_faithful_eq initPM 9404 909 (by decide) sdw_pm_9404
  have hd := recon_intermediateGoal_5268_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5268, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5269 : ∀ n ∈ sm.nodes.drop 425, (5269 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9405 : ∀ n ∈ pm.nodes.drop 910, (9405 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9406 : ∀ n ∈ pm.nodes.drop 911, (9406 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5269_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5269
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5269 425 (by decide) sdw_sm_5269
  have hp0 := sd_pm_faithful_eq initPM 9405 910 (by decide) sdw_pm_9405
  have hp1 := sd_pm_faithful_eq initPM 9406 911 (by decide) sdw_pm_9406
  have hd := recon_intermediateGoal_5269_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5269, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5271 : ∀ n ∈ sm.nodes.drop 426, (5271 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9411 : ∀ n ∈ pm.nodes.drop 912, (9411 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9412 : ∀ n ∈ pm.nodes.drop 913, (9412 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5271_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5271
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5271 426 (by decide) sdw_sm_5271
  have hp0 := sd_pm_faithful_eq initPM 9411 912 (by decide) sdw_pm_9411
  have hp1 := sd_pm_faithful_eq initPM 9412 913 (by decide) sdw_pm_9412
  have hd := recon_intermediateGoal_5271_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5271, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5272 : ∀ n ∈ sm.nodes.drop 427, (5272 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9421 : ∀ n ∈ pm.nodes.drop 914, (9421 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9422 : ∀ n ∈ pm.nodes.drop 915, (9422 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5272_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5272
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5272 427 (by decide) sdw_sm_5272
  have hp0 := sd_pm_faithful_eq initPM 9421 914 (by decide) sdw_pm_9421
  have hp1 := sd_pm_faithful_eq initPM 9422 915 (by decide) sdw_pm_9422
  have hd := recon_intermediateGoal_5272_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5272, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5273 : ∀ n ∈ sm.nodes.drop 428, (5273 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9425 : ∀ n ∈ pm.nodes.drop 916, (9425 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9426 : ∀ n ∈ pm.nodes.drop 917, (9426 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5273_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5273
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5273 428 (by decide) sdw_sm_5273
  have hp0 := sd_pm_faithful_eq initPM 9425 916 (by decide) sdw_pm_9425
  have hp1 := sd_pm_faithful_eq initPM 9426 917 (by decide) sdw_pm_9426
  have hd := recon_intermediateGoal_5273_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5273, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5274 : ∀ n ∈ sm.nodes.drop 429, (5274 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9429 : ∀ n ∈ pm.nodes.drop 918, (9429 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9430 : ∀ n ∈ pm.nodes.drop 919, (9430 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5274_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5274
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5274 429 (by decide) sdw_sm_5274
  have hp0 := sd_pm_faithful_eq initPM 9429 918 (by decide) sdw_pm_9429
  have hp1 := sd_pm_faithful_eq initPM 9430 919 (by decide) sdw_pm_9430
  have hd := recon_intermediateGoal_5274_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5274, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5275 : ∀ n ∈ sm.nodes.drop 430, (5275 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9435 : ∀ n ∈ pm.nodes.drop 920, (9435 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9436 : ∀ n ∈ pm.nodes.drop 921, (9436 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5275_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5275
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5275 430 (by decide) sdw_sm_5275
  have hp0 := sd_pm_faithful_eq initPM 9435 920 (by decide) sdw_pm_9435
  have hp1 := sd_pm_faithful_eq initPM 9436 921 (by decide) sdw_pm_9436
  have hd := recon_intermediateGoal_5275_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5275, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5276 : ∀ n ∈ sm.nodes.drop 431, (5276 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9439 : ∀ n ∈ pm.nodes.drop 922, (9439 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9440 : ∀ n ∈ pm.nodes.drop 923, (9440 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5276_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5276
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5276 431 (by decide) sdw_sm_5276
  have hp0 := sd_pm_faithful_eq initPM 9439 922 (by decide) sdw_pm_9439
  have hp1 := sd_pm_faithful_eq initPM 9440 923 (by decide) sdw_pm_9440
  have hd := recon_intermediateGoal_5276_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5276, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7907 : ∀ n ∈ sm.nodes.drop 393, (7907 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15537 : ∀ n ∈ pm.nodes.drop 846, (15537 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15545 : ∀ n ∈ pm.nodes.drop 847, (15545 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7907_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7907
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7907 393 (by decide) sdw_sm_7907
  have hp0 := sd_pm_faithful_eq initPM 15537 846 (by decide) sdw_pm_15537
  have hp1 := sd_pm_faithful_eq initPM 15545 847 (by decide) sdw_pm_15545
  have hd := recon_intermediateGoal_7907_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_7907, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7928 : ∀ n ∈ sm.nodes.drop 407, (7928 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15579 : ∀ n ∈ pm.nodes.drop 874, (15579 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15587 : ∀ n ∈ pm.nodes.drop 875, (15587 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7928_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7928
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7928 407 (by decide) sdw_sm_7928
  have hp0 := sd_pm_faithful_eq initPM 15579 874 (by decide) sdw_pm_15579
  have hp1 := sd_pm_faithful_eq initPM 15587 875 (by decide) sdw_pm_15587
  have hd := recon_intermediateGoal_7928_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_7928, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7939 : ∀ n ∈ sm.nodes.drop 409, (7939 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15598 : ∀ n ∈ pm.nodes.drop 878, (15598 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15621 : ∀ n ∈ pm.nodes.drop 879, (15621 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7939_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7939
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7939 409 (by decide) sdw_sm_7939
  have hp0 := sd_pm_faithful_eq initPM 15598 878 (by decide) sdw_pm_15598
  have hp1 := sd_pm_faithful_eq initPM 15621 879 (by decide) sdw_pm_15621
  have hd := recon_intermediateGoal_7939_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_7939, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

end

end TrainVerify.Denote.GeneratedPatterns
