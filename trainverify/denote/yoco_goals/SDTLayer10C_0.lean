/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer10DistributedContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer10DistributedContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5200 : ∀ n ∈ sm.nodes.drop 383, (5200 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9165 : ∀ n ∈ pm.nodes.drop 826, (9165 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9166 : ∀ n ∈ pm.nodes.drop 829, (9166 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5200_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5200
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5200 383 (by decide) sdw_sm_5200
  have hp0 := sd_pm_faithful_eq initPM 9165 826 (by decide) sdw_pm_9165
  have hp1 := sd_pm_faithful_eq initPM 9166 829 (by decide) sdw_pm_9166
  have hd := recon_intermediateGoal_5200_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5200, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5201 : ∀ n ∈ sm.nodes.drop 372, (5201 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9167 : ∀ n ∈ pm.nodes.drop 803, (9167 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9168 : ∀ n ∈ pm.nodes.drop 807, (9168 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5201_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5201
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5201 372 (by decide) sdw_sm_5201
  have hp0 := sd_pm_faithful_eq initPM 9167 803 (by decide) sdw_pm_9167
  have hp1 := sd_pm_faithful_eq initPM 9168 807 (by decide) sdw_pm_9168
  have hd := recon_intermediateGoal_5201_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5201, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5203 : ∀ n ∈ sm.nodes.drop 376, (5203 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9171 : ∀ n ∈ pm.nodes.drop 811, (9171 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9172 : ∀ n ∈ pm.nodes.drop 815, (9172 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5203_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5203
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5203 376 (by decide) sdw_sm_5203
  have hp0 := sd_pm_faithful_eq initPM 9171 811 (by decide) sdw_pm_9171
  have hp1 := sd_pm_faithful_eq initPM 9172 815 (by decide) sdw_pm_9172
  have hd := recon_intermediateGoal_5203_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5203, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5204 : ∀ n ∈ sm.nodes.drop 380, (5204 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9177 : ∀ n ∈ pm.nodes.drop 819, (9177 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9178 : ∀ n ∈ pm.nodes.drop 823, (9178 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5204_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5204
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5204 380 (by decide) sdw_sm_5204
  have hp0 := sd_pm_faithful_eq initPM 9177 819 (by decide) sdw_pm_9177
  have hp1 := sd_pm_faithful_eq initPM 9178 823 (by decide) sdw_pm_9178
  have hd := recon_intermediateGoal_5204_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5204, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5205 : ∀ n ∈ sm.nodes.drop 384, (5205 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9179 : ∀ n ∈ pm.nodes.drop 827, (9179 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9180 : ∀ n ∈ pm.nodes.drop 830, (9180 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5205_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5205
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5205 384 (by decide) sdw_sm_5205
  have hp0 := sd_pm_faithful_eq initPM 9179 827 (by decide) sdw_pm_9179
  have hp1 := sd_pm_faithful_eq initPM 9180 830 (by decide) sdw_pm_9180
  have hd := recon_intermediateGoal_5205_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5205, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5206 : ∀ n ∈ sm.nodes.drop 373, (5206 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9181 : ∀ n ∈ pm.nodes.drop 804, (9181 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9182 : ∀ n ∈ pm.nodes.drop 808, (9182 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5206_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5206
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5206 373 (by decide) sdw_sm_5206
  have hp0 := sd_pm_faithful_eq initPM 9181 804 (by decide) sdw_pm_9181
  have hp1 := sd_pm_faithful_eq initPM 9182 808 (by decide) sdw_pm_9182
  have hd := recon_intermediateGoal_5206_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5206, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5208 : ∀ n ∈ sm.nodes.drop 377, (5208 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9185 : ∀ n ∈ pm.nodes.drop 812, (9185 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9186 : ∀ n ∈ pm.nodes.drop 816, (9186 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5208_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5208
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5208 377 (by decide) sdw_sm_5208
  have hp0 := sd_pm_faithful_eq initPM 9185 812 (by decide) sdw_pm_9185
  have hp1 := sd_pm_faithful_eq initPM 9186 816 (by decide) sdw_pm_9186
  have hd := recon_intermediateGoal_5208_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5208, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5209 : ∀ n ∈ sm.nodes.drop 381, (5209 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9195 : ∀ n ∈ pm.nodes.drop 820, (9195 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9196 : ∀ n ∈ pm.nodes.drop 824, (9196 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5209_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5209
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5209 381 (by decide) sdw_sm_5209
  have hp0 := sd_pm_faithful_eq initPM 9195 820 (by decide) sdw_pm_9195
  have hp1 := sd_pm_faithful_eq initPM 9196 824 (by decide) sdw_pm_9196
  have hd := recon_intermediateGoal_5209_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5209, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5210 : ∀ n ∈ sm.nodes.drop 374, (5210 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9199 : ∀ n ∈ pm.nodes.drop 805, (9199 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9200 : ∀ n ∈ pm.nodes.drop 809, (9200 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5210_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5210
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5210 374 (by decide) sdw_sm_5210
  have hp0 := sd_pm_faithful_eq initPM 9199 805 (by decide) sdw_pm_9199
  have hp1 := sd_pm_faithful_eq initPM 9200 809 (by decide) sdw_pm_9200
  have hd := recon_intermediateGoal_5210_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5210, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5212 : ∀ n ∈ sm.nodes.drop 378, (5212 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9203 : ∀ n ∈ pm.nodes.drop 813, (9203 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9204 : ∀ n ∈ pm.nodes.drop 817, (9204 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5212_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5212
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5212 378 (by decide) sdw_sm_5212
  have hp0 := sd_pm_faithful_eq initPM 9203 813 (by decide) sdw_pm_9203
  have hp1 := sd_pm_faithful_eq initPM 9204 817 (by decide) sdw_pm_9204
  have hd := recon_intermediateGoal_5212_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5212, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5213 : ∀ n ∈ sm.nodes.drop 382, (5213 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9213 : ∀ n ∈ pm.nodes.drop 821, (9213 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9214 : ∀ n ∈ pm.nodes.drop 825, (9214 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5213_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5213
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5213 382 (by decide) sdw_sm_5213
  have hp0 := sd_pm_faithful_eq initPM 9213 821 (by decide) sdw_pm_9213
  have hp1 := sd_pm_faithful_eq initPM 9214 825 (by decide) sdw_pm_9214
  have hd := recon_intermediateGoal_5213_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5213, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5214 : ∀ n ∈ sm.nodes.drop 385, (5214 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9217 : ∀ n ∈ pm.nodes.drop 828, (9217 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9218 : ∀ n ∈ pm.nodes.drop 831, (9218 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5214_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5214
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5214 385 (by decide) sdw_sm_5214
  have hp0 := sd_pm_faithful_eq initPM 9217 828 (by decide) sdw_pm_9217
  have hp1 := sd_pm_faithful_eq initPM 9218 831 (by decide) sdw_pm_9218
  have hd := recon_intermediateGoal_5214_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5214, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5215 : ∀ n ∈ sm.nodes.drop 386, (5215 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9219 : ∀ n ∈ pm.nodes.drop 832, (9219 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9220 : ∀ n ∈ pm.nodes.drop 833, (9220 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5215_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5215
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5215 386 (by decide) sdw_sm_5215
  have hp0 := sd_pm_faithful_eq initPM 9219 832 (by decide) sdw_pm_9219
  have hp1 := sd_pm_faithful_eq initPM 9220 833 (by decide) sdw_pm_9220
  have hd := recon_intermediateGoal_5215_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5215, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5217 : ∀ n ∈ sm.nodes.drop 387, (5217 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9225 : ∀ n ∈ pm.nodes.drop 834, (9225 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9226 : ∀ n ∈ pm.nodes.drop 835, (9226 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5217_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5217
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5217 387 (by decide) sdw_sm_5217
  have hp0 := sd_pm_faithful_eq initPM 9225 834 (by decide) sdw_pm_9225
  have hp1 := sd_pm_faithful_eq initPM 9226 835 (by decide) sdw_pm_9226
  have hd := recon_intermediateGoal_5217_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5217, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5218 : ∀ n ∈ sm.nodes.drop 388, (5218 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9235 : ∀ n ∈ pm.nodes.drop 836, (9235 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9236 : ∀ n ∈ pm.nodes.drop 837, (9236 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5218_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5218
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5218 388 (by decide) sdw_sm_5218
  have hp0 := sd_pm_faithful_eq initPM 9235 836 (by decide) sdw_pm_9235
  have hp1 := sd_pm_faithful_eq initPM 9236 837 (by decide) sdw_pm_9236
  have hd := recon_intermediateGoal_5218_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5218, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5219 : ∀ n ∈ sm.nodes.drop 389, (5219 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9239 : ∀ n ∈ pm.nodes.drop 838, (9239 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9240 : ∀ n ∈ pm.nodes.drop 839, (9240 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5219_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5219
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5219 389 (by decide) sdw_sm_5219
  have hp0 := sd_pm_faithful_eq initPM 9239 838 (by decide) sdw_pm_9239
  have hp1 := sd_pm_faithful_eq initPM 9240 839 (by decide) sdw_pm_9240
  have hd := recon_intermediateGoal_5219_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5219, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5220 : ∀ n ∈ sm.nodes.drop 390, (5220 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9243 : ∀ n ∈ pm.nodes.drop 840, (9243 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9244 : ∀ n ∈ pm.nodes.drop 841, (9244 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5220_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5220
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5220 390 (by decide) sdw_sm_5220
  have hp0 := sd_pm_faithful_eq initPM 9243 840 (by decide) sdw_pm_9243
  have hp1 := sd_pm_faithful_eq initPM 9244 841 (by decide) sdw_pm_9244
  have hd := recon_intermediateGoal_5220_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5220, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5221 : ∀ n ∈ sm.nodes.drop 391, (5221 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9249 : ∀ n ∈ pm.nodes.drop 842, (9249 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9250 : ∀ n ∈ pm.nodes.drop 843, (9250 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5221_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5221
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5221 391 (by decide) sdw_sm_5221
  have hp0 := sd_pm_faithful_eq initPM 9249 842 (by decide) sdw_pm_9249
  have hp1 := sd_pm_faithful_eq initPM 9250 843 (by decide) sdw_pm_9250
  have hd := recon_intermediateGoal_5221_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5221, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5222 : ∀ n ∈ sm.nodes.drop 392, (5222 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9253 : ∀ n ∈ pm.nodes.drop 844, (9253 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9254 : ∀ n ∈ pm.nodes.drop 845, (9254 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5222_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5222
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5222 392 (by decide) sdw_sm_5222
  have hp0 := sd_pm_faithful_eq initPM 9253 844 (by decide) sdw_pm_9253
  have hp1 := sd_pm_faithful_eq initPM 9254 845 (by decide) sdw_pm_9254
  have hd := recon_intermediateGoal_5222_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5222, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5224 : ∀ n ∈ sm.nodes.drop 394, (5224 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9257 : ∀ n ∈ pm.nodes.drop 848, (9257 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9258 : ∀ n ∈ pm.nodes.drop 849, (9258 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5224_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5224
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5224 394 (by decide) sdw_sm_5224
  have hp0 := sd_pm_faithful_eq initPM 9257 848 (by decide) sdw_pm_9257
  have hp1 := sd_pm_faithful_eq initPM 9258 849 (by decide) sdw_pm_9258
  have hd := recon_intermediateGoal_5224_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5224, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5226 : ∀ n ∈ sm.nodes.drop 396, (5226 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9259 : ∀ n ∈ pm.nodes.drop 852, (9259 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9260 : ∀ n ∈ pm.nodes.drop 855, (9260 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5226_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5226
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5226 396 (by decide) sdw_sm_5226
  have hp0 := sd_pm_faithful_eq initPM 9259 852 (by decide) sdw_pm_9259
  have hp1 := sd_pm_faithful_eq initPM 9260 855 (by decide) sdw_pm_9260
  have hd := recon_intermediateGoal_5226_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5226, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5228 : ∀ n ∈ sm.nodes.drop 397, (5228 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9271 : ∀ n ∈ pm.nodes.drop 853, (9271 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9272 : ∀ n ∈ pm.nodes.drop 856, (9272 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5228_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5228
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5228 397 (by decide) sdw_sm_5228
  have hp0 := sd_pm_faithful_eq initPM 9271 853 (by decide) sdw_pm_9271
  have hp1 := sd_pm_faithful_eq initPM 9272 856 (by decide) sdw_pm_9272
  have hd := recon_intermediateGoal_5228_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5228, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5230 : ∀ n ∈ sm.nodes.drop 398, (5230 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9281 : ∀ n ∈ pm.nodes.drop 854, (9281 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9282 : ∀ n ∈ pm.nodes.drop 857, (9282 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5230_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5230
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5230 398 (by decide) sdw_sm_5230
  have hp0 := sd_pm_faithful_eq initPM 9281 854 (by decide) sdw_pm_9281
  have hp1 := sd_pm_faithful_eq initPM 9282 857 (by decide) sdw_pm_9282
  have hd := recon_intermediateGoal_5230_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5230, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5232 : ∀ n ∈ sm.nodes.drop 399, (5232 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9293 : ∀ n ∈ pm.nodes.drop 858, (9293 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9294 : ∀ n ∈ pm.nodes.drop 859, (9294 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5232_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5232
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5232 399 (by decide) sdw_sm_5232
  have hp0 := sd_pm_faithful_eq initPM 9293 858 (by decide) sdw_pm_9293
  have hp1 := sd_pm_faithful_eq initPM 9294 859 (by decide) sdw_pm_9294
  have hd := recon_intermediateGoal_5232_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5232, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5233 : ∀ n ∈ sm.nodes.drop 399, (5233 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9295 : ∀ n ∈ pm.nodes.drop 858, (9295 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9296 : ∀ n ∈ pm.nodes.drop 859, (9296 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5233_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5233
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5233 399 (by decide) sdw_sm_5233
  have hp0 := sd_pm_faithful_eq initPM 9295 858 (by decide) sdw_pm_9295
  have hp1 := sd_pm_faithful_eq initPM 9296 859 (by decide) sdw_pm_9296
  have hd := recon_intermediateGoal_5233_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5233, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5236 : ∀ n ∈ sm.nodes.drop 400, (5236 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9297 : ∀ n ∈ pm.nodes.drop 860, (9297 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9298 : ∀ n ∈ pm.nodes.drop 861, (9298 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5236_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5236
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5236 400 (by decide) sdw_sm_5236
  have hp0 := sd_pm_faithful_eq initPM 9297 860 (by decide) sdw_pm_9297
  have hp1 := sd_pm_faithful_eq initPM 9298 861 (by decide) sdw_pm_9298
  have hd := recon_intermediateGoal_5236_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_5236, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7876 : ∀ n ∈ sm.nodes.drop 368, (7876 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15475 : ∀ n ∈ pm.nodes.drop 796, (15475 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15483 : ∀ n ∈ pm.nodes.drop 797, (15483 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7876_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7876
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7876 368 (by decide) sdw_sm_7876
  have hp0 := sd_pm_faithful_eq initPM 15475 796 (by decide) sdw_pm_15475
  have hp1 := sd_pm_faithful_eq initPM 15483 797 (by decide) sdw_pm_15483
  have hd := recon_intermediateGoal_7876_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_7876, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7887 : ∀ n ∈ sm.nodes.drop 370, (7887 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15494 : ∀ n ∈ pm.nodes.drop 800, (15494 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15517 : ∀ n ∈ pm.nodes.drop 801, (15517 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7887_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7887
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7887 370 (by decide) sdw_sm_7887
  have hp0 := sd_pm_faithful_eq initPM 15494 800 (by decide) sdw_pm_15494
  have hp1 := sd_pm_faithful_eq initPM 15517 801 (by decide) sdw_pm_15517
  have hd := recon_intermediateGoal_7887_distributed initSM initPM hSM hPM hInit
  unfold InitGoalHolds at hd ⊢
  simp only [intermediateGoal_7887, List.map, reconstructForGoal, reconstructWithDim_singleton,
    reconstructWithDim] at hd ⊢
  rw [hs, hp0, hp1]
  exact hd

end

end TrainVerify.Denote.GeneratedPatterns
