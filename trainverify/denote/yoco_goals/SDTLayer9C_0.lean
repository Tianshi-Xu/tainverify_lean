/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer9DistributedContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer9DistributedContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5146 : ∀ n ∈ sm.nodes.drop 344, (5146 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8979 : ∀ n ∈ pm.nodes.drop 748, (8979 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8980 : ∀ n ∈ pm.nodes.drop 751, (8980 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5146_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5146
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5146 344 (by decide) sdw_sm_5146
  have hp0 := sd_pm_faithful_eq initPM 8979 748 (by decide) sdw_pm_8979
  have hp1 := sd_pm_faithful_eq initPM 8980 751 (by decide) sdw_pm_8980
  have hd := recon_intermediateGoal_5146_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5146
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5166 : ∀ n ∈ sm.nodes.drop 351, (5166 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9057 : ∀ n ∈ pm.nodes.drop 762, (9057 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9058 : ∀ n ∈ pm.nodes.drop 763, (9058 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5166_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5166
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5166 351 (by decide) sdw_sm_5166
  have hp0 := sd_pm_faithful_eq initPM 9057 762 (by decide) sdw_pm_9057
  have hp1 := sd_pm_faithful_eq initPM 9058 763 (by decide) sdw_pm_9058
  have hd := recon_intermediateGoal_5166_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5166
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5167 : ∀ n ∈ sm.nodes.drop 352, (5167 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9063 : ∀ n ∈ pm.nodes.drop 764, (9063 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9064 : ∀ n ∈ pm.nodes.drop 765, (9064 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5167_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5167
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5167 352 (by decide) sdw_sm_5167
  have hp0 := sd_pm_faithful_eq initPM 9063 764 (by decide) sdw_pm_9063
  have hp1 := sd_pm_faithful_eq initPM 9064 765 (by decide) sdw_pm_9064
  have hd := recon_intermediateGoal_5167_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5167
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5168 : ∀ n ∈ sm.nodes.drop 353, (5168 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9067 : ∀ n ∈ pm.nodes.drop 766, (9067 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9068 : ∀ n ∈ pm.nodes.drop 767, (9068 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5168_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5168
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5168 353 (by decide) sdw_sm_5168
  have hp0 := sd_pm_faithful_eq initPM 9067 766 (by decide) sdw_pm_9067
  have hp1 := sd_pm_faithful_eq initPM 9068 767 (by decide) sdw_pm_9068
  have hd := recon_intermediateGoal_5168_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5168
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5170 : ∀ n ∈ sm.nodes.drop 355, (5170 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9071 : ∀ n ∈ pm.nodes.drop 770, (9071 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9072 : ∀ n ∈ pm.nodes.drop 771, (9072 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5170_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5170
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5170 355 (by decide) sdw_sm_5170
  have hp0 := sd_pm_faithful_eq initPM 9071 770 (by decide) sdw_pm_9071
  have hp1 := sd_pm_faithful_eq initPM 9072 771 (by decide) sdw_pm_9072
  have hd := recon_intermediateGoal_5170_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5170
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5172 : ∀ n ∈ sm.nodes.drop 357, (5172 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9073 : ∀ n ∈ pm.nodes.drop 774, (9073 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9074 : ∀ n ∈ pm.nodes.drop 777, (9074 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5172_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5172
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5172 357 (by decide) sdw_sm_5172
  have hp0 := sd_pm_faithful_eq initPM 9073 774 (by decide) sdw_pm_9073
  have hp1 := sd_pm_faithful_eq initPM 9074 777 (by decide) sdw_pm_9074
  have hd := recon_intermediateGoal_5172_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5172
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5174 : ∀ n ∈ sm.nodes.drop 358, (5174 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9085 : ∀ n ∈ pm.nodes.drop 775, (9085 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9086 : ∀ n ∈ pm.nodes.drop 778, (9086 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5174_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5174
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5174 358 (by decide) sdw_sm_5174
  have hp0 := sd_pm_faithful_eq initPM 9085 775 (by decide) sdw_pm_9085
  have hp1 := sd_pm_faithful_eq initPM 9086 778 (by decide) sdw_pm_9086
  have hd := recon_intermediateGoal_5174_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5174
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5176 : ∀ n ∈ sm.nodes.drop 359, (5176 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9095 : ∀ n ∈ pm.nodes.drop 776, (9095 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9096 : ∀ n ∈ pm.nodes.drop 779, (9096 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5176_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5176
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5176 359 (by decide) sdw_sm_5176
  have hp0 := sd_pm_faithful_eq initPM 9095 776 (by decide) sdw_pm_9095
  have hp1 := sd_pm_faithful_eq initPM 9096 779 (by decide) sdw_pm_9096
  have hd := recon_intermediateGoal_5176_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5176
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5178 : ∀ n ∈ sm.nodes.drop 360, (5178 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9107 : ∀ n ∈ pm.nodes.drop 780, (9107 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9108 : ∀ n ∈ pm.nodes.drop 781, (9108 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5178_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5178
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5178 360 (by decide) sdw_sm_5178
  have hp0 := sd_pm_faithful_eq initPM 9107 780 (by decide) sdw_pm_9107
  have hp1 := sd_pm_faithful_eq initPM 9108 781 (by decide) sdw_pm_9108
  have hd := recon_intermediateGoal_5178_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5178
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5179 : ∀ n ∈ sm.nodes.drop 360, (5179 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9109 : ∀ n ∈ pm.nodes.drop 780, (9109 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9110 : ∀ n ∈ pm.nodes.drop 781, (9110 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5179_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5179
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5179 360 (by decide) sdw_sm_5179
  have hp0 := sd_pm_faithful_eq initPM 9109 780 (by decide) sdw_pm_9109
  have hp1 := sd_pm_faithful_eq initPM 9110 781 (by decide) sdw_pm_9110
  have hd := recon_intermediateGoal_5179_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5179
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5182 : ∀ n ∈ sm.nodes.drop 361, (5182 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9111 : ∀ n ∈ pm.nodes.drop 782, (9111 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9112 : ∀ n ∈ pm.nodes.drop 783, (9112 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5182_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5182
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5182 361 (by decide) sdw_sm_5182
  have hp0 := sd_pm_faithful_eq initPM 9111 782 (by decide) sdw_pm_9111
  have hp1 := sd_pm_faithful_eq initPM 9112 783 (by decide) sdw_pm_9112
  have hd := recon_intermediateGoal_5182_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5182
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5183 : ∀ n ∈ sm.nodes.drop 362, (5183 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9113 : ∀ n ∈ pm.nodes.drop 784, (9113 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9114 : ∀ n ∈ pm.nodes.drop 785, (9114 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5183_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5183
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5183 362 (by decide) sdw_sm_5183
  have hp0 := sd_pm_faithful_eq initPM 9113 784 (by decide) sdw_pm_9113
  have hp1 := sd_pm_faithful_eq initPM 9114 785 (by decide) sdw_pm_9114
  have hd := recon_intermediateGoal_5183_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5183
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5184 : ∀ n ∈ sm.nodes.drop 363, (5184 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9119 : ∀ n ∈ pm.nodes.drop 786, (9119 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9120 : ∀ n ∈ pm.nodes.drop 787, (9120 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5184_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5184
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5184 363 (by decide) sdw_sm_5184
  have hp0 := sd_pm_faithful_eq initPM 9119 786 (by decide) sdw_pm_9119
  have hp1 := sd_pm_faithful_eq initPM 9120 787 (by decide) sdw_pm_9120
  have hd := recon_intermediateGoal_5184_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5184
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5186 : ∀ n ∈ sm.nodes.drop 364, (5186 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9123 : ∀ n ∈ pm.nodes.drop 788, (9123 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9124 : ∀ n ∈ pm.nodes.drop 789, (9124 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5186_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5186
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5186 364 (by decide) sdw_sm_5186
  have hp0 := sd_pm_faithful_eq initPM 9123 788 (by decide) sdw_pm_9123
  have hp1 := sd_pm_faithful_eq initPM 9124 789 (by decide) sdw_pm_9124
  have hd := recon_intermediateGoal_5186_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5186
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5187 : ∀ n ∈ sm.nodes.drop 365, (5187 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9133 : ∀ n ∈ pm.nodes.drop 790, (9133 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9134 : ∀ n ∈ pm.nodes.drop 791, (9134 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5187_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5187
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5187 365 (by decide) sdw_sm_5187
  have hp0 := sd_pm_faithful_eq initPM 9133 790 (by decide) sdw_pm_9133
  have hp1 := sd_pm_faithful_eq initPM 9134 791 (by decide) sdw_pm_9134
  have hd := recon_intermediateGoal_5187_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5187
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5188 : ∀ n ∈ sm.nodes.drop 366, (5188 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9137 : ∀ n ∈ pm.nodes.drop 792, (9137 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9138 : ∀ n ∈ pm.nodes.drop 793, (9138 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5188_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5188
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5188 366 (by decide) sdw_sm_5188
  have hp0 := sd_pm_faithful_eq initPM 9137 792 (by decide) sdw_pm_9137
  have hp1 := sd_pm_faithful_eq initPM 9138 793 (by decide) sdw_pm_9138
  have hd := recon_intermediateGoal_5188_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5188
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5189 : ∀ n ∈ sm.nodes.drop 367, (5189 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9141 : ∀ n ∈ pm.nodes.drop 794, (9141 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9142 : ∀ n ∈ pm.nodes.drop 795, (9142 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5189_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5189
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5189 367 (by decide) sdw_sm_5189
  have hp0 := sd_pm_faithful_eq initPM 9141 794 (by decide) sdw_pm_9141
  have hp1 := sd_pm_faithful_eq initPM 9142 795 (by decide) sdw_pm_9142
  have hd := recon_intermediateGoal_5189_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5189
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5191 : ∀ n ∈ sm.nodes.drop 369, (5191 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9145 : ∀ n ∈ pm.nodes.drop 798, (9145 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9146 : ∀ n ∈ pm.nodes.drop 799, (9146 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5191_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5191
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5191 369 (by decide) sdw_sm_5191
  have hp0 := sd_pm_faithful_eq initPM 9145 798 (by decide) sdw_pm_9145
  have hp1 := sd_pm_faithful_eq initPM 9146 799 (by decide) sdw_pm_9146
  have hd := recon_intermediateGoal_5191_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5191
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5192 : ∀ n ∈ sm.nodes.drop 371, (5192 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9147 : ∀ n ∈ pm.nodes.drop 802, (9147 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9148 : ∀ n ∈ pm.nodes.drop 806, (9148 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5192_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5192
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5192 371 (by decide) sdw_sm_5192
  have hp0 := sd_pm_faithful_eq initPM 9147 802 (by decide) sdw_pm_9147
  have hp1 := sd_pm_faithful_eq initPM 9148 806 (by decide) sdw_pm_9148
  have hd := recon_intermediateGoal_5192_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5192
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5194 : ∀ n ∈ sm.nodes.drop 375, (5194 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9153 : ∀ n ∈ pm.nodes.drop 810, (9153 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9154 : ∀ n ∈ pm.nodes.drop 814, (9154 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5194_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5194
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5194 375 (by decide) sdw_sm_5194
  have hp0 := sd_pm_faithful_eq initPM 9153 810 (by decide) sdw_pm_9153
  have hp1 := sd_pm_faithful_eq initPM 9154 814 (by decide) sdw_pm_9154
  have hd := recon_intermediateGoal_5194_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5194
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5195 : ∀ n ∈ sm.nodes.drop 379, (5195 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9155 : ∀ n ∈ pm.nodes.drop 818, (9155 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9156 : ∀ n ∈ pm.nodes.drop 822, (9156 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5195_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5195
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5195 379 (by decide) sdw_sm_5195
  have hp0 := sd_pm_faithful_eq initPM 9155 818 (by decide) sdw_pm_9155
  have hp1 := sd_pm_faithful_eq initPM 9156 822 (by decide) sdw_pm_9156
  have hd := recon_intermediateGoal_5195_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5195
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5196 : ∀ n ∈ sm.nodes.drop 379, (5196 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9157 : ∀ n ∈ pm.nodes.drop 818, (9157 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9158 : ∀ n ∈ pm.nodes.drop 822, (9158 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5196_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5196
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5196 379 (by decide) sdw_sm_5196
  have hp0 := sd_pm_faithful_eq initPM 9157 818 (by decide) sdw_pm_9157
  have hp1 := sd_pm_faithful_eq initPM 9158 822 (by decide) sdw_pm_9158
  have hd := recon_intermediateGoal_5196_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5196
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7824 : ∀ n ∈ sm.nodes.drop 329, (7824 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15371 : ∀ n ∈ pm.nodes.drop 718, (15371 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15379 : ∀ n ∈ pm.nodes.drop 719, (15379 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7824_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7824
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7824 329 (by decide) sdw_sm_7824
  have hp0 := sd_pm_faithful_eq initPM 15371 718 (by decide) sdw_pm_15371
  have hp1 := sd_pm_faithful_eq initPM 15379 719 (by decide) sdw_pm_15379
  have hd := recon_intermediateGoal_7824_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7824
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7835 : ∀ n ∈ sm.nodes.drop 331, (7835 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15390 : ∀ n ∈ pm.nodes.drop 722, (15390 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15413 : ∀ n ∈ pm.nodes.drop 723, (15413 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7835_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7835
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7835 331 (by decide) sdw_sm_7835
  have hp0 := sd_pm_faithful_eq initPM 15390 722 (by decide) sdw_pm_15390
  have hp1 := sd_pm_faithful_eq initPM 15413 723 (by decide) sdw_pm_15413
  have hd := recon_intermediateGoal_7835_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7835
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_7855 : ∀ n ∈ sm.nodes.drop 354, (7855 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15433 : ∀ n ∈ pm.nodes.drop 768, (15433 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_15441 : ∀ n ∈ pm.nodes.drop 769, (15441 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7855_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7855
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 7855 354 (by decide) sdw_sm_7855
  have hp0 := sd_pm_faithful_eq initPM 15433 768 (by decide) sdw_pm_15433
  have hp1 := sd_pm_faithful_eq initPM 15441 769 (by decide) sdw_pm_15441
  have hd := recon_intermediateGoal_7855_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_7855
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
