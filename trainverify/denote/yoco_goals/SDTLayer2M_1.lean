/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer2DistributedMigration

/-!
# Self-decoder goals transported to the faithful track

Batch 1 of the goals originally proved in `Layer2DistributedMigration.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4864 : ∀ n ∈ sm.nodes.drop 132, (4864 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8021 : ∀ n ∈ pm.nodes.drop 324, (8021 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8022 : ∀ n ∈ pm.nodes.drop 325, (8022 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4864_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4864
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4864 132 (by decide) sdw_sm_4864
  have hp0 := sd_pm_faithful_eq initPM 8021 324 (by decide) sdw_pm_8021
  have hp1 := sd_pm_faithful_eq initPM 8022 325 (by decide) sdw_pm_8022
  have hd := recon_intermediateGoal_4864_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4864
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4865 : ∀ n ∈ sm.nodes.drop 133, (4865 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8025 : ∀ n ∈ pm.nodes.drop 326, (8025 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8026 : ∀ n ∈ pm.nodes.drop 327, (8026 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4865_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4865
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4865 133 (by decide) sdw_sm_4865
  have hp0 := sd_pm_faithful_eq initPM 8025 326 (by decide) sdw_pm_8025
  have hp1 := sd_pm_faithful_eq initPM 8026 327 (by decide) sdw_pm_8026
  have hd := recon_intermediateGoal_4865_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4865
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4867 : ∀ n ∈ sm.nodes.drop 135, (4867 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8029 : ∀ n ∈ pm.nodes.drop 330, (8029 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8030 : ∀ n ∈ pm.nodes.drop 331, (8030 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4867_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4867
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4867 135 (by decide) sdw_sm_4867
  have hp0 := sd_pm_faithful_eq initPM 8029 330 (by decide) sdw_pm_8029
  have hp1 := sd_pm_faithful_eq initPM 8030 331 (by decide) sdw_pm_8030
  have hd := recon_intermediateGoal_4867_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4867
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4868 : ∀ n ∈ sm.nodes.drop 137, (4868 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8031 : ∀ n ∈ pm.nodes.drop 334, (8031 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8032 : ∀ n ∈ pm.nodes.drop 338, (8032 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4868_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4868
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4868 137 (by decide) sdw_sm_4868
  have hp0 := sd_pm_faithful_eq initPM 8031 334 (by decide) sdw_pm_8031
  have hp1 := sd_pm_faithful_eq initPM 8032 338 (by decide) sdw_pm_8032
  have hd := recon_intermediateGoal_4868_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4868
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4870 : ∀ n ∈ sm.nodes.drop 141, (4870 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8037 : ∀ n ∈ pm.nodes.drop 342, (8037 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8038 : ∀ n ∈ pm.nodes.drop 346, (8038 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4870_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4870
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4870 141 (by decide) sdw_sm_4870
  have hp0 := sd_pm_faithful_eq initPM 8037 342 (by decide) sdw_pm_8037
  have hp1 := sd_pm_faithful_eq initPM 8038 346 (by decide) sdw_pm_8038
  have hd := recon_intermediateGoal_4870_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4870
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4871 : ∀ n ∈ sm.nodes.drop 145, (4871 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8039 : ∀ n ∈ pm.nodes.drop 350, (8039 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8040 : ∀ n ∈ pm.nodes.drop 354, (8040 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4871_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4871
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4871 145 (by decide) sdw_sm_4871
  have hp0 := sd_pm_faithful_eq initPM 8039 350 (by decide) sdw_pm_8039
  have hp1 := sd_pm_faithful_eq initPM 8040 354 (by decide) sdw_pm_8040
  have hd := recon_intermediateGoal_4871_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4871
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4872 : ∀ n ∈ sm.nodes.drop 145, (4872 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8041 : ∀ n ∈ pm.nodes.drop 350, (8041 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8042 : ∀ n ∈ pm.nodes.drop 354, (8042 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4872_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4872
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4872 145 (by decide) sdw_sm_4872
  have hp0 := sd_pm_faithful_eq initPM 8041 350 (by decide) sdw_pm_8041
  have hp1 := sd_pm_faithful_eq initPM 8042 354 (by decide) sdw_pm_8042
  have hd := recon_intermediateGoal_4872_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4872
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4876 : ∀ n ∈ sm.nodes.drop 149, (4876 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8049 : ∀ n ∈ pm.nodes.drop 358, (8049 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8050 : ∀ n ∈ pm.nodes.drop 361, (8050 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4876_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4876
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4876 149 (by decide) sdw_sm_4876
  have hp0 := sd_pm_faithful_eq initPM 8049 358 (by decide) sdw_pm_8049
  have hp1 := sd_pm_faithful_eq initPM 8050 361 (by decide) sdw_pm_8050
  have hd := recon_intermediateGoal_4876_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4876
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4877 : ∀ n ∈ sm.nodes.drop 138, (4877 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8051 : ∀ n ∈ pm.nodes.drop 335, (8051 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8052 : ∀ n ∈ pm.nodes.drop 339, (8052 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4877_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4877
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4877 138 (by decide) sdw_sm_4877
  have hp0 := sd_pm_faithful_eq initPM 8051 335 (by decide) sdw_pm_8051
  have hp1 := sd_pm_faithful_eq initPM 8052 339 (by decide) sdw_pm_8052
  have hd := recon_intermediateGoal_4877_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4877
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4879 : ∀ n ∈ sm.nodes.drop 142, (4879 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8055 : ∀ n ∈ pm.nodes.drop 343, (8055 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8056 : ∀ n ∈ pm.nodes.drop 347, (8056 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4879_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4879
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4879 142 (by decide) sdw_sm_4879
  have hp0 := sd_pm_faithful_eq initPM 8055 343 (by decide) sdw_pm_8055
  have hp1 := sd_pm_faithful_eq initPM 8056 347 (by decide) sdw_pm_8056
  have hd := recon_intermediateGoal_4879_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4879
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4880 : ∀ n ∈ sm.nodes.drop 146, (4880 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8061 : ∀ n ∈ pm.nodes.drop 351, (8061 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8062 : ∀ n ∈ pm.nodes.drop 355, (8062 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4880_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4880
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4880 146 (by decide) sdw_sm_4880
  have hp0 := sd_pm_faithful_eq initPM 8061 351 (by decide) sdw_pm_8061
  have hp1 := sd_pm_faithful_eq initPM 8062 355 (by decide) sdw_pm_8062
  have hd := recon_intermediateGoal_4880_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4880
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4881 : ∀ n ∈ sm.nodes.drop 150, (4881 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8063 : ∀ n ∈ pm.nodes.drop 359, (8063 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8064 : ∀ n ∈ pm.nodes.drop 362, (8064 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4881_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4881
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4881 150 (by decide) sdw_sm_4881
  have hp0 := sd_pm_faithful_eq initPM 8063 359 (by decide) sdw_pm_8063
  have hp1 := sd_pm_faithful_eq initPM 8064 362 (by decide) sdw_pm_8064
  have hd := recon_intermediateGoal_4881_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4881
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4882 : ∀ n ∈ sm.nodes.drop 139, (4882 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8065 : ∀ n ∈ pm.nodes.drop 336, (8065 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8066 : ∀ n ∈ pm.nodes.drop 340, (8066 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4882_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4882
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4882 139 (by decide) sdw_sm_4882
  have hp0 := sd_pm_faithful_eq initPM 8065 336 (by decide) sdw_pm_8065
  have hp1 := sd_pm_faithful_eq initPM 8066 340 (by decide) sdw_pm_8066
  have hd := recon_intermediateGoal_4882_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4882
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4884 : ∀ n ∈ sm.nodes.drop 143, (4884 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8069 : ∀ n ∈ pm.nodes.drop 344, (8069 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8070 : ∀ n ∈ pm.nodes.drop 348, (8070 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4884_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4884
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4884 143 (by decide) sdw_sm_4884
  have hp0 := sd_pm_faithful_eq initPM 8069 344 (by decide) sdw_pm_8069
  have hp1 := sd_pm_faithful_eq initPM 8070 348 (by decide) sdw_pm_8070
  have hd := recon_intermediateGoal_4884_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4884
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4885 : ∀ n ∈ sm.nodes.drop 147, (4885 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8079 : ∀ n ∈ pm.nodes.drop 352, (8079 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8080 : ∀ n ∈ pm.nodes.drop 356, (8080 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4885_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4885
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4885 147 (by decide) sdw_sm_4885
  have hp0 := sd_pm_faithful_eq initPM 8079 352 (by decide) sdw_pm_8079
  have hp1 := sd_pm_faithful_eq initPM 8080 356 (by decide) sdw_pm_8080
  have hd := recon_intermediateGoal_4885_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4885
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4886 : ∀ n ∈ sm.nodes.drop 140, (4886 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8083 : ∀ n ∈ pm.nodes.drop 337, (8083 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8084 : ∀ n ∈ pm.nodes.drop 341, (8084 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4886_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4886
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4886 140 (by decide) sdw_sm_4886
  have hp0 := sd_pm_faithful_eq initPM 8083 337 (by decide) sdw_pm_8083
  have hp1 := sd_pm_faithful_eq initPM 8084 341 (by decide) sdw_pm_8084
  have hd := recon_intermediateGoal_4886_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4886
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4888 : ∀ n ∈ sm.nodes.drop 144, (4888 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8087 : ∀ n ∈ pm.nodes.drop 345, (8087 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8088 : ∀ n ∈ pm.nodes.drop 349, (8088 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4888_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4888
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4888 144 (by decide) sdw_sm_4888
  have hp0 := sd_pm_faithful_eq initPM 8087 345 (by decide) sdw_pm_8087
  have hp1 := sd_pm_faithful_eq initPM 8088 349 (by decide) sdw_pm_8088
  have hd := recon_intermediateGoal_4888_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4888
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4889 : ∀ n ∈ sm.nodes.drop 148, (4889 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8097 : ∀ n ∈ pm.nodes.drop 353, (8097 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8098 : ∀ n ∈ pm.nodes.drop 357, (8098 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4889_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4889
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4889 148 (by decide) sdw_sm_4889
  have hp0 := sd_pm_faithful_eq initPM 8097 353 (by decide) sdw_pm_8097
  have hp1 := sd_pm_faithful_eq initPM 8098 357 (by decide) sdw_pm_8098
  have hd := recon_intermediateGoal_4889_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4889
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4890 : ∀ n ∈ sm.nodes.drop 151, (4890 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8101 : ∀ n ∈ pm.nodes.drop 360, (8101 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8102 : ∀ n ∈ pm.nodes.drop 363, (8102 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4890_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4890
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4890 151 (by decide) sdw_sm_4890
  have hp0 := sd_pm_faithful_eq initPM 8101 360 (by decide) sdw_pm_8101
  have hp1 := sd_pm_faithful_eq initPM 8102 363 (by decide) sdw_pm_8102
  have hd := recon_intermediateGoal_4890_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4890
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4891 : ∀ n ∈ sm.nodes.drop 152, (4891 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8103 : ∀ n ∈ pm.nodes.drop 364, (8103 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8104 : ∀ n ∈ pm.nodes.drop 365, (8104 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4891_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4891
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4891 152 (by decide) sdw_sm_4891
  have hp0 := sd_pm_faithful_eq initPM 8103 364 (by decide) sdw_pm_8103
  have hp1 := sd_pm_faithful_eq initPM 8104 365 (by decide) sdw_pm_8104
  have hd := recon_intermediateGoal_4891_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4891
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4893 : ∀ n ∈ sm.nodes.drop 153, (4893 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8109 : ∀ n ∈ pm.nodes.drop 366, (8109 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8110 : ∀ n ∈ pm.nodes.drop 367, (8110 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4893_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4893
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4893 153 (by decide) sdw_sm_4893
  have hp0 := sd_pm_faithful_eq initPM 8109 366 (by decide) sdw_pm_8109
  have hp1 := sd_pm_faithful_eq initPM 8110 367 (by decide) sdw_pm_8110
  have hd := recon_intermediateGoal_4893_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4893
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4894 : ∀ n ∈ sm.nodes.drop 154, (4894 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8119 : ∀ n ∈ pm.nodes.drop 368, (8119 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8120 : ∀ n ∈ pm.nodes.drop 369, (8120 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4894_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4894
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4894 154 (by decide) sdw_sm_4894
  have hp0 := sd_pm_faithful_eq initPM 8119 368 (by decide) sdw_pm_8119
  have hp1 := sd_pm_faithful_eq initPM 8120 369 (by decide) sdw_pm_8120
  have hd := recon_intermediateGoal_4894_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4894
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4895 : ∀ n ∈ sm.nodes.drop 155, (4895 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8123 : ∀ n ∈ pm.nodes.drop 370, (8123 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8124 : ∀ n ∈ pm.nodes.drop 371, (8124 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4895_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4895
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4895 155 (by decide) sdw_sm_4895
  have hp0 := sd_pm_faithful_eq initPM 8123 370 (by decide) sdw_pm_8123
  have hp1 := sd_pm_faithful_eq initPM 8124 371 (by decide) sdw_pm_8124
  have hd := recon_intermediateGoal_4895_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4895
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4896 : ∀ n ∈ sm.nodes.drop 156, (4896 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8127 : ∀ n ∈ pm.nodes.drop 372, (8127 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8128 : ∀ n ∈ pm.nodes.drop 373, (8128 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4896_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4896
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4896 156 (by decide) sdw_sm_4896
  have hp0 := sd_pm_faithful_eq initPM 8127 372 (by decide) sdw_pm_8127
  have hp1 := sd_pm_faithful_eq initPM 8128 373 (by decide) sdw_pm_8128
  have hd := recon_intermediateGoal_4896_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4896
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4897 : ∀ n ∈ sm.nodes.drop 157, (4897 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8133 : ∀ n ∈ pm.nodes.drop 374, (8133 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8134 : ∀ n ∈ pm.nodes.drop 375, (8134 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4897_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4897
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4897 157 (by decide) sdw_sm_4897
  have hp0 := sd_pm_faithful_eq initPM 8133 374 (by decide) sdw_pm_8133
  have hp1 := sd_pm_faithful_eq initPM 8134 375 (by decide) sdw_pm_8134
  have hd := recon_intermediateGoal_4897_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4897
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4898 : ∀ n ∈ sm.nodes.drop 158, (4898 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8137 : ∀ n ∈ pm.nodes.drop 376, (8137 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8138 : ∀ n ∈ pm.nodes.drop 377, (8138 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4898_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4898
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4898 158 (by decide) sdw_sm_4898
  have hp0 := sd_pm_faithful_eq initPM 8137 376 (by decide) sdw_pm_8137
  have hp1 := sd_pm_faithful_eq initPM 8138 377 (by decide) sdw_pm_8138
  have hd := recon_intermediateGoal_4898_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4898
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4900 : ∀ n ∈ sm.nodes.drop 160, (4900 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8141 : ∀ n ∈ pm.nodes.drop 380, (8141 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8142 : ∀ n ∈ pm.nodes.drop 381, (8142 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4900_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4900
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4900 160 (by decide) sdw_sm_4900
  have hp0 := sd_pm_faithful_eq initPM 8141 380 (by decide) sdw_pm_8141
  have hp1 := sd_pm_faithful_eq initPM 8142 381 (by decide) sdw_pm_8142
  have hd := recon_intermediateGoal_4900_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4900
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4902 : ∀ n ∈ sm.nodes.drop 162, (4902 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8143 : ∀ n ∈ pm.nodes.drop 384, (8143 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8144 : ∀ n ∈ pm.nodes.drop 387, (8144 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4902_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4902
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4902 162 (by decide) sdw_sm_4902
  have hp0 := sd_pm_faithful_eq initPM 8143 384 (by decide) sdw_pm_8143
  have hp1 := sd_pm_faithful_eq initPM 8144 387 (by decide) sdw_pm_8144
  have hd := recon_intermediateGoal_4902_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4902
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4904 : ∀ n ∈ sm.nodes.drop 163, (4904 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8155 : ∀ n ∈ pm.nodes.drop 385, (8155 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8156 : ∀ n ∈ pm.nodes.drop 388, (8156 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4904_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4904
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4904 163 (by decide) sdw_sm_4904
  have hp0 := sd_pm_faithful_eq initPM 8155 385 (by decide) sdw_pm_8155
  have hp1 := sd_pm_faithful_eq initPM 8156 388 (by decide) sdw_pm_8156
  have hd := recon_intermediateGoal_4904_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4904
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4906 : ∀ n ∈ sm.nodes.drop 164, (4906 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8165 : ∀ n ∈ pm.nodes.drop 386, (8165 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8166 : ∀ n ∈ pm.nodes.drop 389, (8166 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4906_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4906
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4906 164 (by decide) sdw_sm_4906
  have hp0 := sd_pm_faithful_eq initPM 8165 386 (by decide) sdw_pm_8165
  have hp1 := sd_pm_faithful_eq initPM 8166 389 (by decide) sdw_pm_8166
  have hd := recon_intermediateGoal_4906_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4906
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4908 : ∀ n ∈ sm.nodes.drop 165, (4908 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8177 : ∀ n ∈ pm.nodes.drop 390, (8177 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8178 : ∀ n ∈ pm.nodes.drop 391, (8178 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4908_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4908
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4908 165 (by decide) sdw_sm_4908
  have hp0 := sd_pm_faithful_eq initPM 8177 390 (by decide) sdw_pm_8177
  have hp1 := sd_pm_faithful_eq initPM 8178 391 (by decide) sdw_pm_8178
  have hd := recon_intermediateGoal_4908_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4908
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4909 : ∀ n ∈ sm.nodes.drop 165, (4909 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8179 : ∀ n ∈ pm.nodes.drop 390, (8179 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8180 : ∀ n ∈ pm.nodes.drop 391, (8180 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4909_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4909
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4909 165 (by decide) sdw_sm_4909
  have hp0 := sd_pm_faithful_eq initPM 8179 390 (by decide) sdw_pm_8179
  have hp1 := sd_pm_faithful_eq initPM 8180 391 (by decide) sdw_pm_8180
  have hd := recon_intermediateGoal_4909_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4909
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4912 : ∀ n ∈ sm.nodes.drop 166, (4912 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8181 : ∀ n ∈ pm.nodes.drop 392, (8181 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8182 : ∀ n ∈ pm.nodes.drop 393, (8182 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4912_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4912
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4912 166 (by decide) sdw_sm_4912
  have hp0 := sd_pm_faithful_eq initPM 8181 392 (by decide) sdw_pm_8181
  have hp1 := sd_pm_faithful_eq initPM 8182 393 (by decide) sdw_pm_8182
  have hd := recon_intermediateGoal_4912_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4912
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4913 : ∀ n ∈ sm.nodes.drop 167, (4913 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8183 : ∀ n ∈ pm.nodes.drop 394, (8183 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8184 : ∀ n ∈ pm.nodes.drop 395, (8184 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4913_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4913
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4913 167 (by decide) sdw_sm_4913
  have hp0 := sd_pm_faithful_eq initPM 8183 394 (by decide) sdw_pm_8183
  have hp1 := sd_pm_faithful_eq initPM 8184 395 (by decide) sdw_pm_8184
  have hd := recon_intermediateGoal_4913_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4913
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4914 : ∀ n ∈ sm.nodes.drop 168, (4914 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8189 : ∀ n ∈ pm.nodes.drop 396, (8189 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8190 : ∀ n ∈ pm.nodes.drop 397, (8190 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4914_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4914
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4914 168 (by decide) sdw_sm_4914
  have hp0 := sd_pm_faithful_eq initPM 8189 396 (by decide) sdw_pm_8189
  have hp1 := sd_pm_faithful_eq initPM 8190 397 (by decide) sdw_pm_8190
  have hd := recon_intermediateGoal_4914_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4914
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4916 : ∀ n ∈ sm.nodes.drop 169, (4916 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8193 : ∀ n ∈ pm.nodes.drop 398, (8193 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8194 : ∀ n ∈ pm.nodes.drop 399, (8194 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4916_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4916
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4916 169 (by decide) sdw_sm_4916
  have hp0 := sd_pm_faithful_eq initPM 8193 398 (by decide) sdw_pm_8193
  have hp1 := sd_pm_faithful_eq initPM 8194 399 (by decide) sdw_pm_8194
  have hd := recon_intermediateGoal_4916_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4916
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4917 : ∀ n ∈ sm.nodes.drop 170, (4917 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8203 : ∀ n ∈ pm.nodes.drop 400, (8203 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8204 : ∀ n ∈ pm.nodes.drop 401, (8204 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4917_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4917
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4917 170 (by decide) sdw_sm_4917
  have hp0 := sd_pm_faithful_eq initPM 8203 400 (by decide) sdw_pm_8203
  have hp1 := sd_pm_faithful_eq initPM 8204 401 (by decide) sdw_pm_8204
  have hd := recon_intermediateGoal_4917_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4917
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4918 : ∀ n ∈ sm.nodes.drop 171, (4918 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8207 : ∀ n ∈ pm.nodes.drop 402, (8207 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8208 : ∀ n ∈ pm.nodes.drop 403, (8208 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4918_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4918
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4918 171 (by decide) sdw_sm_4918
  have hp0 := sd_pm_faithful_eq initPM 8207 402 (by decide) sdw_pm_8207
  have hp1 := sd_pm_faithful_eq initPM 8208 403 (by decide) sdw_pm_8208
  have hd := recon_intermediateGoal_4918_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4918
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4919 : ∀ n ∈ sm.nodes.drop 172, (4919 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8211 : ∀ n ∈ pm.nodes.drop 404, (8211 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8212 : ∀ n ∈ pm.nodes.drop 405, (8212 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4919_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4919
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4919 172 (by decide) sdw_sm_4919
  have hp0 := sd_pm_faithful_eq initPM 8211 404 (by decide) sdw_pm_8211
  have hp1 := sd_pm_faithful_eq initPM 8212 405 (by decide) sdw_pm_8212
  have hd := recon_intermediateGoal_4919_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4919
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4921 : ∀ n ∈ sm.nodes.drop 174, (4921 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8215 : ∀ n ∈ pm.nodes.drop 408, (8215 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8216 : ∀ n ∈ pm.nodes.drop 409, (8216 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4921_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4921
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4921 174 (by decide) sdw_sm_4921
  have hp0 := sd_pm_faithful_eq initPM 8215 408 (by decide) sdw_pm_8215
  have hp1 := sd_pm_faithful_eq initPM 8216 409 (by decide) sdw_pm_8216
  have hd := recon_intermediateGoal_4921_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4921
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4922 : ∀ n ∈ sm.nodes.drop 176, (4922 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8217 : ∀ n ∈ pm.nodes.drop 412, (8217 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8218 : ∀ n ∈ pm.nodes.drop 416, (8218 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4922_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4922
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4922 176 (by decide) sdw_sm_4922
  have hp0 := sd_pm_faithful_eq initPM 8217 412 (by decide) sdw_pm_8217
  have hp1 := sd_pm_faithful_eq initPM 8218 416 (by decide) sdw_pm_8218
  have hd := recon_intermediateGoal_4922_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4922
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4924 : ∀ n ∈ sm.nodes.drop 180, (4924 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8223 : ∀ n ∈ pm.nodes.drop 420, (8223 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8224 : ∀ n ∈ pm.nodes.drop 424, (8224 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4924_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4924
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4924 180 (by decide) sdw_sm_4924
  have hp0 := sd_pm_faithful_eq initPM 8223 420 (by decide) sdw_pm_8223
  have hp1 := sd_pm_faithful_eq initPM 8224 424 (by decide) sdw_pm_8224
  have hd := recon_intermediateGoal_4924_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4924
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4925 : ∀ n ∈ sm.nodes.drop 184, (4925 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8225 : ∀ n ∈ pm.nodes.drop 428, (8225 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8226 : ∀ n ∈ pm.nodes.drop 432, (8226 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4925_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4925
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4925 184 (by decide) sdw_sm_4925
  have hp0 := sd_pm_faithful_eq initPM 8225 428 (by decide) sdw_pm_8225
  have hp1 := sd_pm_faithful_eq initPM 8226 432 (by decide) sdw_pm_8226
  have hd := recon_intermediateGoal_4925_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4925
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4926 : ∀ n ∈ sm.nodes.drop 184, (4926 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8227 : ∀ n ∈ pm.nodes.drop 428, (8227 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8228 : ∀ n ∈ pm.nodes.drop 432, (8228 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4926_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4926
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4926 184 (by decide) sdw_sm_4926
  have hp0 := sd_pm_faithful_eq initPM 8227 428 (by decide) sdw_pm_8227
  have hp1 := sd_pm_faithful_eq initPM 8228 432 (by decide) sdw_pm_8228
  have hd := recon_intermediateGoal_4926_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4926
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4930 : ∀ n ∈ sm.nodes.drop 188, (4930 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8235 : ∀ n ∈ pm.nodes.drop 436, (8235 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8236 : ∀ n ∈ pm.nodes.drop 439, (8236 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4930_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4930
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4930 188 (by decide) sdw_sm_4930
  have hp0 := sd_pm_faithful_eq initPM 8235 436 (by decide) sdw_pm_8235
  have hp1 := sd_pm_faithful_eq initPM 8236 439 (by decide) sdw_pm_8236
  have hd := recon_intermediateGoal_4930_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4930
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4931 : ∀ n ∈ sm.nodes.drop 177, (4931 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8237 : ∀ n ∈ pm.nodes.drop 413, (8237 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8238 : ∀ n ∈ pm.nodes.drop 417, (8238 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4931_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4931
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4931 177 (by decide) sdw_sm_4931
  have hp0 := sd_pm_faithful_eq initPM 8237 413 (by decide) sdw_pm_8237
  have hp1 := sd_pm_faithful_eq initPM 8238 417 (by decide) sdw_pm_8238
  have hd := recon_intermediateGoal_4931_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4931
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4933 : ∀ n ∈ sm.nodes.drop 181, (4933 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8241 : ∀ n ∈ pm.nodes.drop 421, (8241 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8242 : ∀ n ∈ pm.nodes.drop 425, (8242 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4933_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4933
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4933 181 (by decide) sdw_sm_4933
  have hp0 := sd_pm_faithful_eq initPM 8241 421 (by decide) sdw_pm_8241
  have hp1 := sd_pm_faithful_eq initPM 8242 425 (by decide) sdw_pm_8242
  have hd := recon_intermediateGoal_4933_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4933
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4934 : ∀ n ∈ sm.nodes.drop 185, (4934 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8247 : ∀ n ∈ pm.nodes.drop 429, (8247 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8248 : ∀ n ∈ pm.nodes.drop 433, (8248 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4934_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4934
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4934 185 (by decide) sdw_sm_4934
  have hp0 := sd_pm_faithful_eq initPM 8247 429 (by decide) sdw_pm_8247
  have hp1 := sd_pm_faithful_eq initPM 8248 433 (by decide) sdw_pm_8248
  have hd := recon_intermediateGoal_4934_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4934
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4935 : ∀ n ∈ sm.nodes.drop 189, (4935 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8249 : ∀ n ∈ pm.nodes.drop 437, (8249 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8250 : ∀ n ∈ pm.nodes.drop 440, (8250 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4935_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4935
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4935 189 (by decide) sdw_sm_4935
  have hp0 := sd_pm_faithful_eq initPM 8249 437 (by decide) sdw_pm_8249
  have hp1 := sd_pm_faithful_eq initPM 8250 440 (by decide) sdw_pm_8250
  have hd := recon_intermediateGoal_4935_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4935
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4936 : ∀ n ∈ sm.nodes.drop 178, (4936 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8251 : ∀ n ∈ pm.nodes.drop 414, (8251 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8252 : ∀ n ∈ pm.nodes.drop 418, (8252 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4936_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4936
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4936 178 (by decide) sdw_sm_4936
  have hp0 := sd_pm_faithful_eq initPM 8251 414 (by decide) sdw_pm_8251
  have hp1 := sd_pm_faithful_eq initPM 8252 418 (by decide) sdw_pm_8252
  have hd := recon_intermediateGoal_4936_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4936
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4938 : ∀ n ∈ sm.nodes.drop 182, (4938 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8255 : ∀ n ∈ pm.nodes.drop 422, (8255 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8256 : ∀ n ∈ pm.nodes.drop 426, (8256 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4938_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4938
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4938 182 (by decide) sdw_sm_4938
  have hp0 := sd_pm_faithful_eq initPM 8255 422 (by decide) sdw_pm_8255
  have hp1 := sd_pm_faithful_eq initPM 8256 426 (by decide) sdw_pm_8256
  have hd := recon_intermediateGoal_4938_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4938
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4939 : ∀ n ∈ sm.nodes.drop 186, (4939 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8265 : ∀ n ∈ pm.nodes.drop 430, (8265 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8266 : ∀ n ∈ pm.nodes.drop 434, (8266 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4939_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4939
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4939 186 (by decide) sdw_sm_4939
  have hp0 := sd_pm_faithful_eq initPM 8265 430 (by decide) sdw_pm_8265
  have hp1 := sd_pm_faithful_eq initPM 8266 434 (by decide) sdw_pm_8266
  have hd := recon_intermediateGoal_4939_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4939
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4940 : ∀ n ∈ sm.nodes.drop 179, (4940 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8269 : ∀ n ∈ pm.nodes.drop 415, (8269 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8270 : ∀ n ∈ pm.nodes.drop 419, (8270 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4940_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4940
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4940 179 (by decide) sdw_sm_4940
  have hp0 := sd_pm_faithful_eq initPM 8269 415 (by decide) sdw_pm_8269
  have hp1 := sd_pm_faithful_eq initPM 8270 419 (by decide) sdw_pm_8270
  have hd := recon_intermediateGoal_4940_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4940
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4942 : ∀ n ∈ sm.nodes.drop 183, (4942 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8273 : ∀ n ∈ pm.nodes.drop 423, (8273 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8274 : ∀ n ∈ pm.nodes.drop 427, (8274 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4942_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4942
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4942 183 (by decide) sdw_sm_4942
  have hp0 := sd_pm_faithful_eq initPM 8273 423 (by decide) sdw_pm_8273
  have hp1 := sd_pm_faithful_eq initPM 8274 427 (by decide) sdw_pm_8274
  have hd := recon_intermediateGoal_4942_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4942
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4943 : ∀ n ∈ sm.nodes.drop 187, (4943 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8283 : ∀ n ∈ pm.nodes.drop 431, (8283 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8284 : ∀ n ∈ pm.nodes.drop 435, (8284 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4943_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4943
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4943 187 (by decide) sdw_sm_4943
  have hp0 := sd_pm_faithful_eq initPM 8283 431 (by decide) sdw_pm_8283
  have hp1 := sd_pm_faithful_eq initPM 8284 435 (by decide) sdw_pm_8284
  have hd := recon_intermediateGoal_4943_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4943
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4944 : ∀ n ∈ sm.nodes.drop 190, (4944 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8287 : ∀ n ∈ pm.nodes.drop 438, (8287 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8288 : ∀ n ∈ pm.nodes.drop 441, (8288 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4944_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4944
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4944 190 (by decide) sdw_sm_4944
  have hp0 := sd_pm_faithful_eq initPM 8287 438 (by decide) sdw_pm_8287
  have hp1 := sd_pm_faithful_eq initPM 8288 441 (by decide) sdw_pm_8288
  have hd := recon_intermediateGoal_4944_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4944
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4945 : ∀ n ∈ sm.nodes.drop 191, (4945 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8289 : ∀ n ∈ pm.nodes.drop 442, (8289 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8290 : ∀ n ∈ pm.nodes.drop 443, (8290 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4945_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4945
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4945 191 (by decide) sdw_sm_4945
  have hp0 := sd_pm_faithful_eq initPM 8289 442 (by decide) sdw_pm_8289
  have hp1 := sd_pm_faithful_eq initPM 8290 443 (by decide) sdw_pm_8290
  have hd := recon_intermediateGoal_4945_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4945
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4947 : ∀ n ∈ sm.nodes.drop 192, (4947 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8295 : ∀ n ∈ pm.nodes.drop 444, (8295 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8296 : ∀ n ∈ pm.nodes.drop 445, (8296 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4947_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4947
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4947 192 (by decide) sdw_sm_4947
  have hp0 := sd_pm_faithful_eq initPM 8295 444 (by decide) sdw_pm_8295
  have hp1 := sd_pm_faithful_eq initPM 8296 445 (by decide) sdw_pm_8296
  have hd := recon_intermediateGoal_4947_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4947
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4948 : ∀ n ∈ sm.nodes.drop 193, (4948 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8305 : ∀ n ∈ pm.nodes.drop 446, (8305 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8306 : ∀ n ∈ pm.nodes.drop 447, (8306 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4948_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4948
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4948 193 (by decide) sdw_sm_4948
  have hp0 := sd_pm_faithful_eq initPM 8305 446 (by decide) sdw_pm_8305
  have hp1 := sd_pm_faithful_eq initPM 8306 447 (by decide) sdw_pm_8306
  have hd := recon_intermediateGoal_4948_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4948
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_4949 : ∀ n ∈ sm.nodes.drop 194, (4949 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8309 : ∀ n ∈ pm.nodes.drop 448, (8309 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8310 : ∀ n ∈ pm.nodes.drop 449, (8310 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4949_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4949
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 4949 194 (by decide) sdw_sm_4949
  have hp0 := sd_pm_faithful_eq initPM 8309 448 (by decide) sdw_pm_8309
  have hp1 := sd_pm_faithful_eq initPM 8310 449 (by decide) sdw_pm_8310
  have hd := recon_intermediateGoal_4949_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_4949
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
