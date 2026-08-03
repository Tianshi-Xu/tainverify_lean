/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.Layer8DistributedContinuation

/-!
# Self-decoder goals transported to the faithful track

Batch 0 of the goals originally proved in `Layer8DistributedContinuation.lean`. Each theorem reads its
`_distributed` counterpart through the region bridge; the sole per-goal
obligation is the not-written fact, decided on the generated graph.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5116 : ∀ n ∈ sm.nodes.drop 316, (5116 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8885 : ∀ n ∈ pm.nodes.drop 692, (8885 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8886 : ∀ n ∈ pm.nodes.drop 693, (8886 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5116_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5116
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5116 316 (by decide) sdw_sm_5116
  have hp0 := sd_pm_faithful_eq initPM 8885 692 (by decide) sdw_pm_8885
  have hp1 := sd_pm_faithful_eq initPM 8886 693 (by decide) sdw_pm_8886
  have hd := recon_intermediateGoal_5116_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5116
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5118 : ∀ n ∈ sm.nodes.drop 318, (5118 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8887 : ∀ n ∈ pm.nodes.drop 696, (8887 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8888 : ∀ n ∈ pm.nodes.drop 699, (8888 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5118_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5118
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5118 318 (by decide) sdw_sm_5118
  have hp0 := sd_pm_faithful_eq initPM 8887 696 (by decide) sdw_pm_8887
  have hp1 := sd_pm_faithful_eq initPM 8888 699 (by decide) sdw_pm_8888
  have hd := recon_intermediateGoal_5118_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5118
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5120 : ∀ n ∈ sm.nodes.drop 319, (5120 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8899 : ∀ n ∈ pm.nodes.drop 697, (8899 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8900 : ∀ n ∈ pm.nodes.drop 700, (8900 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5120_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5120
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5120 319 (by decide) sdw_sm_5120
  have hp0 := sd_pm_faithful_eq initPM 8899 697 (by decide) sdw_pm_8899
  have hp1 := sd_pm_faithful_eq initPM 8900 700 (by decide) sdw_pm_8900
  have hd := recon_intermediateGoal_5120_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5120
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5122 : ∀ n ∈ sm.nodes.drop 320, (5122 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8909 : ∀ n ∈ pm.nodes.drop 698, (8909 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8910 : ∀ n ∈ pm.nodes.drop 701, (8910 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5122_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5122
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5122 320 (by decide) sdw_sm_5122
  have hp0 := sd_pm_faithful_eq initPM 8909 698 (by decide) sdw_pm_8909
  have hp1 := sd_pm_faithful_eq initPM 8910 701 (by decide) sdw_pm_8910
  have hd := recon_intermediateGoal_5122_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5122
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5124 : ∀ n ∈ sm.nodes.drop 321, (5124 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8921 : ∀ n ∈ pm.nodes.drop 702, (8921 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8922 : ∀ n ∈ pm.nodes.drop 703, (8922 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5124_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5124
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5124 321 (by decide) sdw_sm_5124
  have hp0 := sd_pm_faithful_eq initPM 8921 702 (by decide) sdw_pm_8921
  have hp1 := sd_pm_faithful_eq initPM 8922 703 (by decide) sdw_pm_8922
  have hd := recon_intermediateGoal_5124_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5124
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5125 : ∀ n ∈ sm.nodes.drop 321, (5125 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8923 : ∀ n ∈ pm.nodes.drop 702, (8923 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8924 : ∀ n ∈ pm.nodes.drop 703, (8924 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5125_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5125
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5125 321 (by decide) sdw_sm_5125
  have hp0 := sd_pm_faithful_eq initPM 8923 702 (by decide) sdw_pm_8923
  have hp1 := sd_pm_faithful_eq initPM 8924 703 (by decide) sdw_pm_8924
  have hd := recon_intermediateGoal_5125_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5125
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5128 : ∀ n ∈ sm.nodes.drop 322, (5128 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8925 : ∀ n ∈ pm.nodes.drop 704, (8925 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8926 : ∀ n ∈ pm.nodes.drop 705, (8926 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5128_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5128
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5128 322 (by decide) sdw_sm_5128
  have hp0 := sd_pm_faithful_eq initPM 8925 704 (by decide) sdw_pm_8925
  have hp1 := sd_pm_faithful_eq initPM 8926 705 (by decide) sdw_pm_8926
  have hd := recon_intermediateGoal_5128_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5128
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5129 : ∀ n ∈ sm.nodes.drop 323, (5129 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8927 : ∀ n ∈ pm.nodes.drop 706, (8927 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8928 : ∀ n ∈ pm.nodes.drop 707, (8928 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5129_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5129
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5129 323 (by decide) sdw_sm_5129
  have hp0 := sd_pm_faithful_eq initPM 8927 706 (by decide) sdw_pm_8927
  have hp1 := sd_pm_faithful_eq initPM 8928 707 (by decide) sdw_pm_8928
  have hd := recon_intermediateGoal_5129_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5129
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5130 : ∀ n ∈ sm.nodes.drop 324, (5130 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8933 : ∀ n ∈ pm.nodes.drop 708, (8933 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8934 : ∀ n ∈ pm.nodes.drop 709, (8934 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5130_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5130
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5130 324 (by decide) sdw_sm_5130
  have hp0 := sd_pm_faithful_eq initPM 8933 708 (by decide) sdw_pm_8933
  have hp1 := sd_pm_faithful_eq initPM 8934 709 (by decide) sdw_pm_8934
  have hd := recon_intermediateGoal_5130_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5130
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5132 : ∀ n ∈ sm.nodes.drop 325, (5132 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8937 : ∀ n ∈ pm.nodes.drop 710, (8937 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8938 : ∀ n ∈ pm.nodes.drop 711, (8938 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5132_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5132
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5132 325 (by decide) sdw_sm_5132
  have hp0 := sd_pm_faithful_eq initPM 8937 710 (by decide) sdw_pm_8937
  have hp1 := sd_pm_faithful_eq initPM 8938 711 (by decide) sdw_pm_8938
  have hd := recon_intermediateGoal_5132_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5132
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5133 : ∀ n ∈ sm.nodes.drop 326, (5133 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8947 : ∀ n ∈ pm.nodes.drop 712, (8947 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8948 : ∀ n ∈ pm.nodes.drop 713, (8948 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5133_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5133
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5133 326 (by decide) sdw_sm_5133
  have hp0 := sd_pm_faithful_eq initPM 8947 712 (by decide) sdw_pm_8947
  have hp1 := sd_pm_faithful_eq initPM 8948 713 (by decide) sdw_pm_8948
  have hd := recon_intermediateGoal_5133_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5133
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5134 : ∀ n ∈ sm.nodes.drop 327, (5134 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8951 : ∀ n ∈ pm.nodes.drop 714, (8951 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8952 : ∀ n ∈ pm.nodes.drop 715, (8952 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5134_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5134
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5134 327 (by decide) sdw_sm_5134
  have hp0 := sd_pm_faithful_eq initPM 8951 714 (by decide) sdw_pm_8951
  have hp1 := sd_pm_faithful_eq initPM 8952 715 (by decide) sdw_pm_8952
  have hd := recon_intermediateGoal_5134_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5134
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5135 : ∀ n ∈ sm.nodes.drop 328, (5135 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8955 : ∀ n ∈ pm.nodes.drop 716, (8955 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8956 : ∀ n ∈ pm.nodes.drop 717, (8956 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5135_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5135
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5135 328 (by decide) sdw_sm_5135
  have hp0 := sd_pm_faithful_eq initPM 8955 716 (by decide) sdw_pm_8955
  have hp1 := sd_pm_faithful_eq initPM 8956 717 (by decide) sdw_pm_8956
  have hd := recon_intermediateGoal_5135_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5135
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5137 : ∀ n ∈ sm.nodes.drop 330, (5137 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8959 : ∀ n ∈ pm.nodes.drop 720, (8959 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8960 : ∀ n ∈ pm.nodes.drop 721, (8960 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5137_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5137
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5137 330 (by decide) sdw_sm_5137
  have hp0 := sd_pm_faithful_eq initPM 8959 720 (by decide) sdw_pm_8959
  have hp1 := sd_pm_faithful_eq initPM 8960 721 (by decide) sdw_pm_8960
  have hd := recon_intermediateGoal_5137_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5137
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5138 : ∀ n ∈ sm.nodes.drop 332, (5138 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8961 : ∀ n ∈ pm.nodes.drop 724, (8961 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8962 : ∀ n ∈ pm.nodes.drop 728, (8962 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5138_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5138
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5138 332 (by decide) sdw_sm_5138
  have hp0 := sd_pm_faithful_eq initPM 8961 724 (by decide) sdw_pm_8961
  have hp1 := sd_pm_faithful_eq initPM 8962 728 (by decide) sdw_pm_8962
  have hd := recon_intermediateGoal_5138_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5138
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5140 : ∀ n ∈ sm.nodes.drop 336, (5140 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8967 : ∀ n ∈ pm.nodes.drop 732, (8967 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8968 : ∀ n ∈ pm.nodes.drop 736, (8968 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5140_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5140
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5140 336 (by decide) sdw_sm_5140
  have hp0 := sd_pm_faithful_eq initPM 8967 732 (by decide) sdw_pm_8967
  have hp1 := sd_pm_faithful_eq initPM 8968 736 (by decide) sdw_pm_8968
  have hd := recon_intermediateGoal_5140_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5140
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5141 : ∀ n ∈ sm.nodes.drop 340, (5141 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8969 : ∀ n ∈ pm.nodes.drop 740, (8969 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8970 : ∀ n ∈ pm.nodes.drop 744, (8970 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5141_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5141
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5141 340 (by decide) sdw_sm_5141
  have hp0 := sd_pm_faithful_eq initPM 8969 740 (by decide) sdw_pm_8969
  have hp1 := sd_pm_faithful_eq initPM 8970 744 (by decide) sdw_pm_8970
  have hd := recon_intermediateGoal_5141_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5141
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5142 : ∀ n ∈ sm.nodes.drop 340, (5142 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8971 : ∀ n ∈ pm.nodes.drop 740, (8971 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8972 : ∀ n ∈ pm.nodes.drop 744, (8972 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5142_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5142
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5142 340 (by decide) sdw_sm_5142
  have hp0 := sd_pm_faithful_eq initPM 8971 740 (by decide) sdw_pm_8971
  have hp1 := sd_pm_faithful_eq initPM 8972 744 (by decide) sdw_pm_8972
  have hd := recon_intermediateGoal_5142_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5142
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5147 : ∀ n ∈ sm.nodes.drop 333, (5147 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8981 : ∀ n ∈ pm.nodes.drop 725, (8981 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8982 : ∀ n ∈ pm.nodes.drop 729, (8982 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5147_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5147
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5147 333 (by decide) sdw_sm_5147
  have hp0 := sd_pm_faithful_eq initPM 8981 725 (by decide) sdw_pm_8981
  have hp1 := sd_pm_faithful_eq initPM 8982 729 (by decide) sdw_pm_8982
  have hd := recon_intermediateGoal_5147_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5147
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5149 : ∀ n ∈ sm.nodes.drop 337, (5149 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8985 : ∀ n ∈ pm.nodes.drop 733, (8985 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8986 : ∀ n ∈ pm.nodes.drop 737, (8986 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5149_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5149
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5149 337 (by decide) sdw_sm_5149
  have hp0 := sd_pm_faithful_eq initPM 8985 733 (by decide) sdw_pm_8985
  have hp1 := sd_pm_faithful_eq initPM 8986 737 (by decide) sdw_pm_8986
  have hd := recon_intermediateGoal_5149_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5149
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5150 : ∀ n ∈ sm.nodes.drop 341, (5150 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8991 : ∀ n ∈ pm.nodes.drop 741, (8991 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8992 : ∀ n ∈ pm.nodes.drop 745, (8992 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5150_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5150
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5150 341 (by decide) sdw_sm_5150
  have hp0 := sd_pm_faithful_eq initPM 8991 741 (by decide) sdw_pm_8991
  have hp1 := sd_pm_faithful_eq initPM 8992 745 (by decide) sdw_pm_8992
  have hd := recon_intermediateGoal_5150_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5150
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5151 : ∀ n ∈ sm.nodes.drop 345, (5151 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8993 : ∀ n ∈ pm.nodes.drop 749, (8993 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8994 : ∀ n ∈ pm.nodes.drop 752, (8994 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5151_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5151
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5151 345 (by decide) sdw_sm_5151
  have hp0 := sd_pm_faithful_eq initPM 8993 749 (by decide) sdw_pm_8993
  have hp1 := sd_pm_faithful_eq initPM 8994 752 (by decide) sdw_pm_8994
  have hd := recon_intermediateGoal_5151_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5151
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5152 : ∀ n ∈ sm.nodes.drop 334, (5152 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8995 : ∀ n ∈ pm.nodes.drop 726, (8995 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8996 : ∀ n ∈ pm.nodes.drop 730, (8996 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5152_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5152
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5152 334 (by decide) sdw_sm_5152
  have hp0 := sd_pm_faithful_eq initPM 8995 726 (by decide) sdw_pm_8995
  have hp1 := sd_pm_faithful_eq initPM 8996 730 (by decide) sdw_pm_8996
  have hd := recon_intermediateGoal_5152_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5152
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5154 : ∀ n ∈ sm.nodes.drop 338, (5154 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_8999 : ∀ n ∈ pm.nodes.drop 734, (8999 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9000 : ∀ n ∈ pm.nodes.drop 738, (9000 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5154_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5154
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5154 338 (by decide) sdw_sm_5154
  have hp0 := sd_pm_faithful_eq initPM 8999 734 (by decide) sdw_pm_8999
  have hp1 := sd_pm_faithful_eq initPM 9000 738 (by decide) sdw_pm_9000
  have hd := recon_intermediateGoal_5154_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5154
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5155 : ∀ n ∈ sm.nodes.drop 342, (5155 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9009 : ∀ n ∈ pm.nodes.drop 742, (9009 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9010 : ∀ n ∈ pm.nodes.drop 746, (9010 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5155_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5155
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5155 342 (by decide) sdw_sm_5155
  have hp0 := sd_pm_faithful_eq initPM 9009 742 (by decide) sdw_pm_9009
  have hp1 := sd_pm_faithful_eq initPM 9010 746 (by decide) sdw_pm_9010
  have hd := recon_intermediateGoal_5155_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5155
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5156 : ∀ n ∈ sm.nodes.drop 335, (5156 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9013 : ∀ n ∈ pm.nodes.drop 727, (9013 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9014 : ∀ n ∈ pm.nodes.drop 731, (9014 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5156_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5156
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5156 335 (by decide) sdw_sm_5156
  have hp0 := sd_pm_faithful_eq initPM 9013 727 (by decide) sdw_pm_9013
  have hp1 := sd_pm_faithful_eq initPM 9014 731 (by decide) sdw_pm_9014
  have hd := recon_intermediateGoal_5156_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5156
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5158 : ∀ n ∈ sm.nodes.drop 339, (5158 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9017 : ∀ n ∈ pm.nodes.drop 735, (9017 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9018 : ∀ n ∈ pm.nodes.drop 739, (9018 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5158_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5158
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5158 339 (by decide) sdw_sm_5158
  have hp0 := sd_pm_faithful_eq initPM 9017 735 (by decide) sdw_pm_9017
  have hp1 := sd_pm_faithful_eq initPM 9018 739 (by decide) sdw_pm_9018
  have hd := recon_intermediateGoal_5158_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5158
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5159 : ∀ n ∈ sm.nodes.drop 343, (5159 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9027 : ∀ n ∈ pm.nodes.drop 743, (9027 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9028 : ∀ n ∈ pm.nodes.drop 747, (9028 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5159_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5159
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5159 343 (by decide) sdw_sm_5159
  have hp0 := sd_pm_faithful_eq initPM 9027 743 (by decide) sdw_pm_9027
  have hp1 := sd_pm_faithful_eq initPM 9028 747 (by decide) sdw_pm_9028
  have hd := recon_intermediateGoal_5159_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5159
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5160 : ∀ n ∈ sm.nodes.drop 346, (5160 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9031 : ∀ n ∈ pm.nodes.drop 750, (9031 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9032 : ∀ n ∈ pm.nodes.drop 753, (9032 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5160_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5160
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5160 346 (by decide) sdw_sm_5160
  have hp0 := sd_pm_faithful_eq initPM 9031 750 (by decide) sdw_pm_9031
  have hp1 := sd_pm_faithful_eq initPM 9032 753 (by decide) sdw_pm_9032
  have hd := recon_intermediateGoal_5160_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5160
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5161 : ∀ n ∈ sm.nodes.drop 347, (5161 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9033 : ∀ n ∈ pm.nodes.drop 754, (9033 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9034 : ∀ n ∈ pm.nodes.drop 755, (9034 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5161_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5161
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5161 347 (by decide) sdw_sm_5161
  have hp0 := sd_pm_faithful_eq initPM 9033 754 (by decide) sdw_pm_9033
  have hp1 := sd_pm_faithful_eq initPM 9034 755 (by decide) sdw_pm_9034
  have hd := recon_intermediateGoal_5161_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5161
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5163 : ∀ n ∈ sm.nodes.drop 348, (5163 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9039 : ∀ n ∈ pm.nodes.drop 756, (9039 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9040 : ∀ n ∈ pm.nodes.drop 757, (9040 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5163_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5163
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5163 348 (by decide) sdw_sm_5163
  have hp0 := sd_pm_faithful_eq initPM 9039 756 (by decide) sdw_pm_9039
  have hp1 := sd_pm_faithful_eq initPM 9040 757 (by decide) sdw_pm_9040
  have hd := recon_intermediateGoal_5163_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5163
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5164 : ∀ n ∈ sm.nodes.drop 349, (5164 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9049 : ∀ n ∈ pm.nodes.drop 758, (9049 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9050 : ∀ n ∈ pm.nodes.drop 759, (9050 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5164_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5164
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5164 349 (by decide) sdw_sm_5164
  have hp0 := sd_pm_faithful_eq initPM 9049 758 (by decide) sdw_pm_9049
  have hp1 := sd_pm_faithful_eq initPM 9050 759 (by decide) sdw_pm_9050
  have hd := recon_intermediateGoal_5164_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5164
    rfl hs hp0 hp1 hd

set_option maxRecDepth 1000000 in
private theorem sdw_sm_5165 : ∀ n ∈ sm.nodes.drop 350, (5165 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9053 : ∀ n ∈ pm.nodes.drop 760, (9053 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sdw_pm_9054 : ∀ n ∈ pm.nodes.drop 761, (9054 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_5165_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5165
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hs := sd_sm_faithful_eq initSM 5165 350 (by decide) sdw_sm_5165
  have hp0 := sd_pm_faithful_eq initPM 9053 760 (by decide) sdw_pm_9053
  have hp1 := sd_pm_faithful_eq initPM 9054 761 (by decide) sdw_pm_9054
  have hd := recon_intermediateGoal_5165_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_two_pieces pm.numRanks intermediateGoal_5165
    rfl hs hp0 hp1 hd

end

end TrainVerify.Denote.GeneratedPatterns
