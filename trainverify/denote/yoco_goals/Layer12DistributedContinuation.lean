/- Pure-distributed layer-12 pre-attention QKV continuation. -/
import denote.yoco_goals.Layer11DistributedContinuation

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l12d_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_rms_norm", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_rms_norm (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_rms_norm hk hn (by simp)
    (fun st => applyNode_fw_rms_norm_out_1p g st r x w o)
    hdn hdw hpn hpx hpw

private theorem l12d_per_head (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_per_head_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_per_head_linear hk hn (by simp)
    (fun st => applyNode_fw_per_head_mix_precision_linear_out g st r x w o [])
    hdn hdw hpn hpx hpw

private theorem l12d_rms5278_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5278)
      (denoteGraphDistributed pm initPM 9443) (denoteGraphDistributed pm initPM 9444)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5276 5276 9439 9440
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5276_distributed initSM initPM hSM hPM hInit)
  have ms := distributed_reduce1 sm initSM 431
    { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959], params := [2] }
    5276 7955 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5276 7955 7959)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 923
    { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641], params := [2] }
    9439 15637 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 9439 15637 15641)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 924
    { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649], params := [2] }
    9440 15645 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 9440 15645 15649)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hs0 : (denoteGraphDistributed pm initPM 15637).shape = [2048, 1024] := by
    rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15645).shape = [2048, 1024] := by
    rw [m1]; exact h.shard1_shape
  have hg : denoteGraphDistributed sm initSM 7955 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 15637, denoteGraphDistributed pm initPM 15645] := by
    rw [ms, h.value, ← m0, ← m1]
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5277
    (by native_decide) 5277 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l12d_rms sm initSM 432 0 7955 5277 5278
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_rms pm initPM 925 0 15637 5277 9443
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_rms pm initPM 926 1 15645 5277 9444
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hg, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      ← r0, ← r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP RMSNorm at the layer-12 boundary. -/
theorem recon_intermediateGoal_5278_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5278
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5278 5278 9443 9444
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_rms5278_rel initSM initPM hSM hPM hInit)

private theorem l12d_q5280_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5280)
      (denoteGraphDistributed pm initPM 9445) (denoteGraphDistributed pm initPM 9446)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l12d_rms5278_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 433
    { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
    5278 7964 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 5278 7964 7968 7972)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 927
    { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
    9443 15654 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 9443 15654 15658 15662)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 928
    { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
    9444 15667 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 9444 15667 15671 15675)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hs0 : (denoteGraphDistributed pm initPM 15654).shape = [2048, 1024] := by
    rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15667).shape = [2048, 1024] := by
    rw [m1]; exact h.shard1_shape
  have hg : denoteGraphDistributed sm initSM 7964 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 15654, denoteGraphDistributed pm initPM 15667] := by
    rw [ms, h.value, ← m0, ← m1]
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5279
    (by native_decide) 5279 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5279
    (by native_decide) 5279 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5279).shape = [16, 64, 1024] := by
    rw [← hw]; exact hws
  have rs := l12d_per_head sm initSM 434 0 7964 5279 5280
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_per_head pm initPM 929 0 15654 5279 9445
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_per_head pm initPM 932 1 15667 5279 9446
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hg, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, ← r0, ← r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64
      (by rw [ms]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs1 hpw

/-- Pure-distributed exact 2-TP layer-12 Q projection. -/
theorem recon_intermediateGoal_5280_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5280
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5280 5280 9445 9446
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l12d_q5280_rel initSM initPM hSM hPM hInit)

private theorem l12d_k5282_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5282)
      (denoteGraphDistributed pm initPM 9457) (denoteGraphDistributed pm initPM 9458)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l12d_rms5278_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 433
    { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
    5278 7968 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 5278 7964 7968 7972 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 927
    { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
    9443 15658 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 9443 15654 15658 15662 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 928
    { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
    9444 15671 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 9444 15667 15671 15675 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hs0 : (denoteGraphDistributed pm initPM 15658).shape = [2048, 1024] := by
    rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15671).shape = [2048, 1024] := by
    rw [m1]; exact h.shard1_shape
  have hg : denoteGraphDistributed sm initSM 7968 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 15658, denoteGraphDistributed pm initPM 15671] := by
    rw [ms, h.value, ← m0, ← m1]
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5281
    (by native_decide) 5281 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5281
    (by native_decide) 5281 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5281).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have rs := l12d_per_head sm initSM 435 0 7968 5281 5282
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_per_head pm initPM 930 0 15658 5281 9457
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_per_head pm initPM 933 1 15671 5281 9458
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hg, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, ← r0, ← r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64
      (by rw [ms]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP layer-12 K projection. -/
theorem recon_intermediateGoal_5282_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5282
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5282 5282 9457 9458
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l12d_k5282_rel initSM initPM hSM hPM hInit)

private theorem l12d_v5284_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5284)
      (denoteGraphDistributed pm initPM 9467) (denoteGraphDistributed pm initPM 9468)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l12d_rms5278_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 433
    { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }
    5278 7972 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 5278 7964 7968 7972 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 927
    { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }
    9443 15662 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 9443 15654 15658 15662 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 928
    { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }
    9444 15675 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 9444 15667 15671 15675 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hs0 : (denoteGraphDistributed pm initPM 15662).shape = [2048, 1024] := by
    rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15675).shape = [2048, 1024] := by
    rw [m1]; exact h.shard1_shape
  have hg : denoteGraphDistributed sm initSM 7972 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 15662, denoteGraphDistributed pm initPM 15675] := by
    rw [ms, h.value, ← m0, ← m1]
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5283
    (by native_decide) 5283 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5283
    (by native_decide) 5283 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5283).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have rs := l12d_per_head sm initSM 436 0 7972 5283 5284
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_per_head pm initPM 931 0 15662 5283 9467
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_per_head pm initPM 934 1 15675 5283 9468
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hg, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, ← r0, ← r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64
      (by rw [ms]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP layer-12 V projection. -/
theorem recon_intermediateGoal_5284_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5284
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5284 5284 9467 9468
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l12d_v5284_rel initSM initPM hSM hPM hInit)

#print axioms recon_intermediateGoal_5284_distributed

end TrainVerify.Denote.GeneratedPatterns
