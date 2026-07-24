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

/-! ### Layer-12 rotary and faithful sliding attention. -/

private theorem l12d_chunk (g : GraphDecl) (init : Store) (k r i o d : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.ChunkPrim", ins := [i], outs := [o], params := [d] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o =
      chunkPrimDimN d g.numRanks r (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fun t => chunkPrimDimN d g.numRanks r t)
    hk hn (by simp) (fun st => applyNode_chunkPrimDimN_out g st r i o d) hdn hdw hpn hpw

private theorem l12d_rotary_cache_11864 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11864 := by
  have _hindex : ((List.range 12).map (fun r => 11853 + r))[11]? = some 11864 := by
    native_decide
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11864 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11864 id (by native_decide) (by native_decide) (by decide)
      (fun st => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm st 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11864 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
private theorem l12d_rotary5286_5287_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5286)
      (denoteGraphDistributed pm initPM 9479) (denoteGraphDistributed pm initPM 9480)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 5287)
      (denoteGraphDistributed pm initPM 9481) (denoteGraphDistributed pm initPM 9482)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l12d_q5280_rel initSM initPM hSM hPM hInit
  have hk := l12d_k5282_rel initSM initPM hSM hPM hInit
  have hcache := l12d_rotary_cache_11864 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_5285
    (by native_decide) 5285 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_5285
    (by native_decide) 5285 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l12d_chunk pm initPM 11 0 5285 9477 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l12d_chunk pm initPM 24 1 5285 9478 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 9477 = chunkPrimDimN 0 2 0
      (denoteGraphDistributed pm initPM 5285) := c0
  have c1' : denoteGraphDistributed pm initPM 9478 = chunkPrimDimN 0 2 1
      (denoteGraphDistributed pm initPM 5285) := c1
  have qSM : denoteGraphDistributed sm initSM 5286 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5285)
        (denoteGraphDistributed sm initSM 5280) (denoteGraphDistributed sm initSM 5282) 16 4).1 := by
    rw [distributed_node_core sm initSM 437
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5285, 5280, 5282], outs := [5286, 5287], params := [16, 4] }
      5286 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 437 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 437 5285 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 437 5280 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 437 5282 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 5287 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5285)
        (denoteGraphDistributed sm initSM 5280) (denoteGraphDistributed sm initSM 5282) 16 4).2 := by
    rw [distributed_node_core sm initSM 437
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5285, 5280, 5282], outs := [5286, 5287], params := [16, 4] }
      5287 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5285 5280 5282 5286 5287 (by decide),
      distributed_prefix_read sm initSM 437 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 437 5285 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 437 5280 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 437 5282 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 9479 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11864) (denoteGraphDistributed pm initPM 9477)
        (denoteGraphDistributed pm initPM 9445) (denoteGraphDistributed pm initPM 9457) 16 4).1 := by
    rw [distributed_node_core pm initPM 935
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11864, 9477, 9445, 9457], outs := [9479, 9481], params := [16, 4] }
      9479 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 935 11864 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 935 9477 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 935 9445 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 935 9457 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 9481 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11864) (denoteGraphDistributed pm initPM 9477)
        (denoteGraphDistributed pm initPM 9445) (denoteGraphDistributed pm initPM 9457) 16 4).2 := by
    rw [distributed_node_core pm initPM 935
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11864, 9477, 9445, 9457], outs := [9479, 9481], params := [16, 4] }
      9481 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11864 9477 9445 9457 9479 9481 (by decide),
      distributed_prefix_read pm initPM 935 11864 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 935 9477 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 935 9445 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 935 9457 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 9480 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11864) (denoteGraphDistributed pm initPM 9478)
        (denoteGraphDistributed pm initPM 9446) (denoteGraphDistributed pm initPM 9458) 16 4).1 := by
    rw [distributed_node_core pm initPM 936
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11864, 9478, 9446, 9458], outs := [9480, 9482], params := [16, 4] }
      9480 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 936 11864 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 936 9478 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 936 9446 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 936 9458 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 9482 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11864) (denoteGraphDistributed pm initPM 9478)
        (denoteGraphDistributed pm initPM 9446) (denoteGraphDistributed pm initPM 9458) 16 4).2 := by
    rw [distributed_node_core pm initPM 936
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11864, 9478, 9446, 9458], outs := [9480, 9482], params := [16, 4] }
      9482 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11864 9478 9446 9458 9480 9482 (by decide),
      distributed_prefix_read pm initPM 936 11864 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 936 9478 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 936 9446 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 936 9458 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 5286 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9479, denoteGraphDistributed pm initPM 9480] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5285) (denoteGraphDistributed pm initPM 9445)
      (denoteGraphDistributed pm initPM 9446) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 5287 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9481, denoteGraphDistributed pm initPM 9482] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5285) (denoteGraphDistributed pm initPM 9457)
      (denoteGraphDistributed pm initPM 9458) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 9479).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 9480).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 9481).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 9482).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Pure-distributed exact 2-TP layer-12 rotary Q output. -/
theorem recon_intermediateGoal_5286_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5286
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5286 5286 9479 9480
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l12d_rotary5286_5287_rels initSM initPM hSM hPM hInit).1

/-- Pure-distributed exact 2-TP layer-12 rotary K output. -/
theorem recon_intermediateGoal_5287_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5287
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5287 5287 9481 9482
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l12d_rotary5286_5287_rels initSM initPM hSM hPM hInit).2

private def layer12SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5286, 5287, 5284, 5288, 5289], outs := [5290],
    params := [16, 4, 64, 64, 1, 512] }
private def layer12PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [9479, 9481, 9467, 5288, 5289], outs := [9483],
    params := [16, 4, 64, 64, 1, 512] }
private def layer12PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [9480, 9482, 9468, 5288, 5289], outs := [9484],
    params := [16, 4, 64, 64, 1, 512] }

set_option maxRecDepth 1000000 in
private theorem layer12_sm_sliding_node438 :
    sm.nodes[438]'(by native_decide) = layer12SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_sliding_node937 :
    pm.nodes[937]'(by native_decide) = layer12PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_sliding_node938 :
    pm.nodes[938]'(by native_decide) = layer12PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_sm_sliding_buddy :
    ringAttnBuddies sm layer12SmSliding = [layer12SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_sliding_buddy0 :
    ringAttnBuddies pm layer12PmSliding0 = [layer12PmSliding0, layer12PmSliding1] := by
  native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_sliding_buddy1 :
    ringAttnBuddies pm layer12PmSliding1 = [layer12PmSliding0, layer12PmSliding1] := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful pure-distributed exact 2-TP layer-12 sliding-window attention output. -/
theorem recon_intermediateGoal_5290_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5290
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have q := l12d_rotary5286_5287_rels initSM initPM hSM hPM hInit |>.1
  have k := l12d_rotary5286_5287_rels initSM initPM hSM hPM hInit |>.2
  have v := l12d_v5284_rel initSM initPM hSM hPM hInit
  have hcu5288 := distributed_init_singleton_value initSM initPM hInit initGoal_5288
    (by native_decide) 5288 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu5289 := distributed_init_singleton_value initSM initPM hInit initGoal_5289
    (by native_decide) 5289 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 438).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 937).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 938).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 438, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 438, t ∉ n.outs) :
      fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 438 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 937, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 937, t ∉ n.outs) :
      fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 937 t hn hw
  have hqfull : fs 5286 = allGatherPrimDimN 0 2 0 [fp 9479, fp 9480] := by
    rw [bs 5286 (by native_decide) (by native_decide),
      bp 9479 (by native_decide) (by native_decide),
      bp 9480 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 5287 = allGatherPrimDimN 0 2 0 [fp 9481, fp 9482] := by
    rw [bs 5287 (by native_decide) (by native_decide),
      bp 9481 (by native_decide) (by native_decide),
      bp 9482 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 5284 = allGatherPrimDimN 0 2 0 [fp 9467, fp 9468] := by
    rw [bs 5284 (by native_decide) (by native_decide),
      bp 9467 (by native_decide) (by native_decide),
      bp 9468 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer12SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 5286).shape.length
    rw [bs 5286 (by native_decide) (by native_decide), q.full_shape]
    decide
  have hkpos : 0 < (fs (layer12SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 5287).shape.length
    rw [bs 5287 (by native_decide) (by native_decide), k.full_shape]
    decide
  have hvpos : 0 < (fs (layer12SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 5284).shape.length
    rw [bs 5284 (by native_decide) (by native_decide), v.full_shape]
    decide
  have hcuQ : fs 5288 = fp 5288 := by
    rw [bs 5288 (by native_decide) (by native_decide),
      bp 5288 (by native_decide) (by native_decide), hcu5288]
  have hcuK : fs 5289 = fp 5289 := by
    rw [bs 5289 (by native_decide) (by native_decide),
      bp 5289 (by native_decide) (by native_decide), hcu5289]
  have e9479 : fp 9479 = fp' 9479 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9479 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have e9480 : fp 9480 = fp' 9480 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9480 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have e9481 : fp 9481 = fp' 9481 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9481 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have e9482 : fp 9482 = fp' 9482 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9482 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have e9467 : fp 9467 = fp' 9467 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9467 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have e9468 : fp 9468 = fp' 9468 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9468 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have e5288 : fp 5288 = fp' 5288 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5288 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have e5289 : fp 5289 = fp' 5289 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5289 937 938
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer12PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer12PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer12_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9479
      · exact e9480
    · rw [layer12_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9481
      · exact e9482
    · rw [layer12_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9467
      · exact e9468
    · exact e5288
    · exact e5289
  have rSM : denoteGraphDistributed sm initSM 5290 =
      applyNodeRingAttn_sliding_window sm fs layer12SmSliding := by
    rw [distributed_node_core sm initSM 438 layer12SmSliding 5290 (by native_decide)
      layer12_sm_sliding_node438 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5286 5287 5284 5288 5289 5290
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 9483 =
      applyNodeRingAttn_sliding_window pm fp layer12PmSliding0 := by
    rw [distributed_node_core pm initPM 937 layer12PmSliding0 9483 (by native_decide)
      layer12_pm_sliding_node937 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 9479 9481 9467 5288 5289 9483
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 9484 =
      applyNodeRingAttn_sliding_window pm fp' layer12PmSliding1 := by
    rw [distributed_node_core pm initPM 938 layer12PmSliding1 9484 (by native_decide)
      layer12_pm_sliding_node938 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 9480 9482 9468 5288 5289 9484
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9479, fp 9480])
      (allGatherPrimDimN 0 2 0 [fp 9481, fp 9482])
      (allGatherPrimDimN 0 2 0 [fp 9467, fp 9468])
      (fp 5288) (fp 5289) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 5286 (by native_decide) (by native_decide), q.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9479, fp' 9480])
      (allGatherPrimDimN 0 2 0 [fp' 9481, fp' 9482])
      (allGatherPrimDimN 0 2 0 [fp' 9467, fp' 9468])
      (fp' 5288) (fp' 5289) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9479, ← e9480, ← e9481, ← e9482, ← e9467, ← e9468,
      ← e5288, ← e5289]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_5290
    layer12SmSliding layer12PmSliding0 layer12PmSliding1 fs fp fp' 5290 9483 9484
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer12_sm_sliding_buddy layer12_pm_sliding_buddy0 layer12_pm_sliding_buddy1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

/-! ### Layer-12 post-attention projection and residual. -/

private theorem l12d_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
    (tl : List Nat) (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l12d_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
    (tl : List Nat) (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l12d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o)
    hdn hdw hpn hpx hpw

private theorem l12d_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = denoteGraphDistributed g init i := by
  have h := distributed_reduce1 g init k _ i o id hk hn (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l12d_reshape5291_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5291)
      (denoteGraphDistributed pm initPM 9485) (denoteGraphDistributed pm initPM 9486)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5290 5290 9483 9484
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5290_distributed initSM initPM hSM hPM hInit)
  have rs := l12d_reshape sm initSM 439 0 5290 5291 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12d_reshape pm initPM 939 0 9483 9485 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12d_reshape pm initPM 940 1 9484 9486 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, by rw [rs]; rfl, by rw [r0]; rfl, by rw [r1]; rfl, by decide⟩
  rw [rs, h.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape,
    r0, r1]

/-- Pure-distributed exact 2-TP layer-12 attention-output reshape. -/
theorem recon_intermediateGoal_5291_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5291
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5291 5291 9485 9486
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_reshape5291_rel initSM initPM hSM hPM hInit)

private theorem l12d_reshape5292_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5292)
      (denoteGraphDistributed pm initPM 9491) (denoteGraphDistributed pm initPM 9492)
      [4096, 1024] [2048, 1024] := by
  have h := l12d_reshape5291_rel initSM initPM hSM hPM hInit
  have rs := l12d_reshape sm initSM 440 0 5291 5292 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12d_reshape pm initPM 941 0 9485 9491 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12d_reshape pm initPM 942 1 9486 9492 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5292 = denoteGraphDistributed sm initSM 5291 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9491 = denoteGraphDistributed pm initPM 9485 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9492 = denoteGraphDistributed pm initPM 9486 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP layer-12 identity reshape. -/
theorem recon_intermediateGoal_5292_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5292
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5292 5292 9491 9492
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_reshape5292_rel initSM initPM hSM hPM hInit)

private theorem l12d_linear5294_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5294)
      (denoteGraphDistributed pm initPM 9495) (denoteGraphDistributed pm initPM 9496)
      [4096, 1024] [2048, 1024] := by
  have h := l12d_reshape5292_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5293
    (by native_decide) 5293 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5293
    (by native_decide) 5293 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5293).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l12d_linear sm initSM 441 0 5292 5293 5294 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_linear pm initPM 943 0 9491 5293 9495 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_linear pm initPM 944 1 9492 5293 9496 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP layer-12 output projection. -/
theorem recon_intermediateGoal_5294_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5294
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5294 5294 9495 9496
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_linear5294_rel initSM initPM hSM hPM hInit)

private theorem l12d_view5295_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5295)
      (denoteGraphDistributed pm initPM 9505) (denoteGraphDistributed pm initPM 9506)
      [4096, 1024] [2048, 1024] := by
  have h := l12d_linear5294_rel initSM initPM hSM hPM hInit
  have rs := l12d_view sm initSM 442 0 5294 5295 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12d_view pm initPM 945 0 9495 9505 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12d_view pm initPM 946 1 9496 9506 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5295 = denoteGraphDistributed sm initSM 5294 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9505 = denoteGraphDistributed pm initPM 9495 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9506 = denoteGraphDistributed pm initPM 9496 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP layer-12 identity view. -/
theorem recon_intermediateGoal_5295_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5295
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5295 5295 9505 9506
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_view5295_rel initSM initPM hSM hPM hInit)

private theorem l12d_float5296_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5296)
      (denoteGraphDistributed pm initPM 9509) (denoteGraphDistributed pm initPM 9510)
      [4096, 1024] [2048, 1024] := by
  have h := l12d_view5295_rel initSM initPM hSM hPM hInit
  have rs := l12d_float sm initSM 443 0 5295 5296 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_float pm initPM 947 0 9505 9509 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_float pm initPM 948 1 9506 9510 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP layer-12 post-projection float. -/
theorem recon_intermediateGoal_5296_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5296
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5296 5296 9509 9510
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_float5296_rel initSM initPM hSM hPM hInit)

private theorem l12d_carry7959_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7959)
      (denoteGraphDistributed pm initPM 15641) (denoteGraphDistributed pm initPM 15649)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5276 5276 9439 9440
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5276_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 431
    { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959], params := [2] }
    5276 7959 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5276 7955 7959 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 923
    { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641], params := [2] }
    9439 15641 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 9439 15637 15641 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 924
    { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649], params := [2] }
    9440 15649 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 9440 15645 15649 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, ← r0, ← r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP layer-12 cross-block residual carry. -/
theorem recon_intermediateGoal_7959_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7959
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7959 7959 15641 15649
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_carry7959_rel initSM initPM hSM hPM hInit)

/-- Pure-distributed residual add completing the layer-12 post-attention cascade. -/
theorem recon_intermediateGoal_5297_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5297
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := l12d_carry7959_rel initSM initPM hSM hPM hInit
  have hb := l12d_float5296_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce2 sm initSM 444
    { rank := 0, op := "OpName.FW_add", ins := [7959, 5296], outs := [5297] }
    7959 5296 5297 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 7959 5296 5297)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 949
    { rank := 0, op := "OpName.FW_add", ins := [15641, 9509], outs := [9513] }
    15641 9509 9513 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 15641 9509 9513)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 950
    { rank := 1, op := "OpName.FW_add", ins := [15649, 9510], outs := [9514] }
    15649 9510 9514 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 15649 9510 9514)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5297 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 9513, denoteGraphDistributed pm initPM 9514] := by
    rw [rs, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← r0, ← r1]
  have hs0 : (denoteGraphDistributed pm initPM 9513).shape = [2048, 1024] := by
    rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 9514).shape = [2048, 1024] := by
    rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5297).shape = [4096, 1024] := by
    rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5297 5297 9513 9514
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    ⟨hv, hs, hs0, hs1, by decide⟩

/-! ### Layer-12 router front. -/

private theorem l12d_norm_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_norm_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o = fw_norm_linear (denoteGraphDistributed g init x)
      (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_norm_linear hk hn (by simp)
    (fun st => applyNode_fw_norm_linear_out g st r x w o) hdn hdw hpn hpx hpw

private theorem l12d_rms5299_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5299) (denoteGraphDistributed pm initPM 9517)
      (denoteGraphDistributed pm initPM 9518) [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5297 5297 9513 9514
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5297_distributed initSM initPM hSM hPM hInit)
  have ms := distributed_reduce1 sm initSM 445
    { rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] }
    5297 7976 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5297 7976 7980)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 951
    { rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683], params := [2] }
    9513 15679 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 9513 15679 15683)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 952
    { rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691], params := [2] }
    9514 15687 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 9514 15687 15691)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5298
    (by native_decide) 5298 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l12d_rms sm initSM 446 0 7976 5298 5299 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_rms pm initPM 953 0 15679 5298 9517 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_rms pm initPM 954 1 15687 5298 9518 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15679).shape = [2048, 1024] := by rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15687).shape = [2048, 1024] := by rw [m1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ms, h.value, ← m0, ← m1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1, ← r0, ← r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed layer-12 RMSNorm of the first residual copy. -/
theorem recon_intermediateGoal_5299_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5299
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5299 5299 9517 9518
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_rms5299_rel initSM initPM hSM hPM hInit)

private theorem l12d_float5300_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5300)
      (denoteGraphDistributed pm initPM 9519) (denoteGraphDistributed pm initPM 9520)
      [4096, 1024] [2048, 1024] := by
  have h := l12d_rms5299_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 447
    { rank := 0, op := "OpName.FW_multiref", ins := [5299],
      outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
    5299 7987 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' sm st 0 4 5299 7987 [7991, 7995, 7999, 8003])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 955
    { rank := 0, op := "OpName.FW_multiref", ins := [9517],
      outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
    9517 15698 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 0 4 9517 15698 [15702, 15706, 15710, 15714])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 956
    { rank := 1, op := "OpName.FW_multiref", ins := [9518],
      outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
    9518 15721 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 1 4 9518 15721 [15725, 15729, 15733, 15737])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have rs := l12d_float sm initSM 448 0 7987 5300
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12d_float pm initPM 957 0 15698 9519
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12d_float pm initPM 961 1 15721 9520
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  exact ⟨by rw [rs, ms, h.value, ← m0, ← m1, ← r0, ← r1],
    by rw [rs, ms]; exact h.full_shape, by rw [r0, m0]; exact h.shard0_shape,
    by rw [r1, m1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed first router float input. -/
theorem recon_intermediateGoal_5300_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5300
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5300 5300 9519 9520
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12d_float5300_rel initSM initPM hSM hPM hInit)

private theorem l12d_linear5302_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5302)
      (denoteGraphDistributed pm initPM 9525) (denoteGraphDistributed pm initPM 9526)
      [4096, 64] [2048, 64] := by
  have h := l12d_float5300_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5301
    (by native_decide) 5301 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5301
    (by native_decide) 5301 [64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5301).shape = [64, 1024] := by
    rw [← hw]; exact hws
  have rs := l12d_norm_linear sm initSM 452 0 5300 5301 5302
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12d_norm_linear pm initPM 965 0 9519 5301 9525
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12d_norm_linear pm initPM 969 1 9520 5301 9526
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      ← r0, ← r1]
  · rw [rs]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) h.full_shape hws
  · rw [r0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard0_shape hpw
  · rw [r1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard1_shape hpw

/-- Pure-distributed layer-12 router logits. -/
theorem recon_intermediateGoal_5302_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5302
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5302 5302 9525 9526
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l12d_linear5302_rel initSM initPM hSM hPM hInit)

private theorem l12d_topk_common (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5302)
      (denoteGraphDistributed pm initPM 9525) (denoteGraphDistributed pm initPM 9526)
      [4096, 64] [2048, 64]
    ∧ ((sm.nodes.take 456).foldl (applyNodeDistributed sm) initSM 5302).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 973).foldl (applyNodeDistributed pm) initPM 9525).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 977).foldl (applyNodeDistributed pm) initPM 9526).shape.reverse.head? = some 64 := by
  have h := l12d_linear5302_rel initSM initPM hSM hPM hInit
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [foldl_take_distributed_eq sm initSM 5302 456 (by native_decide) (by native_decide),
      h.full_shape]
    rfl
  · rw [foldl_take_distributed_eq pm initPM 9525 973 (by native_decide) (by native_decide),
      h.shard0_shape]
    rfl
  · rw [foldl_take_distributed_eq pm initPM 9526 977 (by native_decide) (by native_decide),
      h.shard1_shape]
    rfl

private theorem l12d_topk_fst (g : GraphDecl) (init : Store) (k r i o0 o1 o2 : Nat)
    (hlast : ((g.nodes.take k).foldl (applyNodeDistributed g) init i).shape.reverse.head? = some 64)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_topk_routing", ins := [i], outs := [o0, o1, o2], params := [8, 1] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o0 ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o0 = (fw_topk_routing (denoteGraphDistributed g init i) 8 64).1 :=
  distributed_reduce_fixed_one g init k _ i o0 (fun t => (fw_topk_routing t 8 64).1)
    hk hn (by simp)
    (applyNode_topk81_fst g ((g.nodes.take k).foldl (applyNodeDistributed g) init)
      r i o0 o1 o2 hlast) hdn hdw hpn hpw

private theorem l12d_topk_snd (g : GraphDecl) (init : Store) (k r i o0 o1 o2 : Nat)
    (hlast : ((g.nodes.take k).foldl (applyNodeDistributed g) init i).shape.reverse.head? = some 64)
    (hneq : o0 ≠ o1)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_topk_routing", ins := [i], outs := [o0, o1, o2], params := [8, 1] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o1 ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o1 = (fw_topk_routing (denoteGraphDistributed g init i) 8 64).2.1 :=
  distributed_reduce_fixed_one g init k _ i o1 (fun t => (fw_topk_routing t 8 64).2.1)
    hk hn (by simp)
    (applyNode_topk81_snd g ((g.nodes.take k).foldl (applyNodeDistributed g) init)
      r i o0 o1 o2 hneq hlast) hdn hdw hpn hpw

/-- Pure-distributed layer-12 top-k routing probabilities. -/
theorem recon_intermediateGoal_5303_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5303
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  obtain ⟨h, hs, h0, h1⟩ := l12d_topk_common initSM initPM hSM hPM hInit
  have rs := l12d_topk_fst sm initSM 456 0 5302 5303 5304 5305 hs
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12d_topk_fst pm initPM 973 0 9525 9527 9529 9531 h0
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12d_topk_fst pm initPM 977 1 9526 9528 9530 9532 h1
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5303 5303 9527 9528
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Pure-distributed layer-12 top-k routing map. -/
theorem recon_intermediateGoal_5304_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5304
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  obtain ⟨h, hs, h0, h1⟩ := l12d_topk_common initSM initPM hSM hPM hInit
  have rs := l12d_topk_snd sm initSM 456 0 5302 5303 5304 5305 hs (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12d_topk_snd pm initPM 973 0 9525 9527 9529 9531 h0 (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12d_topk_snd pm initPM 977 1 9526 9528 9530 9532 h1 (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5304 5304 9529 9530
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

end TrainVerify.Denote.GeneratedPatterns
