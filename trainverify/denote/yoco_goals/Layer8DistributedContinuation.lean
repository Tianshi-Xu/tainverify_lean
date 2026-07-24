/- Pure-distributed layer-8 pre-attention continuation from public goal 5114. -/
import denote.yoco_goals.Layer7DistributedContinuation

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l8d_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
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
    (fun st => applyNode_fw_rms_norm_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l8d_per_head_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l8d_5116_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5116)
      (denoteGraphDistributed pm initPM 8885) (denoteGraphDistributed pm initPM 8886)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5114 5114 8881 8882
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5114_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 314
    { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803], params := [2] }
    5114 7799 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5114 7799 7803)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 689
    { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329], params := [2] }
    8881 15325 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8881 15325 15329)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 690
    { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337], params := [2] }
    8882 15333 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8882 15333 15337)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5115
    (by native_decide) 5115 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l8d_rms sm initSM 315 0 7799 5115 5116 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_rms pm initPM 691 0 15325 5115 8885 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_rms pm initPM 692 1 15333 5115 8886 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15325).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15333).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP layer-8 pre-attention RMSNorm. -/
theorem recon_intermediateGoal_5116_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5116
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5116 5116 8885 8886
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_5116_rel initSM initPM hSM hPM hInit)

private theorem l8d_5118_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5118)
      (denoteGraphDistributed pm initPM 8887) (denoteGraphDistributed pm initPM 8888)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l8d_5116_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 316
    { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
    5116 7808 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 5116 7808 7812 7816)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 693
    { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
    8885 15342 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 8885 15342 15346 15350)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 694
    { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
    8886 15355 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 8886 15355 15359 15363)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5117
    (by native_decide) 5117 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5117
    (by native_decide) 5117 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5117).shape = [16, 64, 1024] := by rw [← hw]; exact hws
  have rs := l8d_per_head_linear sm initSM 317 0 7808 5117 5118 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_per_head_linear pm initPM 695 0 15342 5117 8887 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_per_head_linear pm initPM 698 1 15355 5117 8888 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15342).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15355).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs1 hpw

/-- Pure-distributed exact 2-TP layer-8 Q projection. -/
theorem recon_intermediateGoal_5118_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5118
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5118 5118 8887 8888
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l8d_5118_rel initSM initPM hSM hPM hInit)

private theorem l8d_5120_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5120)
      (denoteGraphDistributed pm initPM 8899) (denoteGraphDistributed pm initPM 8900)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l8d_5116_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 316
    { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
    5116 7812 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 5116 7808 7812 7816 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 693
    { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
    8885 15346 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 8885 15342 15346 15350 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 694
    { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
    8886 15359 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 8886 15355 15359 15363 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5119
    (by native_decide) 5119 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5119
    (by native_decide) 5119 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5119).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l8d_per_head_linear sm initSM 318 0 7812 5119 5120 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_per_head_linear pm initPM 696 0 15346 5119 8899 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_per_head_linear pm initPM 699 1 15359 5119 8900 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15346).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15359).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP layer-8 K projection. -/
theorem recon_intermediateGoal_5120_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5120
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5120 5120 8899 8900
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l8d_5120_rel initSM initPM hSM hPM hInit)

private theorem l8d_5122_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5122)
      (denoteGraphDistributed pm initPM 8909) (denoteGraphDistributed pm initPM 8910)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l8d_5116_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 316
    { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }
    5116 7816 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 5116 7808 7812 7816 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 693
    { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }
    8885 15350 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 8885 15342 15346 15350 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 694
    { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }
    8886 15363 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 8886 15355 15359 15363 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5121
    (by native_decide) 5121 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5121
    (by native_decide) 5121 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5121).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l8d_per_head_linear sm initSM 319 0 7816 5121 5122 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_per_head_linear pm initPM 697 0 15350 5121 8909 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_per_head_linear pm initPM 700 1 15363 5121 8910 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15350).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15363).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP layer-8 V projection. -/
theorem recon_intermediateGoal_5122_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5122
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5122 5122 8909 8910
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l8d_5122_rel initSM initPM hSM hPM hInit)

private theorem l8d_chunk (g : GraphDecl) (init : Store) (k r i o d : Nat)
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

/-- Distributed cache agreement for the layer-8 PM rotary-cache replica. -/
private theorem l8d_rotary_cache_11861 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11861 := by
  have hsource := sm_pm_rotary_cache_agree initSM initPM hInit 11861 8 (by norm_num) rfl
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11861 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11861 id (by native_decide) (by native_decide) (by decide)
      (fun st => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm st 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11861 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
-- Concrete graph reduction for both rotary outputs requires the larger elaboration budget.
private theorem l8d_rotary5124_5125_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5124)
      (denoteGraphDistributed pm initPM 8921) (denoteGraphDistributed pm initPM 8922)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 5125)
      (denoteGraphDistributed pm initPM 8923) (denoteGraphDistributed pm initPM 8924)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l8d_5118_rel initSM initPM hSM hPM hInit
  have hk := l8d_5120_rel initSM initPM hSM hPM hInit
  have hcache := l8d_rotary_cache_11861 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_5123
    (by native_decide) 5123 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_5123
    (by native_decide) 5123 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l8d_chunk pm initPM 8 0 5123 8919 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l8d_chunk pm initPM 21 1 5123 8920 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 8919 = chunkPrimDimN 0 2 0
      (denoteGraphDistributed pm initPM 5123) := c0
  have c1' : denoteGraphDistributed pm initPM 8920 = chunkPrimDimN 0 2 1
      (denoteGraphDistributed pm initPM 5123) := c1
  have qSM : denoteGraphDistributed sm initSM 5124 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5123)
        (denoteGraphDistributed sm initSM 5118) (denoteGraphDistributed sm initSM 5120) 16 4).1 := by
    rw [distributed_node_core sm initSM 320
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5123, 5118, 5120], outs := [5124, 5125], params := [16, 4] }
      5124 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 320 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 320 5123 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 320 5118 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 320 5120 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 5125 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5123)
        (denoteGraphDistributed sm initSM 5118) (denoteGraphDistributed sm initSM 5120) 16 4).2 := by
    rw [distributed_node_core sm initSM 320
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5123, 5118, 5120], outs := [5124, 5125], params := [16, 4] }
      5125 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5123 5118 5120 5124 5125 (by decide),
      distributed_prefix_read sm initSM 320 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 320 5123 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 320 5118 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 320 5120 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 8921 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11861) (denoteGraphDistributed pm initPM 8919)
        (denoteGraphDistributed pm initPM 8887) (denoteGraphDistributed pm initPM 8899) 16 4).1 := by
    rw [distributed_node_core pm initPM 701
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11861, 8919, 8887, 8899], outs := [8921, 8923], params := [16, 4] }
      8921 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 701 11861 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 701 8919 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 701 8887 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 701 8899 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 8923 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11861) (denoteGraphDistributed pm initPM 8919)
        (denoteGraphDistributed pm initPM 8887) (denoteGraphDistributed pm initPM 8899) 16 4).2 := by
    rw [distributed_node_core pm initPM 701
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11861, 8919, 8887, 8899], outs := [8921, 8923], params := [16, 4] }
      8923 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11861 8919 8887 8899 8921 8923 (by decide),
      distributed_prefix_read pm initPM 701 11861 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 701 8919 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 701 8887 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 701 8899 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 8922 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11861) (denoteGraphDistributed pm initPM 8920)
        (denoteGraphDistributed pm initPM 8888) (denoteGraphDistributed pm initPM 8900) 16 4).1 := by
    rw [distributed_node_core pm initPM 702
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11861, 8920, 8888, 8900], outs := [8922, 8924], params := [16, 4] }
      8922 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 702 11861 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 702 8920 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 702 8888 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 702 8900 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 8924 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11861) (denoteGraphDistributed pm initPM 8920)
        (denoteGraphDistributed pm initPM 8888) (denoteGraphDistributed pm initPM 8900) 16 4).2 := by
    rw [distributed_node_core pm initPM 702
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11861, 8920, 8888, 8900], outs := [8922, 8924], params := [16, 4] }
      8924 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11861 8920 8888 8900 8922 8924 (by decide),
      distributed_prefix_read pm initPM 702 11861 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 702 8920 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 702 8888 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 702 8900 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 5124 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8921, denoteGraphDistributed pm initPM 8922] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5123) (denoteGraphDistributed pm initPM 8887)
      (denoteGraphDistributed pm initPM 8888) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 5125 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8923, denoteGraphDistributed pm initPM 8924] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5123) (denoteGraphDistributed pm initPM 8899)
      (denoteGraphDistributed pm initPM 8900) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 8921).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 8922).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 8923).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 8924).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-8 rotary Q output. -/
theorem recon_intermediateGoal_5124_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5124
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5124 5124 8921 8922
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l8d_rotary5124_5125_rels initSM initPM hSM hPM hInit).1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-8 rotary K output. -/
theorem recon_intermediateGoal_5125_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5125
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5125 5125 8923 8924
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l8d_rotary5124_5125_rels initSM initPM hSM hPM hInit).2

#print axioms recon_intermediateGoal_5124_distributed
#print axioms recon_intermediateGoal_5125_distributed

end TrainVerify.Denote.GeneratedPatterns
