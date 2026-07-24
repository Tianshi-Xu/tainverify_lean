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

private def layer8SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5124, 5125, 5122, 5126, 5127], outs := [5128],
    params := [16, 4, 64, 64, 1, 512] }
private def layer8PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8921, 8923, 8909, 5126, 5127], outs := [8925],
    params := [16, 4, 64, 64, 1, 512] }
private def layer8PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8922, 8924, 8910, 5126, 5127], outs := [8926],
    params := [16, 4, 64, 64, 1, 512] }

set_option maxRecDepth 1000000 in
private theorem layer8_sm_sliding_node321 :
    sm.nodes[321]'(by native_decide) = layer8SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer8_pm_sliding_node703 :
    pm.nodes[703]'(by native_decide) = layer8PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer8_pm_sliding_node704 :
    pm.nodes[704]'(by native_decide) = layer8PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer8_sm_sliding_buddy :
    ringAttnBuddies sm layer8SmSliding = [layer8SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer8_pm_sliding_buddy0 :
    ringAttnBuddies pm layer8PmSliding0 = [layer8PmSliding0, layer8PmSliding1] := by
  native_decide
set_option maxRecDepth 1000000 in
private theorem layer8_pm_sliding_buddy1 :
    ringAttnBuddies pm layer8PmSliding1 = [layer8PmSliding0, layer8PmSliding1] := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful public pure-distributed exact 2-TP reconstruction of the layer-8
    sliding-window attention output. -/
theorem recon_intermediateGoal_5128_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5128
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have q := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5124 5124 8921 8922
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5124_distributed initSM initPM hSM hPM hInit)
  have k := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5125 5125 8923 8924
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5125_distributed initSM initPM hSM hPM hInit)
  have v := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5122 5122 8909 8910
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5122_distributed initSM initPM hSM hPM hInit)
  have hcu5126 := distributed_init_singleton_value initSM initPM hInit initGoal_5126
    (by native_decide) 5126 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu5127 := distributed_init_singleton_value initSM initPM hInit initGoal_5127
    (by native_decide) 5127 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 321).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 703).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 704).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 321, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 321, t ∉ n.outs) :
      fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 321 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 703, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 703, t ∉ n.outs) :
      fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 703 t hn hw
  have hqfull : fs 5124 = allGatherPrimDimN 0 2 0 [fp 8921, fp 8922] := by
    rw [bs 5124 (by native_decide) (by native_decide),
      bp 8921 (by native_decide) (by native_decide),
      bp 8922 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 5125 = allGatherPrimDimN 0 2 0 [fp 8923, fp 8924] := by
    rw [bs 5125 (by native_decide) (by native_decide),
      bp 8923 (by native_decide) (by native_decide),
      bp 8924 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 5122 = allGatherPrimDimN 0 2 0 [fp 8909, fp 8910] := by
    rw [bs 5122 (by native_decide) (by native_decide),
      bp 8909 (by native_decide) (by native_decide),
      bp 8910 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer8SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 5124).shape.length
    rw [bs 5124 (by native_decide) (by native_decide), q.full_shape]
    decide
  have hkpos : 0 < (fs (layer8SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 5125).shape.length
    rw [bs 5125 (by native_decide) (by native_decide), k.full_shape]
    decide
  have hvpos : 0 < (fs (layer8SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 5122).shape.length
    rw [bs 5122 (by native_decide) (by native_decide), v.full_shape]
    decide
  have hcuQ : fs 5126 = fp 5126 := by
    rw [bs 5126 (by native_decide) (by native_decide),
      bp 5126 (by native_decide) (by native_decide), hcu5126]
  have hcuK : fs 5127 = fp 5127 := by
    rw [bs 5127 (by native_decide) (by native_decide),
      bp 5127 (by native_decide) (by native_decide), hcu5127]
  have e8921 : fp 8921 = fp' 8921 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8921 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have e8922 : fp 8922 = fp' 8922 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8922 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have e8923 : fp 8923 = fp' 8923 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8923 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have e8924 : fp 8924 = fp' 8924 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8924 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have e8909 : fp 8909 = fp' 8909 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8909 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have e8910 : fp 8910 = fp' 8910 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8910 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have e5126 : fp 5126 = fp' 5126 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5126 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have e5127 : fp 5127 = fp' 5127 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5127 703 704
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer8PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer8PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer8_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8921
      · exact e8922
    · rw [layer8_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8923
      · exact e8924
    · rw [layer8_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8909
      · exact e8910
    · exact e5126
    · exact e5127
  have rSM : denoteGraphDistributed sm initSM 5128 =
      applyNodeRingAttn_sliding_window sm fs layer8SmSliding := by
    rw [distributed_node_core sm initSM 321 layer8SmSliding 5128 (by native_decide)
      layer8_sm_sliding_node321 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5124 5125 5122 5126 5127 5128
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 8925 =
      applyNodeRingAttn_sliding_window pm fp layer8PmSliding0 := by
    rw [distributed_node_core pm initPM 703 layer8PmSliding0 8925 (by native_decide)
      layer8_pm_sliding_node703 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8921 8923 8909 5126 5127 8925
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 8926 =
      applyNodeRingAttn_sliding_window pm fp' layer8PmSliding1 := by
    rw [distributed_node_core pm initPM 704 layer8PmSliding1 8926 (by native_decide)
      layer8_pm_sliding_node704 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8922 8924 8910 5126 5127 8926
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8921, fp 8922])
      (allGatherPrimDimN 0 2 0 [fp 8923, fp 8924])
      (allGatherPrimDimN 0 2 0 [fp 8909, fp 8910])
      (fp 5126) (fp 5127) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 5124 (by native_decide) (by native_decide), q.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8921, fp' 8922])
      (allGatherPrimDimN 0 2 0 [fp' 8923, fp' 8924])
      (allGatherPrimDimN 0 2 0 [fp' 8909, fp' 8910])
      (fp' 5126) (fp' 5127) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e8921, ← e8922, ← e8923, ← e8924, ← e8909, ← e8910,
      ← e5126, ← e5127]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_5128
    layer8SmSliding layer8PmSliding0 layer8PmSliding1 fs fp fp' 5128 8925 8926
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer8_sm_sliding_buddy layer8_pm_sliding_buddy0 layer8_pm_sliding_buddy1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

private theorem l8d_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l8d_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l8d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l8d_float (g : GraphDecl) (init : Store) (k r i o : Nat)
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

private theorem l8d_reshape5129_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5129)
      (denoteGraphDistributed pm initPM 8927) (denoteGraphDistributed pm initPM 8928)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5128 5128 8925 8926
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5128_distributed initSM initPM hSM hPM hInit)
  have rs := l8d_reshape sm initSM 322 0 5128 5129 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l8d_reshape pm initPM 705 0 8925 8927 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l8d_reshape pm initPM 706 1 8926 8928 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, by rw [rs]; rfl, by rw [r0]; rfl, by rw [r1]; rfl, by decide⟩
  rw [rs, h.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape,
    r0, r1]

/-- Pure-distributed exact 2-TP reconstruction of the layer-8 attention reshape. -/
theorem recon_intermediateGoal_5129_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5129
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5129 5129 8927 8928
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_reshape5129_rel initSM initPM hSM hPM hInit)

private theorem l8d_reshape5130_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5130)
      (denoteGraphDistributed pm initPM 8933) (denoteGraphDistributed pm initPM 8934)
      [4096, 1024] [2048, 1024] := by
  have h := l8d_reshape5129_rel initSM initPM hSM hPM hInit
  have rs := l8d_reshape sm initSM 323 0 5129 5130 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l8d_reshape pm initPM 707 0 8927 8933 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l8d_reshape pm initPM 708 1 8928 8934 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5130 = denoteGraphDistributed sm initSM 5129 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8933 = denoteGraphDistributed pm initPM 8927 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8934 = denoteGraphDistributed pm initPM 8928 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the identity reshape. -/
theorem recon_intermediateGoal_5130_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5130
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5130 5130 8933 8934
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_reshape5130_rel initSM initPM hSM hPM hInit)

private theorem l8d_linear5132_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5132)
      (denoteGraphDistributed pm initPM 8937) (denoteGraphDistributed pm initPM 8938)
      [4096, 1024] [2048, 1024] := by
  have h := l8d_reshape5130_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5131
    (by native_decide) 5131 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5131
    (by native_decide) 5131 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5131).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l8d_linear sm initSM 324 0 5130 5131 5132 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_linear pm initPM 709 0 8933 5131 8937 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_linear pm initPM 710 1 8934 5131 8938 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the output projection. -/
theorem recon_intermediateGoal_5132_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5132
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5132 5132 8937 8938
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_linear5132_rel initSM initPM hSM hPM hInit)

private theorem l8d_view5133_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5133)
      (denoteGraphDistributed pm initPM 8947) (denoteGraphDistributed pm initPM 8948)
      [4096, 1024] [2048, 1024] := by
  have h := l8d_linear5132_rel initSM initPM hSM hPM hInit
  have rs := l8d_view sm initSM 325 0 5132 5133 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l8d_view pm initPM 711 0 8937 8947 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l8d_view pm initPM 712 1 8938 8948 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5133 = denoteGraphDistributed sm initSM 5132 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8947 = denoteGraphDistributed pm initPM 8937 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8948 = denoteGraphDistributed pm initPM 8938 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the identity view. -/
theorem recon_intermediateGoal_5133_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5133
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5133 5133 8947 8948
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_view5133_rel initSM initPM hSM hPM hInit)

private theorem l8d_float5134_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5134)
      (denoteGraphDistributed pm initPM 8951) (denoteGraphDistributed pm initPM 8952)
      [4096, 1024] [2048, 1024] := by
  have h := l8d_view5133_rel initSM initPM hSM hPM hInit
  have rs := l8d_float sm initSM 326 0 5133 5134 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_float pm initPM 713 0 8947 8951 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_float pm initPM 714 1 8948 8952 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the post-projection float. -/
theorem recon_intermediateGoal_5134_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5134
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5134 5134 8951 8952
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_float5134_rel initSM initPM hSM hPM hInit)

private theorem l8d_carry7803_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7803)
      (denoteGraphDistributed pm initPM 15329) (denoteGraphDistributed pm initPM 15337)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5114 5114 8881 8882
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5114_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 314
    { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803], params := [2] }
    5114 7803 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5114 7799 7803 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 689
    { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329], params := [2] }
    8881 15329 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8881 15325 15329 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 690
    { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337], params := [2] }
    8882 15337 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8882 15333 15337 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, ← r0, ← r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed residual add `7803 + 5134` completing the post-attention cascade. -/
theorem recon_intermediateGoal_5135_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5135
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := l8d_carry7803_rel initSM initPM hSM hPM hInit
  have hb := l8d_float5134_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce2 sm initSM 327
    { rank := 0, op := "OpName.FW_add", ins := [7803, 5134], outs := [5135] }
    7803 5134 5135 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 7803 5134 5135)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 715
    { rank := 0, op := "OpName.FW_add", ins := [15329, 8951], outs := [8955] }
    15329 8951 8955 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 15329 8951 8955)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 716
    { rank := 1, op := "OpName.FW_add", ins := [15337, 8952], outs := [8956] }
    15337 8952 8956 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 15337 8952 8956)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5135 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8955, denoteGraphDistributed pm initPM 8956] := by
    rw [rs, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← r0, ← r1]
  have hs0 : (denoteGraphDistributed pm initPM 8955).shape = [2048, 1024] := by
    rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 8956).shape = [2048, 1024] := by
    rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5135).shape = [4096, 1024] := by
    rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5135 5135 8955 8956
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide) hv hs hs0 hs1

/-! ## Pure-distributed layer-9 router entrance -/

private theorem l8d_norm_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_norm_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_norm_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_norm_linear hk hn (by simp)
    (fun st => applyNode_fw_norm_linear_out g st r x w o) hdn hdw hpn hpx hpw

private theorem l8d_rms5137_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5137)
      (denoteGraphDistributed pm initPM 8959) (denoteGraphDistributed pm initPM 8960)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5135 5135 8955 8956
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5135_distributed initSM initPM hSM hPM hInit)
  have ms := distributed_reduce1 sm initSM 328
    { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824], params := [2] }
    5135 7820 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5135 7820 7824)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 717
    { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371], params := [2] }
    8955 15367 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8955 15367 15371)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 718
    { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379], params := [2] }
    8956 15375 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8956 15375 15379)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5136
    (by native_decide) 5136 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l8d_rms sm initSM 329 0 7820 5136 5137 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_rms pm initPM 719 0 15367 5136 8959 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_rms pm initPM 720 1 15375 5136 8960 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15367).shape = [2048, 1024] := by rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15375).shape = [2048, 1024] := by rw [m1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ms, h.value, ← m0, ← m1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1, r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP reconstruction of the layer-9 router RMSNorm. -/
theorem recon_intermediateGoal_5137_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5137
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5137 5137 8959 8960
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_rms5137_rel initSM initPM hSM hPM hInit)

private theorem l8d_float5138_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5138)
      (denoteGraphDistributed pm initPM 8961) (denoteGraphDistributed pm initPM 8962)
      [4096, 1024] [2048, 1024] := by
  have h := l8d_rms5137_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 330
    { rank := 0, op := "OpName.FW_multiref", ins := [5137],
      outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
    5137 7831 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' sm st 0 4 5137 7831 [7835, 7839, 7843, 7847])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 721
    { rank := 0, op := "OpName.FW_multiref", ins := [8959],
      outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
    8959 15386 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 0 4 8959 15386 [15390, 15394, 15398, 15402])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 722
    { rank := 1, op := "OpName.FW_multiref", ins := [8960],
      outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
    8960 15409 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 1 4 8960 15409 [15413, 15417, 15421, 15425])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rs := l8d_float sm initSM 331 0 7831 5138 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_float pm initPM 723 0 15386 8961 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_float pm initPM 727 1 15409 8962 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  exact ⟨by rw [rs, ms, h.value, ← m0, ← m1, r0, r1],
    by rw [rs, ms]; exact h.full_shape, by rw [r0, m0]; exact h.shard0_shape,
    by rw [r1, m1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the first router `mref5` float. -/
theorem recon_intermediateGoal_5138_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5138
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5138 5138 8961 8962
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l8d_float5138_rel initSM initPM hSM hPM hInit)

private theorem l8d_logits5140_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5140)
      (denoteGraphDistributed pm initPM 8967) (denoteGraphDistributed pm initPM 8968)
      [4096, 64] [2048, 64] := by
  have h := l8d_float5138_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5139
    (by native_decide) 5139 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5139
    (by native_decide) 5139 [64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5139).shape = [64, 1024] := by rw [← hw]; exact hws
  have rs := l8d_norm_linear sm initSM 335 0 5138 5139 5140 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_norm_linear pm initPM 731 0 8961 5139 8967 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_norm_linear pm initPM 735 1 8962 5139 8968 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) h.full_shape hws
  · rw [r0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard0_shape hpw
  · rw [r1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-9 router logits. -/
theorem recon_intermediateGoal_5140_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5140
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5140 5140 8967 8968
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l8d_logits5140_rel initSM initPM hSM hPM hInit)

private theorem l8d_distributed_reduce1_at (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : applyNodeRingAttn g ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid =
      opfun (((g.nodes.take k).foldl (applyNodeDistributed g) init) inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraphDistributed g init outTid = opfun (denoteGraphDistributed g init inTid) := by
  rw [distributed_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, distributed_prefix_read g init k inTid hpre_nil hpre]

private theorem l8d_topk_common (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5140)
      (denoteGraphDistributed pm initPM 8967) (denoteGraphDistributed pm initPM 8968)
      [4096, 64] [2048, 64]
    ∧ ((sm.nodes.take 339).foldl (applyNodeDistributed sm) initSM 5140).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 739).foldl (applyNodeDistributed pm) initPM 8967).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 743).foldl (applyNodeDistributed pm) initPM 8968).shape.reverse.head? = some 64 := by
  have h := l8d_logits5140_rel initSM initPM hSM hPM hInit
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [distributed_prefix_read sm initSM 339 5140 (by native_decide) (by native_decide), h.full_shape]; rfl
  · rw [distributed_prefix_read pm initPM 739 8967 (by native_decide) (by native_decide), h.shard0_shape]; rfl
  · rw [distributed_prefix_read pm initPM 743 8968 (by native_decide) (by native_decide), h.shard1_shape]; rfl

private theorem l8d_topk5141_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5141)
      (denoteGraphDistributed pm initPM 8969) (denoteGraphDistributed pm initPM 8970)
      [4096, 64] [2048, 64] := by
  obtain ⟨h, ls, l0, l1⟩ := l8d_topk_common initSM initPM hSM hPM hInit
  have rs := l8d_distributed_reduce1_at sm initSM 339
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5140], outs := [5141, 5142, 5143], params := [8, 1] }
    5140 5141 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst sm ((sm.nodes.take 339).foldl (applyNodeDistributed sm) initSM) 0 5140 5141 5142 5143 ls)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_distributed_reduce1_at pm initPM 739
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8967], outs := [8969, 8971, 8973], params := [8, 1] }
    8967 8969 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm ((pm.nodes.take 739).foldl (applyNodeDistributed pm) initPM) 0 8967 8969 8971 8973 l0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_distributed_reduce1_at pm initPM 743
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8968], outs := [8970, 8972, 8974], params := [8, 1] }
    8968 8970 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm ((pm.nodes.take 743).foldl (applyNodeDistributed pm) initPM) 1 8968 8970 8972 8974 l1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega)
        h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Pure-distributed exact 2-TP reconstruction of layer-9 routing probabilities. -/
theorem recon_intermediateGoal_5141_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5141
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5141 5141 8969 8970
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l8d_topk5141_rel initSM initPM hSM hPM hInit)

/-- Pure-distributed exact 2-TP reconstruction of the layer-9 routing map. -/
theorem recon_intermediateGoal_5142_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5142
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  obtain ⟨h, ls, l0, l1⟩ := l8d_topk_common initSM initPM hSM hPM hInit
  have rs := l8d_distributed_reduce1_at sm initSM 339
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5140], outs := [5141, 5142, 5143], params := [8, 1] }
    5140 5142 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd sm ((sm.nodes.take 339).foldl (applyNodeDistributed sm) initSM) 0 5140 5141 5142 5143 (by decide) ls)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l8d_distributed_reduce1_at pm initPM 739
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8967], outs := [8969, 8971, 8973], params := [8, 1] }
    8967 8971 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm ((pm.nodes.take 739).foldl (applyNodeDistributed pm) initPM) 0 8967 8969 8971 8973 (by decide) l0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l8d_distributed_reduce1_at pm initPM 743
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8968], outs := [8970, 8972, 8974], params := [8, 1] }
    8968 8972 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm ((pm.nodes.take 743).foldl (applyNodeDistributed pm) initPM) 1 8968 8970 8972 8974 (by decide) l1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rel : Gather2Rel (denoteGraphDistributed sm initSM 5142)
      (denoteGraphDistributed pm initPM 8971) (denoteGraphDistributed pm initPM 8972)
      [4096, 64] [2048, 64] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, h.value,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega)
          h.shard0_shape h.shard1_shape, r0, r1]
    · rw [rs]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
    · rw [r0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
    · rw [r1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5142 5142 8971 8972
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl rel

#print axioms recon_intermediateGoal_5124_distributed
#print axioms recon_intermediateGoal_5125_distributed
#print axioms recon_intermediateGoal_5128_distributed
#print axioms recon_intermediateGoal_5135_distributed
#print axioms recon_intermediateGoal_5141_distributed
#print axioms recon_intermediateGoal_5142_distributed

end TrainVerify.Denote.GeneratedPatterns
