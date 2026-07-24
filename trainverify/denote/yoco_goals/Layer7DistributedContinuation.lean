/- Pure-distributed continuation of layer 7 through pre-attention RMSNorm and Q/K/V. -/
import denote.yoco_goals.Layer6DistributedContinuation

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l7d_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l7d_per_head_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l7d_rms5062_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5062)
      (denoteGraphDistributed pm initPM 8699) (denoteGraphDistributed pm initPM 8700)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5060 5060 8695 8696
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5060_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 275
    { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751], params := [2] }
    5060 7747 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5060 7747 7751)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 611
    { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225], params := [2] }
    8695 15221 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8695 15221 15225)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 612
    { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233], params := [2] }
    8696 15229 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8696 15229 15233)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5061
    (by native_decide) 5061 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l7d_rms sm initSM 276 0 7747 5061 5062 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l7d_rms pm initPM 613 0 15221 5061 8699 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l7d_rms pm initPM 614 1 15229 5061 8700 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15221).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15229).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP reconstruction of the layer-7 pre-attention RMSNorm. -/
theorem recon_intermediateGoal_5062_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5062
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5062 5062 8699 8700
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_rms5062_rel initSM initPM hSM hPM hInit)

private theorem l7d_q5064_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5064)
      (denoteGraphDistributed pm initPM 8701) (denoteGraphDistributed pm initPM 8702)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l7d_rms5062_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 277
    { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
    5062 7756 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 5062 7756 7760 7764)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 615
    { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
    8699 15238 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 8699 15238 15242 15246)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 616
    { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
    8700 15251 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 8700 15251 15255 15259)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5063
    (by native_decide) 5063 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5063
    (by native_decide) 5063 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5063).shape = [16, 64, 1024] := by
    rw [← hw]; exact hws
  have rs := l7d_per_head_linear sm initSM 278 0 7756 5063 5064 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l7d_per_head_linear pm initPM 617 0 15238 5063 8701 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l7d_per_head_linear pm initPM 620 1 15251 5063 8702 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15238).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15251).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-7 Q projection. -/
theorem recon_intermediateGoal_5064_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5064
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5064 5064 8701 8702
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l7d_q5064_rel initSM initPM hSM hPM hInit)

private theorem l7d_k5066_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5066)
      (denoteGraphDistributed pm initPM 8713) (denoteGraphDistributed pm initPM 8714)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l7d_rms5062_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 277
    { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
    5062 7760 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 5062 7756 7760 7764 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 615
    { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
    8699 15242 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 8699 15238 15242 15246 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 616
    { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
    8700 15255 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 8700 15251 15255 15259 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5065
    (by native_decide) 5065 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5065
    (by native_decide) 5065 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5065).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have rs := l7d_per_head_linear sm initSM 279 0 7760 5065 5066 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l7d_per_head_linear pm initPM 618 0 15242 5065 8713 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l7d_per_head_linear pm initPM 621 1 15255 5065 8714 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15242).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15255).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-7 K projection. -/
theorem recon_intermediateGoal_5066_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5066
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5066 5066 8713 8714
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l7d_k5066_rel initSM initPM hSM hPM hInit)

private theorem l7d_v5068_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5068)
      (denoteGraphDistributed pm initPM 8723) (denoteGraphDistributed pm initPM 8724)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l7d_rms5062_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 277
    { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }
    5062 7764 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 5062 7756 7760 7764 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 615
    { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }
    8699 15246 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 8699 15238 15242 15246 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 616
    { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }
    8700 15259 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 8700 15251 15255 15259 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5067
    (by native_decide) 5067 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5067
    (by native_decide) 5067 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5067).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have rs := l7d_per_head_linear sm initSM 280 0 7764 5067 5068 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l7d_per_head_linear pm initPM 619 0 15246 5067 8723 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l7d_per_head_linear pm initPM 622 1 15259 5067 8724 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15246).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15259).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-7 V projection. -/
theorem recon_intermediateGoal_5068_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5068
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5068 5068 8723 8724
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l7d_v5068_rel initSM initPM hSM hPM hInit)

private theorem l7d_chunk (g : GraphDecl) (init : Store) (k r i o d : Nat)
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

/-- Distributed cache agreement for the layer-7 PM rotary-cache replica. -/
private theorem l7d_rotary_cache_11860 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11860 := by
  have hsource := sm_pm_rotary_cache_agree initSM initPM hInit 11860 7 (by norm_num) rfl
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11860 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11860 id (by native_decide) (by native_decide) (by decide)
      (fun st => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm st 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11860 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
-- Concrete graph reduction for both rotary outputs requires the larger elaboration budget.
private theorem l7d_rotary5070_5071_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5070)
      (denoteGraphDistributed pm initPM 8735) (denoteGraphDistributed pm initPM 8736)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 5071)
      (denoteGraphDistributed pm initPM 8737) (denoteGraphDistributed pm initPM 8738)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l7d_q5064_rel initSM initPM hSM hPM hInit
  have hk := l7d_k5066_rel initSM initPM hSM hPM hInit
  have hcache := l7d_rotary_cache_11860 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_5069
    (by native_decide) 5069 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_5069
    (by native_decide) 5069 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l7d_chunk pm initPM 7 0 5069 8733 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l7d_chunk pm initPM 20 1 5069 8734 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 8733 = chunkPrimDimN 0 2 0
      (denoteGraphDistributed pm initPM 5069) := c0
  have c1' : denoteGraphDistributed pm initPM 8734 = chunkPrimDimN 0 2 1
      (denoteGraphDistributed pm initPM 5069) := c1
  have qSM : denoteGraphDistributed sm initSM 5070 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5069)
        (denoteGraphDistributed sm initSM 5064) (denoteGraphDistributed sm initSM 5066) 16 4).1 := by
    rw [distributed_node_core sm initSM 281
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5069, 5064, 5066], outs := [5070, 5071], params := [16, 4] }
      5070 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 281 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 281 5069 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 281 5064 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 281 5066 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 5071 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5069)
        (denoteGraphDistributed sm initSM 5064) (denoteGraphDistributed sm initSM 5066) 16 4).2 := by
    rw [distributed_node_core sm initSM 281
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5069, 5064, 5066], outs := [5070, 5071], params := [16, 4] }
      5071 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5069 5064 5066 5070 5071 (by decide),
      distributed_prefix_read sm initSM 281 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 281 5069 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 281 5064 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 281 5066 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 8735 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11860) (denoteGraphDistributed pm initPM 8733)
        (denoteGraphDistributed pm initPM 8701) (denoteGraphDistributed pm initPM 8713) 16 4).1 := by
    rw [distributed_node_core pm initPM 623
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11860, 8733, 8701, 8713], outs := [8735, 8737], params := [16, 4] }
      8735 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 623 11860 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 623 8733 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 623 8701 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 623 8713 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 8737 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11860) (denoteGraphDistributed pm initPM 8733)
        (denoteGraphDistributed pm initPM 8701) (denoteGraphDistributed pm initPM 8713) 16 4).2 := by
    rw [distributed_node_core pm initPM 623
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11860, 8733, 8701, 8713], outs := [8735, 8737], params := [16, 4] }
      8737 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11860 8733 8701 8713 8735 8737 (by decide),
      distributed_prefix_read pm initPM 623 11860 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 623 8733 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 623 8701 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 623 8713 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 8736 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11860) (denoteGraphDistributed pm initPM 8734)
        (denoteGraphDistributed pm initPM 8702) (denoteGraphDistributed pm initPM 8714) 16 4).1 := by
    rw [distributed_node_core pm initPM 624
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11860, 8734, 8702, 8714], outs := [8736, 8738], params := [16, 4] }
      8736 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 624 11860 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 624 8734 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 624 8702 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 624 8714 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 8738 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11860) (denoteGraphDistributed pm initPM 8734)
        (denoteGraphDistributed pm initPM 8702) (denoteGraphDistributed pm initPM 8714) 16 4).2 := by
    rw [distributed_node_core pm initPM 624
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11860, 8734, 8702, 8714], outs := [8736, 8738], params := [16, 4] }
      8738 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11860 8734 8702 8714 8736 8738 (by decide),
      distributed_prefix_read pm initPM 624 11860 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 624 8734 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 624 8702 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 624 8714 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 5070 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8735, denoteGraphDistributed pm initPM 8736] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5069) (denoteGraphDistributed pm initPM 8701)
      (denoteGraphDistributed pm initPM 8702) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 5071 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8737, denoteGraphDistributed pm initPM 8738] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5069) (denoteGraphDistributed pm initPM 8713)
      (denoteGraphDistributed pm initPM 8714) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 8735).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 8736).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 8737).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 8738).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-7 rotary Q output. -/
theorem recon_intermediateGoal_5070_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5070
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5070 5070 8735 8736
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l7d_rotary5070_5071_rels initSM initPM hSM hPM hInit).1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-7 rotary K output. -/
theorem recon_intermediateGoal_5071_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5071
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5071 5071 8737 8738
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l7d_rotary5070_5071_rels initSM initPM hSM hPM hInit).2

private def layer7SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5070, 5071, 5068, 5072, 5073], outs := [5074],
    params := [16, 4, 64, 64, 1, 512] }
private def layer7PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8735, 8737, 8723, 5072, 5073], outs := [8739],
    params := [16, 4, 64, 64, 1, 512] }
private def layer7PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8736, 8738, 8724, 5072, 5073], outs := [8740],
    params := [16, 4, 64, 64, 1, 512] }

set_option maxRecDepth 1000000 in
private theorem layer7_sm_sliding_node282 :
    sm.nodes[282]'(by native_decide) = layer7SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer7_pm_sliding_node625 :
    pm.nodes[625]'(by native_decide) = layer7PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer7_pm_sliding_node626 :
    pm.nodes[626]'(by native_decide) = layer7PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer7_sm_sliding_buddy :
    ringAttnBuddies sm layer7SmSliding = [layer7SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer7_pm_sliding_buddy0 :
    ringAttnBuddies pm layer7PmSliding0 = [layer7PmSliding0, layer7PmSliding1] := by
  native_decide
set_option maxRecDepth 1000000 in
private theorem layer7_pm_sliding_buddy1 :
    ringAttnBuddies pm layer7PmSliding1 = [layer7PmSliding0, layer7PmSliding1] := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful public pure-distributed exact 2-TP reconstruction of the layer-7
    sliding-window attention output. -/
theorem recon_intermediateGoal_5074_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5074
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have q := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5070 5070 8735 8736
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5070_distributed initSM initPM hSM hPM hInit)
  have k := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5071 5071 8737 8738
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5071_distributed initSM initPM hSM hPM hInit)
  have v := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5068 5068 8723 8724
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5068_distributed initSM initPM hSM hPM hInit)
  have hcu5072 := distributed_init_singleton_value initSM initPM hInit initGoal_5072
    (by native_decide) 5072 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu5073 := distributed_init_singleton_value initSM initPM hInit initGoal_5073
    (by native_decide) 5073 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 282).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 625).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 626).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 282, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 282, t ∉ n.outs) :
      fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 282 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 625, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 625, t ∉ n.outs) :
      fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 625 t hn hw
  have hqfull : fs 5070 = allGatherPrimDimN 0 2 0 [fp 8735, fp 8736] := by
    rw [bs 5070 (by native_decide) (by native_decide),
      bp 8735 (by native_decide) (by native_decide),
      bp 8736 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 5071 = allGatherPrimDimN 0 2 0 [fp 8737, fp 8738] := by
    rw [bs 5071 (by native_decide) (by native_decide),
      bp 8737 (by native_decide) (by native_decide),
      bp 8738 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 5068 = allGatherPrimDimN 0 2 0 [fp 8723, fp 8724] := by
    rw [bs 5068 (by native_decide) (by native_decide),
      bp 8723 (by native_decide) (by native_decide),
      bp 8724 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer7SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 5070).shape.length
    rw [bs 5070 (by native_decide) (by native_decide), q.full_shape]
    decide
  have hkpos : 0 < (fs (layer7SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 5071).shape.length
    rw [bs 5071 (by native_decide) (by native_decide), k.full_shape]
    decide
  have hvpos : 0 < (fs (layer7SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 5068).shape.length
    rw [bs 5068 (by native_decide) (by native_decide), v.full_shape]
    decide
  have hcuQ : fs 5072 = fp 5072 := by
    rw [bs 5072 (by native_decide) (by native_decide),
      bp 5072 (by native_decide) (by native_decide), hcu5072]
  have hcuK : fs 5073 = fp 5073 := by
    rw [bs 5073 (by native_decide) (by native_decide),
      bp 5073 (by native_decide) (by native_decide), hcu5073]
  have e8735 : fp 8735 = fp' 8735 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8735 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have e8736 : fp 8736 = fp' 8736 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8736 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have e8737 : fp 8737 = fp' 8737 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8737 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have e8738 : fp 8738 = fp' 8738 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8738 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have e8723 : fp 8723 = fp' 8723 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8723 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have e8724 : fp 8724 = fp' 8724 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8724 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have e5072 : fp 5072 = fp' 5072 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5072 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have e5073 : fp 5073 = fp' 5073 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5073 625 626
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer7PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer7PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer7_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8735
      · exact e8736
    · rw [layer7_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8737
      · exact e8738
    · rw [layer7_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8723
      · exact e8724
    · exact e5072
    · exact e5073
  have rSM : denoteGraphDistributed sm initSM 5074 =
      applyNodeRingAttn_sliding_window sm fs layer7SmSliding := by
    rw [distributed_node_core sm initSM 282 layer7SmSliding 5074 (by native_decide)
      layer7_sm_sliding_node282 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5070 5071 5068 5072 5073 5074
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 8739 =
      applyNodeRingAttn_sliding_window pm fp layer7PmSliding0 := by
    rw [distributed_node_core pm initPM 625 layer7PmSliding0 8739 (by native_decide)
      layer7_pm_sliding_node625 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8735 8737 8723 5072 5073 8739
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 8740 =
      applyNodeRingAttn_sliding_window pm fp' layer7PmSliding1 := by
    rw [distributed_node_core pm initPM 626 layer7PmSliding1 8740 (by native_decide)
      layer7_pm_sliding_node626 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8736 8738 8724 5072 5073 8740
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8735, fp 8736])
      (allGatherPrimDimN 0 2 0 [fp 8737, fp 8738])
      (allGatherPrimDimN 0 2 0 [fp 8723, fp 8724])
      (fp 5072) (fp 5073) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 5070 (by native_decide) (by native_decide), q.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8735, fp' 8736])
      (allGatherPrimDimN 0 2 0 [fp' 8737, fp' 8738])
      (allGatherPrimDimN 0 2 0 [fp' 8723, fp' 8724])
      (fp' 5072) (fp' 5073) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e8735, ← e8736, ← e8737, ← e8738, ← e8723, ← e8724,
      ← e5072, ← e5073]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_5074
    layer7SmSliding layer7PmSliding0 layer7PmSliding1 fs fp fp' 5074 8739 8740
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer7_sm_sliding_buddy layer7_pm_sliding_buddy0 layer7_pm_sliding_buddy1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

private theorem l7d_view (g : GraphDecl) (init : Store) (k r i o n : Nat) (tail : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := n :: tail })
    (hdn : ∀ nd ∈ g.nodes.drop (k + 1), nd.outs ≠ [])
    (hdw : ∀ nd ∈ g.nodes.drop (k + 1), o ∉ nd.outs)
    (hpn : ∀ nd ∈ g.nodes.drop k, nd.outs ≠ [])
    (hpw : ∀ nd ∈ g.nodes.drop k, i ∉ nd.outs) :
    denoteGraphDistributed g init o = fw_view (n :: tail) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (n :: tail)) hk hn (by simp)
    (fun st => applyNode_fw_view_out g st r n tail i o) hdn hdw hpn hpw

private theorem l7d_view_op (g : GraphDecl) (init : Store) (k r i o n : Nat) (tail : List Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := n :: tail })
    (hdn : ∀ nd ∈ g.nodes.drop (k + 1), nd.outs ≠ [])
    (hdw : ∀ nd ∈ g.nodes.drop (k + 1), o ∉ nd.outs)
    (hpn : ∀ nd ∈ g.nodes.drop k, nd.outs ≠ [])
    (hpw : ∀ nd ∈ g.nodes.drop k, i ∉ nd.outs) :
    denoteGraphDistributed g init o = fw_view (n :: tail) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (n :: tail)) hk hn (by simp)
    (fun st => applyNode_fw_view_out g st r n tail i o) hdn hdw hpn hpw

private theorem l7d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ nd ∈ g.nodes.drop (k + 1), nd.outs ≠ [])
    (hdw : ∀ nd ∈ g.nodes.drop (k + 1), o ∉ nd.outs)
    (hpn : ∀ nd ∈ g.nodes.drop k, nd.outs ≠ [])
    (hpx : ∀ nd ∈ g.nodes.drop k, x ∉ nd.outs)
    (hpw : ∀ nd ∈ g.nodes.drop k, w ∉ nd.outs) :
    denoteGraphDistributed g init o =
      fw_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o)
    hdn hdw hpn hpx hpw

private theorem l7d_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ nd ∈ g.nodes.drop (k + 1), nd.outs ≠ [])
    (hdw : ∀ nd ∈ g.nodes.drop (k + 1), o ∉ nd.outs)
    (hpn : ∀ nd ∈ g.nodes.drop k, nd.outs ≠ [])
    (hpx : ∀ nd ∈ g.nodes.drop k, x ∉ nd.outs)
    (hpy : ∀ nd ∈ g.nodes.drop k, y ∉ nd.outs) :
    denoteGraphDistributed g init o =
      elemwiseAdd (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  distributed_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

private theorem l7d_5075_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5075)
      (denoteGraphDistributed pm initPM 8741) (denoteGraphDistributed pm initPM 8742)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5074 5074 8739 8740
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5074_distributed initSM initPM hSM hPM hInit)
  have rs := l7d_view sm initSM 283 0 5074 5075 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l7d_view pm initPM 627 0 8739 8741 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l7d_view pm initPM 628 1 8740 8742 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, r0, r1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

/-- Pure-distributed exact 2-TP reshape of the layer-7 attention output. -/
theorem recon_intermediateGoal_5075_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5075
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5075 5075 8741 8742
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_5075_rel initSM initPM hSM hPM hInit)

private theorem l7d_5076_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5076)
      (denoteGraphDistributed pm initPM 8747) (denoteGraphDistributed pm initPM 8748)
      [4096, 1024] [2048, 1024] := by
  have h := l7d_5075_rel initSM initPM hSM hPM hInit
  have rs := l7d_view sm initSM 284 0 5075 5076 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l7d_view pm initPM 629 0 8741 8747 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l7d_view pm initPM 630 1 8742 8748 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape, h.value,
      r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape,
      r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

/-- Pure-distributed exact 2-TP identity reshape after layer-7 attention. -/
theorem recon_intermediateGoal_5076_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5076
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5076 5076 8747 8748
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_5076_rel initSM initPM hSM hPM hInit)

private theorem l7d_5078_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5078)
      (denoteGraphDistributed pm initPM 8751) (denoteGraphDistributed pm initPM 8752)
      [4096, 1024] [2048, 1024] := by
  have h := l7d_5076_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5077
    (by native_decide) 5077 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5077
    (by native_decide) 5077 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5077).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l7d_linear sm initSM 285 0 5076 5077 5078
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l7d_linear pm initPM 631 0 8747 5077 8751
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l7d_linear pm initPM 632 1 8748 5077 8752
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP post-attention output projection. -/
theorem recon_intermediateGoal_5078_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5078
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5078 5078 8751 8752
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_5078_rel initSM initPM hSM hPM hInit)

private theorem l7d_5079_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5079)
      (denoteGraphDistributed pm initPM 8761) (denoteGraphDistributed pm initPM 8762)
      [4096, 1024] [2048, 1024] := by
  have h := l7d_5078_rel initSM initPM hSM hPM hInit
  have rs := l7d_view_op sm initSM 286 0 5078 5079 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l7d_view_op pm initPM 633 0 8751 8761 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l7d_view_op pm initPM 634 1 8752 8762 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape, h.value,
      r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape,
      r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

/-- Pure-distributed exact 2-TP post-projection view. -/
theorem recon_intermediateGoal_5079_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5079
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5079 5079 8761 8762
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_5079_rel initSM initPM hSM hPM hInit)

private theorem l7d_5080_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5080)
      (denoteGraphDistributed pm initPM 8765) (denoteGraphDistributed pm initPM 8766)
      [4096, 1024] [2048, 1024] := by
  have h := l7d_5079_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 287
    { rank := 0, op := "OpName.FW_float", ins := [5079], outs := [5080] }
    5079 5080 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_float_out sm st 0 5079 5080 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 635
    { rank := 0, op := "OpName.FW_float", ins := [8761], outs := [8765] }
    8761 8765 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_float_out pm st 0 8761 8765 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 636
    { rank := 1, op := "OpName.FW_float", ins := [8762], outs := [8766] }
    8762 8766 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_float_out pm st 1 8762 8766 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, r0, r1]
  · rw [rs]; exact h.full_shape
  · rw [r0]; exact h.shard0_shape
  · rw [r1]; exact h.shard1_shape

/-- Pure-distributed exact 2-TP float cast after the attention projection. -/
theorem recon_intermediateGoal_5080_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5080
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5080 5080 8765 8766
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_5080_rel initSM initPM hSM hPM hInit)

private theorem l7d_7751_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7751)
      (denoteGraphDistributed pm initPM 15225) (denoteGraphDistributed pm initPM 15233)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5060 5060 8695 8696
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5060_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 275
    { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751], params := [2] }
    5060 7751 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5060 7747 7751 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 611
    { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225], params := [2] }
    8695 15225 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8695 15221 15225 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 612
    { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233], params := [2] }
    8696 15233 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8696 15229 15233 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, r0, r1]
  · rw [rs]; exact h.full_shape
  · rw [r0]; exact h.shard0_shape
  · rw [r1]; exact h.shard1_shape

/-- Pure-distributed exact 2-TP residual carry from the second multiref of `5060`. -/
theorem recon_intermediateGoal_7751_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7751
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7751 7751 15225 15233
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_7751_rel initSM initPM hSM hPM hInit)

private theorem l7d_5081_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5081)
      (denoteGraphDistributed pm initPM 8769) (denoteGraphDistributed pm initPM 8770)
      [4096, 1024] [2048, 1024] := by
  have a := l7d_7751_rel initSM initPM hSM hPM hInit
  have b := l7d_5080_rel initSM initPM hSM hPM hInit
  have rs := l7d_add sm initSM 288 0 7751 5080 5081
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l7d_add pm initPM 637 0 15225 8765 8769
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l7d_add pm initPM 638 1 15233 8766 8770
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, a.value, b.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _
        a.shard0_shape a.shard1_shape b.shard0_shape b.shard1_shape,
      r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] a.full_shape b.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] a.shard0_shape b.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] a.shard1_shape b.shard1_shape

/-- Pure-distributed exact 2-TP layer-7 post-attention residual add. -/
theorem recon_intermediateGoal_5081_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5081
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5081 5081 8769 8770
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l7d_5081_rel initSM initPM hSM hPM hInit)

#print axioms recon_intermediateGoal_5062_distributed
#print axioms recon_intermediateGoal_5064_distributed
#print axioms recon_intermediateGoal_5066_distributed
#print axioms recon_intermediateGoal_5068_distributed
#print axioms recon_intermediateGoal_5070_distributed
#print axioms recon_intermediateGoal_5071_distributed
#print axioms recon_intermediateGoal_5074_distributed
#print axioms recon_intermediateGoal_5075_distributed
#print axioms recon_intermediateGoal_5078_distributed
#print axioms recon_intermediateGoal_5080_distributed
#print axioms recon_intermediateGoal_7751_distributed
#print axioms recon_intermediateGoal_5081_distributed

end TrainVerify.Denote.GeneratedPatterns
