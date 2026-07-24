/- Pure-distributed layer-11 post-attention projection/residual continuation. -/
import denote.yoco_goals.Layer10DistributedContinuation

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l11d_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l11d_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l11d_float (g : GraphDecl) (init : Store) (k r i o : Nat)
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

private theorem l11d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l11d_5237_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5237)
      (denoteGraphDistributed pm initPM 9299) (denoteGraphDistributed pm initPM 9300)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5236 5236 9297 9298
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5236_distributed initSM initPM hSM hPM hInit)
  have rs := l11d_reshape sm initSM 400 0 5236 5237 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_reshape pm initPM 861 0 9297 9299 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_reshape pm initPM 862 1 9298 9300 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, by rw [rs]; rfl, by rw [r0]; rfl, by rw [r1]; rfl, by decide⟩
  rw [rs, h.value, r0, r1]
  exact fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape

/-- Pure-distributed exact 2-TP reshape of layer-11 attention output. -/
theorem recon_intermediateGoal_5237_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5237
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5237 5237 9299 9300
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_5237_rel initSM initPM hSM hPM hInit)

private theorem l11d_5238_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5238)
      (denoteGraphDistributed pm initPM 9305) (denoteGraphDistributed pm initPM 9306)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5237_rel initSM initPM hSM hPM hInit
  have rs := l11d_reshape sm initSM 401 0 5237 5238 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_reshape pm initPM 863 0 9299 9305 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_reshape pm initPM 864 1 9300 9306 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5238 = denoteGraphDistributed sm initSM 5237 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9305 = denoteGraphDistributed pm initPM 9299 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9306 = denoteGraphDistributed pm initPM 9300 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP identity reshape. -/
theorem recon_intermediateGoal_5238_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5238
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5238 5238 9305 9306
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_5238_rel initSM initPM hSM hPM hInit)

private theorem l11d_5240_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5240)
      (denoteGraphDistributed pm initPM 9309) (denoteGraphDistributed pm initPM 9310)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5238_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5239
    (by native_decide) 5239 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5239
    (by native_decide) 5239 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5239).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l11d_linear sm initSM 402 0 5238 5239 5240
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_linear pm initPM 865 0 9305 5239 9309
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_linear pm initPM 866 1 9306 5239 9310
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, ← r0, ← r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP layer-11 output projection. -/
theorem recon_intermediateGoal_5240_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5240
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5240 5240 9309 9310
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_5240_rel initSM initPM hSM hPM hInit)

private theorem l11d_5241_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5241)
      (denoteGraphDistributed pm initPM 9319) (denoteGraphDistributed pm initPM 9320)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5240_rel initSM initPM hSM hPM hInit
  have rs := l11d_view sm initSM 403 0 5240 5241 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_view pm initPM 867 0 9309 9319 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_view pm initPM 868 1 9310 9320 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5241 = denoteGraphDistributed sm initSM 5240 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9319 = denoteGraphDistributed pm initPM 9309 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9320 = denoteGraphDistributed pm initPM 9310 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP identity view. -/
theorem recon_intermediateGoal_5241_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5241
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5241 5241 9319 9320
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_5241_rel initSM initPM hSM hPM hInit)

private theorem l11d_5242_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5242)
      (denoteGraphDistributed pm initPM 9323) (denoteGraphDistributed pm initPM 9324)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5241_rel initSM initPM hSM hPM hInit
  have rs := l11d_float sm initSM 404 0 5241 5242 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_float pm initPM 869 0 9319 9323 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_float pm initPM 870 1 9320 9324 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP identity float. -/
theorem recon_intermediateGoal_5242_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5242
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5242 5242 9323 9324
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_5242_rel initSM initPM hSM hPM hInit)

private theorem l11d_7907_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7907)
      (denoteGraphDistributed pm initPM 15537) (denoteGraphDistributed pm initPM 15545)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5222 5222 9253 9254
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5222_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 392
    { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907], params := [2] }
    5222 7907 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5222 7903 7907 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 845
    { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537], params := [2] }
    9253 15537 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 9253 15533 15537 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 846
    { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545], params := [2] }
    9254 15545 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 9254 15541 15545 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, ← r0, ← r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP residual carry from `5222`. -/
theorem recon_intermediateGoal_7907_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7907
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7907 7907 15537 15545
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_7907_rel initSM initPM hSM hPM hInit)

/-- Pure-distributed exact 2-TP layer-11 residual add `7907 + 5242`. -/
theorem recon_intermediateGoal_5243_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5243
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := l11d_7907_rel initSM initPM hSM hPM hInit
  have hb := l11d_5242_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce2 sm initSM 405
    { rank := 0, op := "OpName.FW_add", ins := [7907, 5242], outs := [5243] }
    7907 5242 5243 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 7907 5242 5243)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 871
    { rank := 0, op := "OpName.FW_add", ins := [15537, 9323], outs := [9327] }
    15537 9323 9327 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 15537 9323 9327)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 872
    { rank := 1, op := "OpName.FW_add", ins := [15545, 9324], outs := [9328] }
    15545 9324 9328 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 15545 9324 9328)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5243 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 9327, denoteGraphDistributed pm initPM 9328] := by
    rw [rs, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← r0, ← r1]
  have hs0 : (denoteGraphDistributed pm initPM 9327).shape = [2048, 1024] := by
    rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 9328).shape = [2048, 1024] := by
    rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5243).shape = [4096, 1024] := by
    rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5243 5243 9327 9328
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide) hv hs hs0 hs1

#print axioms recon_intermediateGoal_5243_distributed

end TrainVerify.Denote.GeneratedPatterns
