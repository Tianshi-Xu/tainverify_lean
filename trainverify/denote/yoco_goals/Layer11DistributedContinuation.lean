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

/-! ### Layer-11 router front, pure-distributed exact 2-TP. -/

private theorem l11d_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l11d_norm_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l11d_5245_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5245)
      (denoteGraphDistributed pm initPM 9331) (denoteGraphDistributed pm initPM 9332)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5243 5243 9327 9328
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5243_distributed initSM initPM hSM hPM hInit)
  have ms := distributed_reduce1 sm initSM 406
    { rank := 0, op := "OpName.FW_multiref", ins := [5243], outs := [7924, 7928], params := [2] }
    5243 7924 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5243 7924 7928)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 873
    { rank := 0, op := "OpName.FW_multiref", ins := [9327], outs := [15575, 15579], params := [2] }
    9327 15575 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 9327 15575 15579)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 874
    { rank := 1, op := "OpName.FW_multiref", ins := [9328], outs := [15583, 15587], params := [2] }
    9328 15583 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 9328 15583 15587)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5244
    (by native_decide) 5244 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l11d_rms sm initSM 407 0 7924 5244 5245
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_rms pm initPM 875 0 15575 5244 9331
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_rms pm initPM 876 1 15583 5244 9332
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15575).shape = [2048, 1024] := by
    rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15583).shape = [2048, 1024] := by
    rw [m1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ms, h.value, ← m0, ← m1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      ← r0, ← r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed layer-11 RMSNorm of the first residual copy. -/
theorem recon_intermediateGoal_5245_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5245
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5245 5245 9331 9332
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_5245_rel initSM initPM hSM hPM hInit)

private theorem l11d_5246_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5246)
      (denoteGraphDistributed pm initPM 9333) (denoteGraphDistributed pm initPM 9334)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5245_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 408
    { rank := 0, op := "OpName.FW_multiref", ins := [5245],
      outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
    5245 7935 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' sm st 0 4 5245 7935 [7939, 7943, 7947, 7951])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 877
    { rank := 0, op := "OpName.FW_multiref", ins := [9331],
      outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
    9331 15594 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 0 4 9331 15594 [15598, 15602, 15606, 15610])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 878
    { rank := 1, op := "OpName.FW_multiref", ins := [9332],
      outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
    9332 15617 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 1 4 9332 15617 [15621, 15625, 15629, 15633])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have rs := l11d_float sm initSM 409 0 7935 5246
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_float pm initPM 879 0 15594 9333
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_float pm initPM 883 1 15617 9334
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  exact ⟨by rw [rs, ms, h.value, ← m0, ← m1, ← r0, ← r1],
    by rw [rs, ms]; exact h.full_shape, by rw [r0, m0]; exact h.shard0_shape,
    by rw [r1, m1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed first router float input. -/
theorem recon_intermediateGoal_5246_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5246
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5246 5246 9333 9334
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_5246_rel initSM initPM hSM hPM hInit)

private theorem l11d_5248_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5248)
      (denoteGraphDistributed pm initPM 9339) (denoteGraphDistributed pm initPM 9340)
      [4096, 64] [2048, 64] := by
  have h := l11d_5246_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5247
    (by native_decide) 5247 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5247
    (by native_decide) 5247 [64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5247).shape = [64, 1024] := by
    rw [← hw]; exact hws
  have rs := l11d_norm_linear sm initSM 413 0 5246 5247 5248
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_norm_linear pm initPM 887 0 9333 5247 9339
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_norm_linear pm initPM 891 1 9334 5247 9340
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

/-- Pure-distributed layer-11 router logits. -/
theorem recon_intermediateGoal_5248_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5248
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5248 5248 9339 9340
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l11d_5248_rel initSM initPM hSM hPM hInit)

private theorem l11d_topk_common (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5248)
      (denoteGraphDistributed pm initPM 9339) (denoteGraphDistributed pm initPM 9340)
      [4096, 64] [2048, 64]
    ∧ ((sm.nodes.take 417).foldl (applyNodeDistributed sm) initSM 5248).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 895).foldl (applyNodeDistributed pm) initPM 9339).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 899).foldl (applyNodeDistributed pm) initPM 9340).shape.reverse.head? = some 64 := by
  have h := l11d_5248_rel initSM initPM hSM hPM hInit
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [foldl_take_distributed_eq sm initSM 5248 417 (by native_decide) (by native_decide),
      h.full_shape]
    rfl
  · rw [foldl_take_distributed_eq pm initPM 9339 895 (by native_decide) (by native_decide),
      h.shard0_shape]
    rfl
  · rw [foldl_take_distributed_eq pm initPM 9340 899 (by native_decide) (by native_decide),
      h.shard1_shape]
    rfl

private theorem l11d_topk_fst (g : GraphDecl) (init : Store) (k r i o0 o1 o2 : Nat)
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

private theorem l11d_topk_snd (g : GraphDecl) (init : Store) (k r i o0 o1 o2 : Nat)
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

/-- Pure-distributed layer-11 top-k routing probabilities. -/
theorem recon_intermediateGoal_5249_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5249
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  obtain ⟨h, hs, h0, h1⟩ := l11d_topk_common initSM initPM hSM hPM hInit
  have rs := l11d_topk_fst sm initSM 417 0 5248 5249 5250 5251 hs
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_topk_fst pm initPM 895 0 9339 9341 9343 9345 h0
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_topk_fst pm initPM 899 1 9340 9342 9344 9346 h1
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5249 5249 9341 9342
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Pure-distributed layer-11 top-k routing map. -/
theorem recon_intermediateGoal_5250_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5250
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  obtain ⟨h, hs, h0, h1⟩ := l11d_topk_common initSM initPM hSM hPM hInit
  have rs := l11d_topk_snd sm initSM 417 0 5248 5249 5250 5251 hs (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_topk_snd pm initPM 895 0 9339 9341 9343 9345 h0 (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_topk_snd pm initPM 899 1 9340 9342 9344 9346 h1 (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5250 5250 9343 9344
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

#print axioms recon_intermediateGoal_5249_distributed
#print axioms recon_intermediateGoal_5250_distributed

/-! ### Layer-11 router product/gating continuation, pure-distributed exact 2-TP. -/

private theorem l11d_sigmoid (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_sigmoid", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_sigmoid (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o fw_sigmoid hk hn (by simp)
    (fun st => applyNode_fw_sigmoid_out g st r i o []) hdn hdw hpn hpw

private theorem l11d_swiglu (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_swiglu", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_swiglu (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  distributed_reduce2 g init k _ x y o fw_swiglu hk hn (by simp)
    (fun st => applyNode_fw_swiglu_out g st r x y o []) hdn hdw hpn hpx hpy

private theorem l11d_mul (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mul", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o =
      elemwiseMul (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  distributed_reduce2 g init k _ x y o elemwiseMul hk hn (by simp)
    (fun st => applyNode_fw_mul_out g st r x y o) hdn hdw hpn hpx hpy

/-! ### L11 router expert side branches — `mref5-pos{2,3,4}(5245)` reshape/mixlin/view. -/

private theorem l11d_reshape5255_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5255)
      (denoteGraphDistributed pm initPM 9353) (denoteGraphDistributed pm initPM 9354)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5245_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 408
    { rank := 0, op := "OpName.FW_multiref", ins := [5245],
      outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
    5245 7943 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out sm st 0 5245 7935 7939 7943 7947 7951
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 877
    { rank := 0, op := "OpName.FW_multiref", ins := [9331],
      outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
    9331 15602 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 0 9331 15594 15598 15602 15606 15610
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 878
    { rank := 1, op := "OpName.FW_multiref", ins := [9332],
      outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
    9332 15625 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 1 9332 15617 15621 15625 15629 15633
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l11d_reshape sm initSM 410 0 7943 5255 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_reshape pm initPM 880 0 15602 9353 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_reshape pm initPM 884 1 15625 9354 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5255 = denoteGraphDistributed sm initSM 7943 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9353 = denoteGraphDistributed pm initPM 15602 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9354 = denoteGraphDistributed pm initPM 15625 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos2(5245)` reshape. -/
theorem recon_intermediateGoal_5255_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5255
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5255 5255 9353 9354
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_reshape5255_rel initSM initPM hSM hPM hInit)

private theorem l11d_reshape5260_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5260)
      (denoteGraphDistributed pm initPM 9367) (denoteGraphDistributed pm initPM 9368)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5245_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 408
    { rank := 0, op := "OpName.FW_multiref", ins := [5245],
      outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
    5245 7947 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out sm st 0 5245 7935 7939 7943 7947 7951
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 877
    { rank := 0, op := "OpName.FW_multiref", ins := [9331],
      outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
    9331 15606 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 0 9331 15594 15598 15602 15606 15610
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 878
    { rank := 1, op := "OpName.FW_multiref", ins := [9332],
      outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
    9332 15629 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 1 9332 15617 15621 15625 15629 15633
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l11d_reshape sm initSM 411 0 7947 5260 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_reshape pm initPM 881 0 15606 9367 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_reshape pm initPM 885 1 15629 9368 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5260 = denoteGraphDistributed sm initSM 7947 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9367 = denoteGraphDistributed pm initPM 15606 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9368 = denoteGraphDistributed pm initPM 15629 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos3(5245)` reshape. -/
theorem recon_intermediateGoal_5260_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5260
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5260 5260 9367 9368
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_reshape5260_rel initSM initPM hSM hPM hInit)

private theorem l11d_reshape5264_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5264)
      (denoteGraphDistributed pm initPM 9385) (denoteGraphDistributed pm initPM 9386)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5245_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 408
    { rank := 0, op := "OpName.FW_multiref", ins := [5245],
      outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
    5245 7951 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out sm st 0 5245 7935 7939 7943 7947 7951
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 877
    { rank := 0, op := "OpName.FW_multiref", ins := [9331],
      outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
    9331 15610 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 0 9331 15594 15598 15602 15606 15610
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 878
    { rank := 1, op := "OpName.FW_multiref", ins := [9332],
      outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
    9332 15633 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 1 9332 15617 15621 15625 15629 15633
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l11d_reshape sm initSM 412 0 7951 5264 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_reshape pm initPM 882 0 15610 9385 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_reshape pm initPM 886 1 15633 9386 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5264 = denoteGraphDistributed sm initSM 7951 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9385 = denoteGraphDistributed pm initPM 15610 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9386 = denoteGraphDistributed pm initPM 15633 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos4(5245)` reshape. -/
theorem recon_intermediateGoal_5264_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5264
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5264 5264 9385 9386
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_reshape5264_rel initSM initPM hSM hPM hInit)

private theorem l11d_linear5257_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5257)
      (denoteGraphDistributed pm initPM 9357) (denoteGraphDistributed pm initPM 9358)
      [4096, 1] [2048, 1] := by
  have h := l11d_reshape5255_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5256
    (by native_decide) 5256 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5256
    (by native_decide) 5256 [1, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5256).shape = [1, 1024] := by rw [← hw]; exact hws
  have rs := l11d_linear sm initSM 414 0 5255 5256 5257
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_linear pm initPM 888 0 9353 5256 9357
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_linear pm initPM 892 1 9354 5256 9358
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5255, 5256)`. -/
theorem recon_intermediateGoal_5257_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5257
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5257 5257 9357 9358
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l11d_linear5257_rel initSM initPM hSM hPM hInit)

private theorem l11d_linear5262_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5262)
      (denoteGraphDistributed pm initPM 9371) (denoteGraphDistributed pm initPM 9372)
      [4096, 512] [2048, 512] := by
  have h := l11d_reshape5260_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5261
    (by native_decide) 5261 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5261
    (by native_decide) 5261 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5261).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l11d_linear sm initSM 415 0 5260 5261 5262
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_linear pm initPM 889 0 9367 5261 9371
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_linear pm initPM 893 1 9368 5261 9372
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5260, 5261)`. -/
theorem recon_intermediateGoal_5262_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5262
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5262 5262 9371 9372
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l11d_linear5262_rel initSM initPM hSM hPM hInit)

private theorem l11d_linear5266_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5266)
      (denoteGraphDistributed pm initPM 9389) (denoteGraphDistributed pm initPM 9390)
      [4096, 512] [2048, 512] := by
  have h := l11d_reshape5264_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5265
    (by native_decide) 5265 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5265
    (by native_decide) 5265 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5265).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l11d_linear sm initSM 416 0 5264 5265 5266
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_linear pm initPM 890 0 9385 5265 9389
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_linear pm initPM 894 1 9386 5265 9390
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5264, 5265)`. -/
theorem recon_intermediateGoal_5266_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5266
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5266 5266 9389 9390
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l11d_linear5266_rel initSM initPM hSM hPM hInit)

private theorem l11d_view5258_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5258)
      (denoteGraphDistributed pm initPM 9363) (denoteGraphDistributed pm initPM 9364)
      [4096, 1] [2048, 1] := by
  have h := l11d_linear5257_rel initSM initPM hSM hPM hInit
  have rs := l11d_view sm initSM 418 0 5257 5258 4096 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_view pm initPM 896 0 9357 9363 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_view pm initPM 900 1 9358 9364 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5258 = denoteGraphDistributed sm initSM 5257 := by
    rw [rs, fw_view_id_shape [4096, 1] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9363 = denoteGraphDistributed pm initPM 9357 := by
    rw [r0, fw_view_id_shape [2048, 1] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9364 = denoteGraphDistributed pm initPM 9358 := by
    rw [r1, fw_view_id_shape [2048, 1] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,1] (5257)`. -/
theorem recon_intermediateGoal_5258_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5258
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5258 5258 9363 9364
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l11d_view5258_rel initSM initPM hSM hPM hInit)

private theorem l11d_view5263_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5263)
      (denoteGraphDistributed pm initPM 9381) (denoteGraphDistributed pm initPM 9382)
      [4096, 512] [2048, 512] := by
  have h := l11d_linear5262_rel initSM initPM hSM hPM hInit
  have rs := l11d_view sm initSM 419 0 5262 5263 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_view pm initPM 897 0 9371 9381 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_view pm initPM 901 1 9372 9382 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5263 = denoteGraphDistributed sm initSM 5262 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9381 = denoteGraphDistributed pm initPM 9371 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9382 = denoteGraphDistributed pm initPM 9372 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,512] (5262)`. -/
theorem recon_intermediateGoal_5263_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5263
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5263 5263 9381 9382
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l11d_view5263_rel initSM initPM hSM hPM hInit)

private theorem l11d_view5267_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5267)
      (denoteGraphDistributed pm initPM 9399) (denoteGraphDistributed pm initPM 9400)
      [4096, 512] [2048, 512] := by
  have h := l11d_linear5266_rel initSM initPM hSM hPM hInit
  have rs := l11d_view sm initSM 420 0 5266 5267 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_view pm initPM 898 0 9389 9399 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_view pm initPM 902 1 9390 9400 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5267 = denoteGraphDistributed sm initSM 5266 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9399 = denoteGraphDistributed pm initPM 9389 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9400 = denoteGraphDistributed pm initPM 9390 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,512] (5266)`. -/
theorem recon_intermediateGoal_5267_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5267
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5267 5267 9399 9400
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l11d_view5267_rel initSM initPM hSM hPM hInit)

/-! ### Layer-11 gate/expert postprocessing, pure-distributed exact 2-TP. -/

private theorem l11d_sigmoid5259_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5259)
      (denoteGraphDistributed pm initPM 9365) (denoteGraphDistributed pm initPM 9366)
      [4096, 1] [2048, 1] := by
  have h := l11d_view5258_rel initSM initPM hSM hPM hInit
  have rs := l11d_sigmoid sm initSM 422 0 5258 5259
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_sigmoid pm initPM 904 0 9363 9365
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_sigmoid pm initPM 907 1 9364 9366
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_sigmoid_allGather0_commute_2 _ _ 2048 1
      (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs, fw_sigmoid_shape]; exact h.full_shape
  · rw [r0, fw_sigmoid_shape]; exact h.shard0_shape
  · rw [r1, fw_sigmoid_shape]; exact h.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of gate sigmoid `fw_sigmoid(5258)`. -/
theorem recon_intermediateGoal_5259_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5259
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5259 5259 9365 9366
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l11d_sigmoid5259_rel initSM initPM hSM hPM hInit)

private theorem l11d_swiglu5268_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5268)
      (denoteGraphDistributed pm initPM 9403) (denoteGraphDistributed pm initPM 9404)
      [4096, 512] [2048, 512] := by
  have hx := l11d_view5263_rel initSM initPM hSM hPM hInit
  have hy := l11d_view5267_rel initSM initPM hSM hPM hInit
  have rs := l11d_swiglu sm initSM 423 0 5263 5267 5268
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_swiglu pm initPM 905 0 9381 9399 9403
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_swiglu pm initPM 908 1 9382 9400 9404
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs, fw_swiglu_shape]; exact hy.full_shape
  · rw [r0, fw_swiglu_shape]; exact hy.shard0_shape
  · rw [r1, fw_swiglu_shape]; exact hy.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of expert `fw_swiglu(5263, 5267)`. -/
theorem recon_intermediateGoal_5268_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5268
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5268 5268 9403 9404
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l11d_swiglu5268_rel initSM initPM hSM hPM hInit)

private theorem l11d_reshape5269_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5269)
      (denoteGraphDistributed pm initPM 9405) (denoteGraphDistributed pm initPM 9406)
      [4096, 512] [2048, 512] := by
  have h := l11d_swiglu5268_rel initSM initPM hSM hPM hInit
  have rs := l11d_reshape sm initSM 424 0 5268 5269 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_reshape pm initPM 909 0 9403 9405 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_reshape pm initPM 910 1 9404 9406 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5269 = denoteGraphDistributed sm initSM 5268 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9405 = denoteGraphDistributed pm initPM 9403 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9406 = denoteGraphDistributed pm initPM 9404 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert reshape `5269`. -/
theorem recon_intermediateGoal_5269_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5269
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5269 5269 9405 9406
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l11d_reshape5269_rel initSM initPM hSM hPM hInit)

private theorem l11d_linear5271_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5271)
      (denoteGraphDistributed pm initPM 9411) (denoteGraphDistributed pm initPM 9412)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_reshape5269_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5270
    (by native_decide) 5270 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5270
    (by native_decide) 5270 [1024, 512] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5270).shape = [1024, 512] := by
    rw [← hw]; exact hws
  have rs := l11d_linear sm initSM 425 0 5269 5270 5271
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_linear pm initPM 911 0 9405 5270 9411
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_linear pm initPM 912 1 9406 5270 9412
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 512 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert output linear `5271`. -/
theorem recon_intermediateGoal_5271_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5271
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5271 5271 9411 9412
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_linear5271_rel initSM initPM hSM hPM hInit)

private theorem l11d_view5272_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5272)
      (denoteGraphDistributed pm initPM 9421) (denoteGraphDistributed pm initPM 9422)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_linear5271_rel initSM initPM hSM hPM hInit
  have rs := l11d_view sm initSM 426 0 5271 5272 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l11d_view pm initPM 913 0 9411 9421 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l11d_view pm initPM 914 1 9412 9422 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5272 = denoteGraphDistributed sm initSM 5271 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9421 = denoteGraphDistributed pm initPM 9411 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9422 = denoteGraphDistributed pm initPM 9412 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `5272`. -/
theorem recon_intermediateGoal_5272_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5272
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5272 5272 9421 9422
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_view5272_rel initSM initPM hSM hPM hInit)

private theorem l11d_mul_shape (x y : Tensor) (s h : Nat) (hh : 1 ≤ h)
    (hx : x.shape = [s, 1]) (hy : y.shape = [s, h]) :
    (elemwiseMul x y).shape = [s, h] := by
  simp [elemwiseMul, Tensor.mkShape, outShape2, hx, hy, Nat.max_eq_right hh]

private theorem l11d_mul5273_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5273)
      (denoteGraphDistributed pm initPM 9425) (denoteGraphDistributed pm initPM 9426)
      [4096, 1024] [2048, 1024] := by
  have hx := l11d_sigmoid5259_rel initSM initPM hSM hPM hInit
  have hy := l11d_view5272_rel initSM initPM hSM hPM hInit
  have rs := l11d_mul sm initSM 427 0 5259 5272 5273
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11d_mul pm initPM 915 0 9365 9421 9425
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11d_mul pm initPM 916 1 9366 9422 9426
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024
        (by omega) (by omega) (by decide) (by decide) (by decide)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs]; exact l11d_mul_shape _ _ 4096 1024 (by omega) hx.full_shape hy.full_shape
  · rw [r0]; exact l11d_mul_shape _ _ 2048 1024 (by omega) hx.shard0_shape hy.shard0_shape
  · rw [r1]; exact l11d_mul_shape _ _ 2048 1024 (by omega) hx.shard1_shape hy.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of gate/expert broadcast product `5273`. -/
theorem recon_intermediateGoal_5273_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5273
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5273 5273 9425 9426
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_mul5273_rel initSM initPM hSM hPM hInit)
#print axioms recon_intermediateGoal_5273_distributed

/-! ### Layer-11 faithful full-expert MoE, pure-distributed exact 2-TP. -/

private theorem l11d_token7939_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7939)
      (denoteGraphDistributed pm initPM 15598) (denoteGraphDistributed pm initPM 15621)
      [4096, 1024] [2048, 1024] := by
  have h := l11d_5245_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 408
    { rank := 0, op := "OpName.FW_multiref", ins := [5245],
      outs := [7935, 7939, 7943, 7947, 7951], params := [5] }
    5245 7939 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 5245 7935 7939 7943 7947 7951
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 877
    { rank := 0, op := "OpName.FW_multiref", ins := [9331],
      outs := [15594, 15598, 15602, 15606, 15610], params := [5] }
    9331 15598 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 9331 15594 15598 15602 15606 15610
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 878
    { rank := 1, op := "OpName.FW_multiref", ins := [9332],
      outs := [15617, 15621, 15625, 15629, 15633], params := [5] }
    9332 15621 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 9332 15617 15621 15625 15629 15633
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP bridge for `mref5-pos1(5245)`. -/
theorem recon_intermediateGoal_7939_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7939
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7939 7939 15598 15621
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l11d_token7939_rel initSM initPM hSM hPM hInit)

private def layer11SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7939, 5249, 5250, 5252, 5253], outs := [5254], params := [64, 0, 64, 8] }
private def layer11PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [15598, 9341, 9343, 9347, 9349], outs := [9351], params := [64, 0, 32, 8] }
private def layer11PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [15621, 9342, 9344, 9348, 9350], outs := [9352], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer11_sm_node421 : sm.nodes[421]'(by native_decide) = layer11SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer11_pm_node903 : pm.nodes[903]'(by native_decide) = layer11PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer11_pm_node906 : pm.nodes[906]'(by native_decide) = layer11PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer11_sm_buddies : sm.replicaBuddies layer11SmMoe = [layer11SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer11_pm_buddies0 :
    pm.replicaBuddies layer11PmMoe0 = [layer11PmMoe0, layer11PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer11_pm_buddies1 :
    pm.replicaBuddies layer11PmMoe1 = [layer11PmMoe0, layer11PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful pure-distributed full-expert reconstruction of the layer-11 MoE boundary. -/
theorem recon_intermediateGoal_5254_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5254
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l11d_token7939_rel initSM initPM hSM hPM hInit
  have hrp := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5249 5249 9341 9342
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5249_distributed initSM initPM hSM hPM hInit)
  have hrm := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5250 5250 9343 9344
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5250_distributed initSM initPM hSM hPM hInit)
  have hW13 := hInit initGoal_5252 (by native_decide)
  have hW2 := hInit initGoal_5253 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_5252, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_5253, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 9347).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9347
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 9348).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9348
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 9349).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9349
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 9350).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9350
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 5252 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9347, denoteGraphDistributed pm initPM 9348] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5252 pm.numRanks _ rfl] at hv
    simp only [initGoal_5252, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5252 = initSM 5252 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5252
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 9347 = initPM 9347 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9347
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 9348 = initPM 9348 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9348
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 5253 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9349, denoteGraphDistributed pm initPM 9350] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5253 pm.numRanks _ rfl] at hv
    simp only [initGoal_5253, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5253 = initSM 5253 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5253
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 9349 = initPM 9349 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9349
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 9350 = initPM 9350 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9350
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5252] =
      denoteGraphDistributed sm initSM 5252 := by
    have hs : (denoteGraphDistributed sm initSM 5252).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5253] =
      denoteGraphDistributed sm initSM 5253 := by
    have hs : (denoteGraphDistributed sm initSM 5253).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hSMout : denoteGraphDistributed sm initSM 5254 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7939)
        (denoteGraphDistributed sm initSM 5249) (denoteGraphDistributed sm initSM 5250)
        [denoteGraphDistributed pm initPM 9347, denoteGraphDistributed pm initPM 9348]
        [denoteGraphDistributed pm initPM 9349, denoteGraphDistributed pm initPM 9350]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 421 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 421 layer11SmMoe 5254 hk
      (show sm.nodes[421]'hk = layer11SmMoe from layer11_sm_node421)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer11_sm_buddies]
    simp only [layer11SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7939 421 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5249 421 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5250 421 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5252 421 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5253 421 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 9351 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15598)
        (denoteGraphDistributed pm initPM 9341) (denoteGraphDistributed pm initPM 9343)
        [denoteGraphDistributed pm initPM 9347, denoteGraphDistributed pm initPM 9348]
        [denoteGraphDistributed pm initPM 9349, denoteGraphDistributed pm initPM 9350]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 903 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 903 layer11PmMoe0 9351 hk
      (show pm.nodes[903]'hk = layer11PmMoe0 from layer11_pm_node903)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer11_pm_buddies0]
    simp only [layer11PmMoe0, layer11PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15598 903 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9341 903 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9343 903 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9347 903 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9348 903 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9349 903 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9350 903 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 9352 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15621)
        (denoteGraphDistributed pm initPM 9342) (denoteGraphDistributed pm initPM 9344)
        [denoteGraphDistributed pm initPM 9347, denoteGraphDistributed pm initPM 9348]
        [denoteGraphDistributed pm initPM 9349, denoteGraphDistributed pm initPM 9350]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 906 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 906 layer11PmMoe1 9352 hk
      (show pm.nodes[906]'hk = layer11PmMoe1 from layer11_pm_node906)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer11_pm_buddies1]
    simp only [layer11PmMoe0, layer11PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15621 906 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9342 906 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9344 906 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9347 906 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9348 906 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9349 906 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9350 906 (by native_decide) (by native_decide)]
  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 15598) (denoteGraphDistributed pm initPM 15621)
    (denoteGraphDistributed pm initPM 9341) (denoteGraphDistributed pm initPM 9342)
    (denoteGraphDistributed pm initPM 9343) (denoteGraphDistributed pm initPM 9344)
    (denoteGraphDistributed pm initPM 9347) (denoteGraphDistributed pm initPM 9348)
    (denoteGraphDistributed pm initPM 9349) (denoteGraphDistributed pm initPM 9350)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 5254 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 9351, denoteGraphDistributed pm initPM 9352] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 9351).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15598)
      (rp := denoteGraphDistributed pm initPM 9341)
      (rm := denoteGraphDistributed pm initPM 9343)
      (w13s := [denoteGraphDistributed pm initPM 9347, denoteGraphDistributed pm initPM 9348])
      (w2s := [denoteGraphDistributed pm initPM 9349, denoteGraphDistributed pm initPM 9350])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 9352).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15621)
      (rp := denoteGraphDistributed pm initPM 9342)
      (rm := denoteGraphDistributed pm initPM 9344)
      (w13s := [denoteGraphDistributed pm initPM 9347, denoteGraphDistributed pm initPM 9348])
      (w2s := [denoteGraphDistributed pm initPM 9349, denoteGraphDistributed pm initPM 9350])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 5254).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5254 5254 9351 9352
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

#print axioms recon_intermediateGoal_7939_distributed
#print axioms recon_intermediateGoal_5254_distributed

end TrainVerify.Denote.GeneratedPatterns
