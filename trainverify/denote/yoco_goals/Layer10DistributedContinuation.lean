/- Pure-distributed layer-10 router product/gating continuation. -/
import denote.yoco_goals.Layer9DistributedContinuation

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l10d_rms5191_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5191)
      (denoteGraphDistributed pm initPM 9145) (denoteGraphDistributed pm initPM 9146)
      [4096, 1024] [2048, 1024] :=
  Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5191 5191 9145 9146
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5191_distributed initSM initPM hSM hPM hInit)

private theorem l10d_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l10d_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l10d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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
private theorem l10d_sigmoid (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_sigmoid", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_sigmoid (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o fw_sigmoid hk hn (by simp)
    (fun st => applyNode_fw_sigmoid_out g st r i o []) hdn hdw hpn hpw

private theorem l10d_swiglu (g : GraphDecl) (init : Store) (k r x y o : Nat)
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

private theorem l10d_mul (g : GraphDecl) (init : Store) (k r x y o : Nat)
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

/-! ### L10 router expert side branches — `mref5-pos{2,3,4}(5191)` reshape/mixlin/view. -/

private theorem l10d_reshape5201_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5201)
      (denoteGraphDistributed pm initPM 9167) (denoteGraphDistributed pm initPM 9168)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_rms5191_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 369
    { rank := 0, op := "OpName.FW_multiref", ins := [5191],
      outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
    5191 7891 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out sm st 0 5191 7883 7887 7891 7895 7899
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 799
    { rank := 0, op := "OpName.FW_multiref", ins := [9145],
      outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
    9145 15498 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 0 9145 15490 15494 15498 15502 15506
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 800
    { rank := 1, op := "OpName.FW_multiref", ins := [9146],
      outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
    9146 15521 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 1 9146 15513 15517 15521 15525 15529
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l10d_reshape sm initSM 371 0 7891 5201 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_reshape pm initPM 802 0 15498 9167 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_reshape pm initPM 806 1 15521 9168 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5201 = denoteGraphDistributed sm initSM 7891 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9167 = denoteGraphDistributed pm initPM 15498 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9168 = denoteGraphDistributed pm initPM 15521 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos2(5191)` reshape. -/
theorem recon_intermediateGoal_5201_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5201
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5201 5201 9167 9168
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_reshape5201_rel initSM initPM hSM hPM hInit)

private theorem l10d_reshape5206_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5206)
      (denoteGraphDistributed pm initPM 9181) (denoteGraphDistributed pm initPM 9182)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_rms5191_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 369
    { rank := 0, op := "OpName.FW_multiref", ins := [5191],
      outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
    5191 7895 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out sm st 0 5191 7883 7887 7891 7895 7899
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 799
    { rank := 0, op := "OpName.FW_multiref", ins := [9145],
      outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
    9145 15502 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 0 9145 15490 15494 15498 15502 15506
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 800
    { rank := 1, op := "OpName.FW_multiref", ins := [9146],
      outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
    9146 15525 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 1 9146 15513 15517 15521 15525 15529
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l10d_reshape sm initSM 372 0 7895 5206 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_reshape pm initPM 803 0 15502 9181 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_reshape pm initPM 807 1 15525 9182 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5206 = denoteGraphDistributed sm initSM 7895 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9181 = denoteGraphDistributed pm initPM 15502 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9182 = denoteGraphDistributed pm initPM 15525 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos3(5191)` reshape. -/
theorem recon_intermediateGoal_5206_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5206
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5206 5206 9181 9182
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_reshape5206_rel initSM initPM hSM hPM hInit)

private theorem l10d_reshape5210_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5210)
      (denoteGraphDistributed pm initPM 9199) (denoteGraphDistributed pm initPM 9200)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_rms5191_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 369
    { rank := 0, op := "OpName.FW_multiref", ins := [5191],
      outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
    5191 7899 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out sm st 0 5191 7883 7887 7891 7895 7899
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 799
    { rank := 0, op := "OpName.FW_multiref", ins := [9145],
      outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
    9145 15506 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 0 9145 15490 15494 15498 15502 15506
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 800
    { rank := 1, op := "OpName.FW_multiref", ins := [9146],
      outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
    9146 15529 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 1 9146 15513 15517 15521 15525 15529
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l10d_reshape sm initSM 373 0 7899 5210 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_reshape pm initPM 804 0 15506 9199 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_reshape pm initPM 808 1 15529 9200 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5210 = denoteGraphDistributed sm initSM 7899 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9199 = denoteGraphDistributed pm initPM 15506 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9200 = denoteGraphDistributed pm initPM 15529 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos4(5191)` reshape. -/
theorem recon_intermediateGoal_5210_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5210
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5210 5210 9199 9200
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_reshape5210_rel initSM initPM hSM hPM hInit)

private theorem l10d_linear5203_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5203)
      (denoteGraphDistributed pm initPM 9171) (denoteGraphDistributed pm initPM 9172)
      [4096, 1] [2048, 1] := by
  have h := l10d_reshape5201_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5202
    (by native_decide) 5202 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5202
    (by native_decide) 5202 [1, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5202).shape = [1, 1024] := by rw [← hw]; exact hws
  have rs := l10d_linear sm initSM 375 0 5201 5202 5203
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_linear pm initPM 810 0 9167 5202 9171
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_linear pm initPM 814 1 9168 5202 9172
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5201, 5202)`. -/
theorem recon_intermediateGoal_5203_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5203
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5203 5203 9171 9172
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l10d_linear5203_rel initSM initPM hSM hPM hInit)

private theorem l10d_linear5208_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5208)
      (denoteGraphDistributed pm initPM 9185) (denoteGraphDistributed pm initPM 9186)
      [4096, 512] [2048, 512] := by
  have h := l10d_reshape5206_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5207
    (by native_decide) 5207 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5207
    (by native_decide) 5207 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5207).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l10d_linear sm initSM 376 0 5206 5207 5208
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_linear pm initPM 811 0 9181 5207 9185
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_linear pm initPM 815 1 9182 5207 9186
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5206, 5207)`. -/
theorem recon_intermediateGoal_5208_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5208
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5208 5208 9185 9186
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l10d_linear5208_rel initSM initPM hSM hPM hInit)

private theorem l10d_linear5212_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5212)
      (denoteGraphDistributed pm initPM 9203) (denoteGraphDistributed pm initPM 9204)
      [4096, 512] [2048, 512] := by
  have h := l10d_reshape5210_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5211
    (by native_decide) 5211 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5211
    (by native_decide) 5211 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5211).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l10d_linear sm initSM 377 0 5210 5211 5212
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_linear pm initPM 812 0 9199 5211 9203
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_linear pm initPM 816 1 9200 5211 9204
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5210, 5211)`. -/
theorem recon_intermediateGoal_5212_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5212
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5212 5212 9203 9204
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l10d_linear5212_rel initSM initPM hSM hPM hInit)

private theorem l10d_view5204_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5204)
      (denoteGraphDistributed pm initPM 9177) (denoteGraphDistributed pm initPM 9178)
      [4096, 1] [2048, 1] := by
  have h := l10d_linear5203_rel initSM initPM hSM hPM hInit
  have rs := l10d_view sm initSM 379 0 5203 5204 4096 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_view pm initPM 818 0 9171 9177 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_view pm initPM 822 1 9172 9178 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5204 = denoteGraphDistributed sm initSM 5203 := by
    rw [rs, fw_view_id_shape [4096, 1] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9177 = denoteGraphDistributed pm initPM 9171 := by
    rw [r0, fw_view_id_shape [2048, 1] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9178 = denoteGraphDistributed pm initPM 9172 := by
    rw [r1, fw_view_id_shape [2048, 1] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,1] (5203)`. -/
theorem recon_intermediateGoal_5204_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5204
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5204 5204 9177 9178
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l10d_view5204_rel initSM initPM hSM hPM hInit)

private theorem l10d_view5209_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5209)
      (denoteGraphDistributed pm initPM 9195) (denoteGraphDistributed pm initPM 9196)
      [4096, 512] [2048, 512] := by
  have h := l10d_linear5208_rel initSM initPM hSM hPM hInit
  have rs := l10d_view sm initSM 380 0 5208 5209 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_view pm initPM 819 0 9185 9195 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_view pm initPM 823 1 9186 9196 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5209 = denoteGraphDistributed sm initSM 5208 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9195 = denoteGraphDistributed pm initPM 9185 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9196 = denoteGraphDistributed pm initPM 9186 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,512] (5208)`. -/
theorem recon_intermediateGoal_5209_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5209
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5209 5209 9195 9196
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l10d_view5209_rel initSM initPM hSM hPM hInit)

private theorem l10d_view5213_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5213)
      (denoteGraphDistributed pm initPM 9213) (denoteGraphDistributed pm initPM 9214)
      [4096, 512] [2048, 512] := by
  have h := l10d_linear5212_rel initSM initPM hSM hPM hInit
  have rs := l10d_view sm initSM 381 0 5212 5213 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_view pm initPM 820 0 9203 9213 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_view pm initPM 824 1 9204 9214 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5213 = denoteGraphDistributed sm initSM 5212 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9213 = denoteGraphDistributed pm initPM 9203 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9214 = denoteGraphDistributed pm initPM 9204 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,512] (5212)`. -/
theorem recon_intermediateGoal_5213_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5213
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5213 5213 9213 9214
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l10d_view5213_rel initSM initPM hSM hPM hInit)

/-! ### Layer-10 gate/expert postprocessing, pure-distributed exact 2-TP. -/

private theorem l10d_sigmoid5205_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5205)
      (denoteGraphDistributed pm initPM 9179) (denoteGraphDistributed pm initPM 9180)
      [4096, 1] [2048, 1] := by
  have h := l10d_view5204_rel initSM initPM hSM hPM hInit
  have rs := l10d_sigmoid sm initSM 383 0 5204 5205
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_sigmoid pm initPM 826 0 9177 9179
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_sigmoid pm initPM 829 1 9178 9180
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_sigmoid_allGather0_commute_2 _ _ 2048 1
      (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs, fw_sigmoid_shape]; exact h.full_shape
  · rw [r0, fw_sigmoid_shape]; exact h.shard0_shape
  · rw [r1, fw_sigmoid_shape]; exact h.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of gate sigmoid `fw_sigmoid(5204)`. -/
theorem recon_intermediateGoal_5205_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5205
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5205 5205 9179 9180
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l10d_sigmoid5205_rel initSM initPM hSM hPM hInit)

private theorem l10d_swiglu5214_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5214)
      (denoteGraphDistributed pm initPM 9217) (denoteGraphDistributed pm initPM 9218)
      [4096, 512] [2048, 512] := by
  have hx := l10d_view5209_rel initSM initPM hSM hPM hInit
  have hy := l10d_view5213_rel initSM initPM hSM hPM hInit
  have rs := l10d_swiglu sm initSM 384 0 5209 5213 5214
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_swiglu pm initPM 827 0 9195 9213 9217
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_swiglu pm initPM 830 1 9196 9214 9218
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs, fw_swiglu_shape]; exact hy.full_shape
  · rw [r0, fw_swiglu_shape]; exact hy.shard0_shape
  · rw [r1, fw_swiglu_shape]; exact hy.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of expert `fw_swiglu(5209, 5213)`. -/
theorem recon_intermediateGoal_5214_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5214
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5214 5214 9217 9218
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l10d_swiglu5214_rel initSM initPM hSM hPM hInit)

private theorem l10d_reshape5215_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5215)
      (denoteGraphDistributed pm initPM 9219) (denoteGraphDistributed pm initPM 9220)
      [4096, 512] [2048, 512] := by
  have h := l10d_swiglu5214_rel initSM initPM hSM hPM hInit
  have rs := l10d_reshape sm initSM 385 0 5214 5215 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_reshape pm initPM 831 0 9217 9219 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_reshape pm initPM 832 1 9218 9220 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5215 = denoteGraphDistributed sm initSM 5214 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9219 = denoteGraphDistributed pm initPM 9217 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9220 = denoteGraphDistributed pm initPM 9218 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert reshape `5215`. -/
theorem recon_intermediateGoal_5215_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5215
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5215 5215 9219 9220
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l10d_reshape5215_rel initSM initPM hSM hPM hInit)

private theorem l10d_linear5217_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5217)
      (denoteGraphDistributed pm initPM 9225) (denoteGraphDistributed pm initPM 9226)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_reshape5215_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5216
    (by native_decide) 5216 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5216
    (by native_decide) 5216 [1024, 512] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5216).shape = [1024, 512] := by
    rw [← hw]; exact hws
  have rs := l10d_linear sm initSM 386 0 5215 5216 5217
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_linear pm initPM 833 0 9219 5216 9225
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_linear pm initPM 834 1 9220 5216 9226
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 512 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert output linear `5217`. -/
theorem recon_intermediateGoal_5217_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5217
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5217 5217 9225 9226
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_linear5217_rel initSM initPM hSM hPM hInit)

private theorem l10d_view5218_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5218)
      (denoteGraphDistributed pm initPM 9235) (denoteGraphDistributed pm initPM 9236)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_linear5217_rel initSM initPM hSM hPM hInit
  have rs := l10d_view sm initSM 387 0 5217 5218 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_view pm initPM 835 0 9225 9235 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_view pm initPM 836 1 9226 9236 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5218 = denoteGraphDistributed sm initSM 5217 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9235 = denoteGraphDistributed pm initPM 9225 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9236 = denoteGraphDistributed pm initPM 9226 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `5218`. -/
theorem recon_intermediateGoal_5218_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5218
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5218 5218 9235 9236
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_view5218_rel initSM initPM hSM hPM hInit)

private theorem l10d_mul_shape (x y : Tensor) (s h : Nat) (hh : 1 ≤ h)
    (hx : x.shape = [s, 1]) (hy : y.shape = [s, h]) :
    (elemwiseMul x y).shape = [s, h] := by
  simp [elemwiseMul, Tensor.mkShape, outShape2, hx, hy, Nat.max_eq_right hh]

private theorem l10d_mul5219_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5219)
      (denoteGraphDistributed pm initPM 9239) (denoteGraphDistributed pm initPM 9240)
      [4096, 1024] [2048, 1024] := by
  have hx := l10d_sigmoid5205_rel initSM initPM hSM hPM hInit
  have hy := l10d_view5218_rel initSM initPM hSM hPM hInit
  have rs := l10d_mul sm initSM 388 0 5205 5218 5219
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_mul pm initPM 837 0 9179 9235 9239
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_mul pm initPM 838 1 9180 9236 9240
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024
        (by omega) (by omega) (by decide) (by decide) (by decide)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs]; exact l10d_mul_shape _ _ 4096 1024 (by omega) hx.full_shape hy.full_shape
  · rw [r0]; exact l10d_mul_shape _ _ 2048 1024 (by omega) hx.shard0_shape hy.shard0_shape
  · rw [r1]; exact l10d_mul_shape _ _ 2048 1024 (by omega) hx.shard1_shape hy.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of gate/expert broadcast product `5219`. -/
theorem recon_intermediateGoal_5219_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5219
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5219 5219 9239 9240
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_mul5219_rel initSM initPM hSM hPM hInit)
#print axioms recon_intermediateGoal_5219_distributed

end TrainVerify.Denote.GeneratedPatterns
