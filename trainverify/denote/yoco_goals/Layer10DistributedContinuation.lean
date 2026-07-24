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

/-! ### Layer-10 faithful full-expert MoE, pure-distributed exact 2-TP. -/

private theorem l10d_token7887_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7887)
      (denoteGraphDistributed pm initPM 15494) (denoteGraphDistributed pm initPM 15517)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_rms5191_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 369
    { rank := 0, op := "OpName.FW_multiref", ins := [5191],
      outs := [7883, 7887, 7891, 7895, 7899], params := [5] }
    5191 7887 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 5191 7883 7887 7891 7895 7899
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 799
    { rank := 0, op := "OpName.FW_multiref", ins := [9145],
      outs := [15490, 15494, 15498, 15502, 15506], params := [5] }
    9145 15494 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 9145 15490 15494 15498 15502 15506
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 800
    { rank := 1, op := "OpName.FW_multiref", ins := [9146],
      outs := [15513, 15517, 15521, 15525, 15529], params := [5] }
    9146 15517 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 9146 15513 15517 15521 15525 15529
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP bridge for `mref5-pos1(5191)`. -/
theorem recon_intermediateGoal_7887_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7887
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7887 7887 15494 15517
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_token7887_rel initSM initPM hSM hPM hInit)

private def layer10SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7887, 5195, 5196, 5198, 5199], outs := [5200], params := [64, 0, 64, 8] }
private def layer10PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [15494, 9155, 9157, 9161, 9163], outs := [9165], params := [64, 0, 32, 8] }
private def layer10PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [15517, 9156, 9158, 9162, 9164], outs := [9166], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer10_sm_node382 : sm.nodes[382]'(by native_decide) = layer10SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer10_pm_node825 : pm.nodes[825]'(by native_decide) = layer10PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer10_pm_node828 : pm.nodes[828]'(by native_decide) = layer10PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer10_sm_buddies : sm.replicaBuddies layer10SmMoe = [layer10SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer10_pm_buddies0 :
    pm.replicaBuddies layer10PmMoe0 = [layer10PmMoe0, layer10PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer10_pm_buddies1 :
    pm.replicaBuddies layer10PmMoe1 = [layer10PmMoe0, layer10PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful pure-distributed full-expert reconstruction of the layer-10 MoE boundary. -/
theorem recon_intermediateGoal_5200_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5200
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l10d_token7887_rel initSM initPM hSM hPM hInit
  have hrp := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5195 5195 9155 9156
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5195_distributed initSM initPM hSM hPM hInit)
  have hrm := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5196 5196 9157 9158
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5196_distributed initSM initPM hSM hPM hInit)
  have hW13 := hInit initGoal_5198 (by native_decide)
  have hW2 := hInit initGoal_5199 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_5198, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_5199, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 9161).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9161
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 9162).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9162
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 9163).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9163
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 9164).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9164
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 5198 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9161, denoteGraphDistributed pm initPM 9162] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5198 pm.numRanks _ rfl] at hv
    simp only [initGoal_5198, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5198 = initSM 5198 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5198
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 9161 = initPM 9161 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9161
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 9162 = initPM 9162 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9162
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 5199 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9163, denoteGraphDistributed pm initPM 9164] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5199 pm.numRanks _ rfl] at hv
    simp only [initGoal_5199, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5199 = initSM 5199 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5199
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 9163 = initPM 9163 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9163
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 9164 = initPM 9164 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9164
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5198] =
      denoteGraphDistributed sm initSM 5198 := by
    have hs : (denoteGraphDistributed sm initSM 5198).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5199] =
      denoteGraphDistributed sm initSM 5199 := by
    have hs : (denoteGraphDistributed sm initSM 5199).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hSMout : denoteGraphDistributed sm initSM 5200 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7887)
        (denoteGraphDistributed sm initSM 5195) (denoteGraphDistributed sm initSM 5196)
        [denoteGraphDistributed pm initPM 9161, denoteGraphDistributed pm initPM 9162]
        [denoteGraphDistributed pm initPM 9163, denoteGraphDistributed pm initPM 9164]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 382 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 382 layer10SmMoe 5200 hk
      (show sm.nodes[382]'hk = layer10SmMoe from layer10_sm_node382)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer10_sm_buddies]
    simp only [layer10SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7887 382 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5195 382 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5196 382 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5198 382 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5199 382 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 9165 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15494)
        (denoteGraphDistributed pm initPM 9155) (denoteGraphDistributed pm initPM 9157)
        [denoteGraphDistributed pm initPM 9161, denoteGraphDistributed pm initPM 9162]
        [denoteGraphDistributed pm initPM 9163, denoteGraphDistributed pm initPM 9164]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 825 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 825 layer10PmMoe0 9165 hk
      (show pm.nodes[825]'hk = layer10PmMoe0 from layer10_pm_node825)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer10_pm_buddies0]
    simp only [layer10PmMoe0, layer10PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15494 825 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9155 825 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9157 825 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9161 825 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9162 825 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9163 825 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9164 825 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 9166 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15517)
        (denoteGraphDistributed pm initPM 9156) (denoteGraphDistributed pm initPM 9158)
        [denoteGraphDistributed pm initPM 9161, denoteGraphDistributed pm initPM 9162]
        [denoteGraphDistributed pm initPM 9163, denoteGraphDistributed pm initPM 9164]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 828 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 828 layer10PmMoe1 9166 hk
      (show pm.nodes[828]'hk = layer10PmMoe1 from layer10_pm_node828)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer10_pm_buddies1]
    simp only [layer10PmMoe0, layer10PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15517 828 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9156 828 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9158 828 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9161 828 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9162 828 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9163 828 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9164 828 (by native_decide) (by native_decide)]
  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 15494) (denoteGraphDistributed pm initPM 15517)
    (denoteGraphDistributed pm initPM 9155) (denoteGraphDistributed pm initPM 9156)
    (denoteGraphDistributed pm initPM 9157) (denoteGraphDistributed pm initPM 9158)
    (denoteGraphDistributed pm initPM 9161) (denoteGraphDistributed pm initPM 9162)
    (denoteGraphDistributed pm initPM 9163) (denoteGraphDistributed pm initPM 9164)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 5200 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 9165, denoteGraphDistributed pm initPM 9166] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 9165).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15494)
      (rp := denoteGraphDistributed pm initPM 9155)
      (rm := denoteGraphDistributed pm initPM 9157)
      (w13s := [denoteGraphDistributed pm initPM 9161, denoteGraphDistributed pm initPM 9162])
      (w2s := [denoteGraphDistributed pm initPM 9163, denoteGraphDistributed pm initPM 9164])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 9166).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15517)
      (rp := denoteGraphDistributed pm initPM 9156)
      (rm := denoteGraphDistributed pm initPM 9158)
      (w13s := [denoteGraphDistributed pm initPM 9161, denoteGraphDistributed pm initPM 9162])
      (w2s := [denoteGraphDistributed pm initPM 9163, denoteGraphDistributed pm initPM 9164])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 5200).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5200 5200 9165 9166
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

#print axioms recon_intermediateGoal_7887_distributed
#print axioms recon_intermediateGoal_5200_distributed

/-! ### Layer-10 post-MoE residual tail, pure-distributed exact 2-TP. -/

private theorem l10dc_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o =
      elemwiseAdd (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  distributed_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

private theorem l10dc_float (g : GraphDecl) (init : Store) (k r i o : Nat)
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

private theorem l10d_carry7876_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7876)
      (denoteGraphDistributed pm initPM 15475) (denoteGraphDistributed pm initPM 15483)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5189 5189 9141 9142
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5189_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 367
    { rank := 0, op := "OpName.FW_multiref", ins := [5189], outs := [7872, 7876], params := [2] }
    5189 7876 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5189 7872 7876 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 795
    { rank := 0, op := "OpName.FW_multiref", ins := [9141], outs := [15471, 15475], params := [2] }
    9141 15475 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 9141 15471 15475 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 796
    { rank := 1, op := "OpName.FW_multiref", ins := [9142], outs := [15479, 15483], params := [2] }
    9142 15483 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 9142 15479 15483 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, ← r0, ← r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP bridge for `mref2-second(5189)`. -/
theorem recon_intermediateGoal_7876_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7876
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7876 7876 15475 15483
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_carry7876_rel initSM initPM hSM hPM hInit)

private theorem l10d_add5220_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5220)
      (denoteGraphDistributed pm initPM 9243) (denoteGraphDistributed pm initPM 9244)
      [4096, 1024] [2048, 1024] := by
  have ha := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5200 5200 9165 9166
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5200_distributed initSM initPM hSM hPM hInit)
  have hb := l10d_mul5219_rel initSM initPM hSM hPM hInit
  have rs := l10dc_add sm initSM 389 0 5200 5219 5220
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10dc_add pm initPM 839 0 9165 9239 9243
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10dc_add pm initPM 840 1 9166 9240 9244
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of post-MoE residual add `5200 + 5219`. -/
theorem recon_intermediateGoal_5220_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5220
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5220 5220 9243 9244
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_add5220_rel initSM initPM hSM hPM hInit)

private theorem l10d_float5221_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5221)
      (denoteGraphDistributed pm initPM 9249) (denoteGraphDistributed pm initPM 9250)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_add5220_rel initSM initPM hSM hPM hInit
  have rs := l10dc_float sm initSM 390 0 5220 5221
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10dc_float pm initPM 841 0 9243 9249
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10dc_float pm initPM 842 1 9244 9250
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `FW_float(5220)`. -/
theorem recon_intermediateGoal_5221_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5221
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5221 5221 9249 9250
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_float5221_rel initSM initPM hSM hPM hInit)

private theorem l10d_add5222_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5222)
      (denoteGraphDistributed pm initPM 9253) (denoteGraphDistributed pm initPM 9254)
      [4096, 1024] [2048, 1024] := by
  have ha := l10d_carry7876_rel initSM initPM hSM hPM hInit
  have hb := l10d_float5221_rel initSM initPM hSM hPM hInit
  have rs := l10dc_add sm initSM 391 0 7876 5221 5222
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10dc_add pm initPM 843 0 15475 9249 9253
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10dc_add pm initPM 844 1 15483 9250 9254
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of cross-block residual add `7876 + 5221`. -/
theorem recon_intermediateGoal_5222_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5222
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5222 5222 9253 9254
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_add5222_rel initSM initPM hSM hPM hInit)

/-! ### Layer-10 next-block pre-attention RMS and Q/K/V, pure-distributed exact 2-TP. -/

private theorem l10dc_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l10dc_perhead (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l10d_rms5224_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5224)
      (denoteGraphDistributed pm initPM 9257) (denoteGraphDistributed pm initPM 9258)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_add5222_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 392
    { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907], params := [2] }
    5222 7903 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5222 7903 7907)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 845
    { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537], params := [2] }
    9253 15533 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 9253 15533 15537)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 846
    { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545], params := [2] }
    9254 15541 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 9254 15541 15545)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5223
    (by native_decide) 5223 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l10dc_rms sm initSM 393 0 7903 5223 5224
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10dc_rms pm initPM 847 0 15533 5223 9257
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10dc_rms pm initPM 848 1 15541 5223 9258
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15533).shape = [2048, 1024] := by
    rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15541).shape = [2048, 1024] := by
    rw [m1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ms, h.value, ← m0, ← m1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1, r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP reconstruction of next-block RMSNorm `5224`. -/
theorem recon_intermediateGoal_5224_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5224
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5224 5224 9257 9258
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_rms5224_rel initSM initPM hSM hPM hInit)

private theorem l10d_mref7912_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7912)
      (denoteGraphDistributed pm initPM 15550) (denoteGraphDistributed pm initPM 15563)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_rms5224_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 394
    { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
    5224 7912 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 5224 7912 7916 7920)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 849
    { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
    9257 15550 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 9257 15550 15554 15558)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 850
    { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
    9258 15563 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 9258 15563 15567 15571)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

private theorem l10d_mref7916_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7916)
      (denoteGraphDistributed pm initPM 15554) (denoteGraphDistributed pm initPM 15567)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_rms5224_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 394
    { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
    5224 7916 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 5224 7912 7916 7920 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 849
    { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
    9257 15554 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 9257 15550 15554 15558 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 850
    { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
    9258 15567 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 9258 15563 15567 15571 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

private theorem l10d_mref7920_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7920)
      (denoteGraphDistributed pm initPM 15558) (denoteGraphDistributed pm initPM 15571)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_rms5224_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 394
    { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }
    5224 7920 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 5224 7912 7916 7920 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 849
    { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }
    9257 15558 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 9257 15550 15554 15558 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 850
    { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }
    9258 15571 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 9258 15563 15567 15571 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

private theorem l10d_q5226_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5226)
      (denoteGraphDistributed pm initPM 9259) (denoteGraphDistributed pm initPM 9260)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l10d_mref7912_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5225
    (by native_decide) 5225 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5225
    (by native_decide) 5225 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5225).shape = [16, 64, 1024] := by rw [← hw]; exact hws
  have rs := l10dc_perhead sm initSM 395 0 7912 5225 5226
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10dc_perhead pm initPM 851 0 15550 5225 9259
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10dc_perhead pm initPM 854 1 15563 5225 9260
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 h.full_shape hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 h.shard0_shape hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 h.shard1_shape hpw

/-- Pure-distributed exact 2-TP Q projection `5226`. -/
theorem recon_intermediateGoal_5226_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5226
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5226 5226 9259 9260
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l10d_q5226_rel initSM initPM hSM hPM hInit)

private theorem l10d_k5228_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5228)
      (denoteGraphDistributed pm initPM 9271) (denoteGraphDistributed pm initPM 9272)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l10d_mref7916_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5227
    (by native_decide) 5227 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5227
    (by native_decide) 5227 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5227).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l10dc_perhead sm initSM 396 0 7916 5227 5228
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10dc_perhead pm initPM 852 0 15554 5227 9271
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10dc_perhead pm initPM 855 1 15567 5227 9272
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 h.full_shape hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard0_shape hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard1_shape hpw

/-- Pure-distributed exact 2-TP K projection `5228`. -/
theorem recon_intermediateGoal_5228_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5228
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5228 5228 9271 9272
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l10d_k5228_rel initSM initPM hSM hPM hInit)

private theorem l10d_v5230_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5230)
      (denoteGraphDistributed pm initPM 9281) (denoteGraphDistributed pm initPM 9282)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l10d_mref7920_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5229
    (by native_decide) 5229 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5229
    (by native_decide) 5229 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5229).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l10dc_perhead sm initSM 397 0 7920 5229 5230
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10dc_perhead pm initPM 853 0 15558 5229 9281
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10dc_perhead pm initPM 856 1 15571 5229 9282
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 h.full_shape hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard0_shape hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard1_shape hpw

/-- Pure-distributed exact 2-TP V projection `5230`. -/
theorem recon_intermediateGoal_5230_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5230
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5230 5230 9281 9282
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l10d_v5230_rel initSM initPM hSM hPM hInit)

#print axioms recon_intermediateGoal_5222_distributed
#print axioms recon_intermediateGoal_5230_distributed

end TrainVerify.Denote.GeneratedPatterns
