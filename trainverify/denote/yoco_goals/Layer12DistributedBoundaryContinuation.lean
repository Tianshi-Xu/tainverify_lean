import denote.yoco_goals.Layer12DistributedContinuation

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### Layer-12 router product/gating continuation, pure-distributed exact 2-TP. -/

private theorem l12b_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l12b_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l12b_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l12b_sigmoid (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_sigmoid", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_sigmoid (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o fw_sigmoid hk hn (by simp)
    (fun st => applyNode_fw_sigmoid_out g st r i o []) hdn hdw hpn hpw

private theorem l12b_swiglu (g : GraphDecl) (init : Store) (k r x y o : Nat)
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

private theorem l12b_mul (g : GraphDecl) (init : Store) (k r x y o : Nat)
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

private theorem l12b_5299_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5299)
      (denoteGraphDistributed pm initPM 9517) (denoteGraphDistributed pm initPM 9518)
      [4096, 1024] [2048, 1024] :=
  Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5299 5299 9517 9518
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5299_distributed initSM initPM hSM hPM hInit)

private theorem l12b_token7991_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7991)
      (denoteGraphDistributed pm initPM 15702) (denoteGraphDistributed pm initPM 15725)
      [4096, 1024] [2048, 1024] := by
  have h := l12b_5299_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 447
    { rank := 0, op := "OpName.FW_multiref", ins := [5299],
      outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
    5299 7991 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 5299 7987 7991 7995 7999 8003
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 955
    { rank := 0, op := "OpName.FW_multiref", ins := [9517],
      outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
    9517 15702 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 9517 15698 15702 15706 15710 15714
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 956
    { rank := 1, op := "OpName.FW_multiref", ins := [9518],
      outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
    9518 15725 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 9518 15721 15725 15729 15733 15737
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-12 MoE token input
    (`mref5` position 1 of `5299`). -/
theorem recon_intermediateGoal_7991_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7991
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7991 7991 15702 15725
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12b_token7991_rel initSM initPM hSM hPM hInit)

/-! ### L12 router expert side branches — `mref5-pos{2,3,4}(5299)` reshape/mixlin/view. -/

private theorem l12b_reshape5309_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5309)
      (denoteGraphDistributed pm initPM 9539) (denoteGraphDistributed pm initPM 9540)
      [4096, 1024] [2048, 1024] := by
  have h := l12b_5299_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 447
    { rank := 0, op := "OpName.FW_multiref", ins := [5299],
      outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
    5299 7995 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out sm st 0 5299 7987 7991 7995 7999 8003
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 955
    { rank := 0, op := "OpName.FW_multiref", ins := [9517],
      outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
    9517 15706 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 0 9517 15698 15702 15706 15710 15714
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 956
    { rank := 1, op := "OpName.FW_multiref", ins := [9518],
      outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
    9518 15729 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 1 9518 15721 15725 15729 15733 15737
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l12b_reshape sm initSM 449 0 7995 5309 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_reshape pm initPM 958 0 15706 9539 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_reshape pm initPM 962 1 15729 9540 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5309 = denoteGraphDistributed sm initSM 7995 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9539 = denoteGraphDistributed pm initPM 15706 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9540 = denoteGraphDistributed pm initPM 15729 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos2(5299)` reshape. -/
theorem recon_intermediateGoal_5309_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5309
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5309 5309 9539 9540
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12b_reshape5309_rel initSM initPM hSM hPM hInit)

private theorem l12b_reshape5314_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5314)
      (denoteGraphDistributed pm initPM 9553) (denoteGraphDistributed pm initPM 9554)
      [4096, 1024] [2048, 1024] := by
  have h := l12b_5299_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 447
    { rank := 0, op := "OpName.FW_multiref", ins := [5299],
      outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
    5299 7999 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out sm st 0 5299 7987 7991 7995 7999 8003
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 955
    { rank := 0, op := "OpName.FW_multiref", ins := [9517],
      outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
    9517 15710 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 0 9517 15698 15702 15706 15710 15714
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 956
    { rank := 1, op := "OpName.FW_multiref", ins := [9518],
      outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
    9518 15733 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 1 9518 15721 15725 15729 15733 15737
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l12b_reshape sm initSM 450 0 7999 5314 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_reshape pm initPM 959 0 15710 9553 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_reshape pm initPM 963 1 15733 9554 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5314 = denoteGraphDistributed sm initSM 7999 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9553 = denoteGraphDistributed pm initPM 15710 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9554 = denoteGraphDistributed pm initPM 15733 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos3(5299)` reshape. -/
theorem recon_intermediateGoal_5314_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5314
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5314 5314 9553 9554
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12b_reshape5314_rel initSM initPM hSM hPM hInit)

private theorem l12b_reshape5318_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5318)
      (denoteGraphDistributed pm initPM 9571) (denoteGraphDistributed pm initPM 9572)
      [4096, 1024] [2048, 1024] := by
  have h := l12b_5299_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 447
    { rank := 0, op := "OpName.FW_multiref", ins := [5299],
      outs := [7987, 7991, 7995, 7999, 8003], params := [5] }
    5299 8003 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out sm st 0 5299 7987 7991 7995 7999 8003
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 955
    { rank := 0, op := "OpName.FW_multiref", ins := [9517],
      outs := [15698, 15702, 15706, 15710, 15714], params := [5] }
    9517 15714 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 0 9517 15698 15702 15706 15710 15714
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 956
    { rank := 1, op := "OpName.FW_multiref", ins := [9518],
      outs := [15721, 15725, 15729, 15733, 15737], params := [5] }
    9518 15737 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 1 9518 15721 15725 15729 15733 15737
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l12b_reshape sm initSM 451 0 8003 5318 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_reshape pm initPM 960 0 15714 9571 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_reshape pm initPM 964 1 15737 9572 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5318 = denoteGraphDistributed sm initSM 8003 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 9571 = denoteGraphDistributed pm initPM 15714 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 9572 = denoteGraphDistributed pm initPM 15737 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of `mref5-pos4(5299)` reshape. -/
theorem recon_intermediateGoal_5318_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5318
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5318 5318 9571 9572
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12b_reshape5318_rel initSM initPM hSM hPM hInit)

private theorem l12b_linear5311_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5311)
      (denoteGraphDistributed pm initPM 9543) (denoteGraphDistributed pm initPM 9544)
      [4096, 1] [2048, 1] := by
  have h := l12b_reshape5309_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5310
    (by native_decide) 5310 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5310
    (by native_decide) 5310 [1, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5310).shape = [1, 1024] := by rw [← hw]; exact hws
  have rs := l12b_linear sm initSM 453 0 5309 5310 5311
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12b_linear pm initPM 966 0 9539 5310 9543
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12b_linear pm initPM 970 1 9540 5310 9544
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5309, 5310)`. -/
theorem recon_intermediateGoal_5311_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5311
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5311 5311 9543 9544
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l12b_linear5311_rel initSM initPM hSM hPM hInit)

private theorem l12b_linear5316_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5316)
      (denoteGraphDistributed pm initPM 9557) (denoteGraphDistributed pm initPM 9558)
      [4096, 512] [2048, 512] := by
  have h := l12b_reshape5314_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5315
    (by native_decide) 5315 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5315
    (by native_decide) 5315 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5315).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l12b_linear sm initSM 454 0 5314 5315 5316
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12b_linear pm initPM 967 0 9553 5315 9557
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12b_linear pm initPM 971 1 9554 5315 9558
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5314, 5315)`. -/
theorem recon_intermediateGoal_5316_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5316
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5316 5316 9557 9558
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l12b_linear5316_rel initSM initPM hSM hPM hInit)

private theorem l12b_linear5320_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5320)
      (denoteGraphDistributed pm initPM 9575) (denoteGraphDistributed pm initPM 9576)
      [4096, 512] [2048, 512] := by
  have h := l12b_reshape5318_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5319
    (by native_decide) 5319 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5319
    (by native_decide) 5319 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5319).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l12b_linear sm initSM 455 0 5318 5319 5320
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12b_linear pm initPM 968 0 9571 5319 9575
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12b_linear pm initPM 972 1 9572 5319 9576
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert linear `fw_linear(5318, 5319)`. -/
theorem recon_intermediateGoal_5320_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5320
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5320 5320 9575 9576
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l12b_linear5320_rel initSM initPM hSM hPM hInit)

private theorem l12b_view5312_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5312)
      (denoteGraphDistributed pm initPM 9549) (denoteGraphDistributed pm initPM 9550)
      [4096, 1] [2048, 1] := by
  have h := l12b_linear5311_rel initSM initPM hSM hPM hInit
  have rs := l12b_view sm initSM 457 0 5311 5312 4096 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_view pm initPM 974 0 9543 9549 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_view pm initPM 978 1 9544 9550 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5312 = denoteGraphDistributed sm initSM 5311 := by
    rw [rs, fw_view_id_shape [4096, 1] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9549 = denoteGraphDistributed pm initPM 9543 := by
    rw [r0, fw_view_id_shape [2048, 1] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9550 = denoteGraphDistributed pm initPM 9544 := by
    rw [r1, fw_view_id_shape [2048, 1] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,1] (5311)`. -/
theorem recon_intermediateGoal_5312_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5312
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5312 5312 9549 9550
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l12b_view5312_rel initSM initPM hSM hPM hInit)

private theorem l12b_view5317_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5317)
      (denoteGraphDistributed pm initPM 9567) (denoteGraphDistributed pm initPM 9568)
      [4096, 512] [2048, 512] := by
  have h := l12b_linear5316_rel initSM initPM hSM hPM hInit
  have rs := l12b_view sm initSM 458 0 5316 5317 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_view pm initPM 975 0 9557 9567 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_view pm initPM 979 1 9558 9568 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5317 = denoteGraphDistributed sm initSM 5316 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9567 = denoteGraphDistributed pm initPM 9557 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9568 = denoteGraphDistributed pm initPM 9558 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,512] (5316)`. -/
theorem recon_intermediateGoal_5317_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5317
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5317 5317 9567 9568
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l12b_view5317_rel initSM initPM hSM hPM hInit)

private theorem l12b_view5321_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5321)
      (denoteGraphDistributed pm initPM 9585) (denoteGraphDistributed pm initPM 9586)
      [4096, 512] [2048, 512] := by
  have h := l12b_linear5320_rel initSM initPM hSM hPM hInit
  have rs := l12b_view sm initSM 459 0 5320 5321 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_view pm initPM 976 0 9575 9585 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_view pm initPM 980 1 9576 9586 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5321 = denoteGraphDistributed sm initSM 5320 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9585 = denoteGraphDistributed pm initPM 9575 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9586 = denoteGraphDistributed pm initPM 9576 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `fw_view [4096,512] (5320)`. -/
theorem recon_intermediateGoal_5321_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5321
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5321 5321 9585 9586
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l12b_view5321_rel initSM initPM hSM hPM hInit)

/-! ### Layer-12 gate/expert postprocessing, pure-distributed exact 2-TP. -/

private theorem l12b_sigmoid5313_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5313)
      (denoteGraphDistributed pm initPM 9551) (denoteGraphDistributed pm initPM 9552)
      [4096, 1] [2048, 1] := by
  have h := l12b_view5312_rel initSM initPM hSM hPM hInit
  have rs := l12b_sigmoid sm initSM 461 0 5312 5313
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_sigmoid pm initPM 982 0 9549 9551
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_sigmoid pm initPM 985 1 9550 9552
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_sigmoid_allGather0_commute_2 _ _ 2048 1
      (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs, fw_sigmoid_shape]; exact h.full_shape
  · rw [r0, fw_sigmoid_shape]; exact h.shard0_shape
  · rw [r1, fw_sigmoid_shape]; exact h.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of gate sigmoid `fw_sigmoid(5312)`. -/
theorem recon_intermediateGoal_5313_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5313
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5313 5313 9551 9552
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l12b_sigmoid5313_rel initSM initPM hSM hPM hInit)

private theorem l12b_swiglu5322_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5322)
      (denoteGraphDistributed pm initPM 9589) (denoteGraphDistributed pm initPM 9590)
      [4096, 512] [2048, 512] := by
  have hx := l12b_view5317_rel initSM initPM hSM hPM hInit
  have hy := l12b_view5321_rel initSM initPM hSM hPM hInit
  have rs := l12b_swiglu sm initSM 462 0 5317 5321 5322
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12b_swiglu pm initPM 983 0 9567 9585 9589
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12b_swiglu pm initPM 986 1 9568 9586 9590
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs, fw_swiglu_shape]; exact hy.full_shape
  · rw [r0, fw_swiglu_shape]; exact hy.shard0_shape
  · rw [r1, fw_swiglu_shape]; exact hy.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of expert `fw_swiglu(5317, 5321)`. -/
theorem recon_intermediateGoal_5322_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5322
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5322 5322 9589 9590
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l12b_swiglu5322_rel initSM initPM hSM hPM hInit)

private theorem l12b_reshape5323_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5323)
      (denoteGraphDistributed pm initPM 9591) (denoteGraphDistributed pm initPM 9592)
      [4096, 512] [2048, 512] := by
  have h := l12b_swiglu5322_rel initSM initPM hSM hPM hInit
  have rs := l12b_reshape sm initSM 463 0 5322 5323 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_reshape pm initPM 987 0 9589 9591 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_reshape pm initPM 988 1 9590 9592 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5323 = denoteGraphDistributed sm initSM 5322 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9591 = denoteGraphDistributed pm initPM 9589 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9592 = denoteGraphDistributed pm initPM 9590 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert reshape `5323`. -/
theorem recon_intermediateGoal_5323_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5323
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5323 5323 9591 9592
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l12b_reshape5323_rel initSM initPM hSM hPM hInit)

private theorem l12b_linear5325_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5325)
      (denoteGraphDistributed pm initPM 9597) (denoteGraphDistributed pm initPM 9598)
      [4096, 1024] [2048, 1024] := by
  have h := l12b_reshape5323_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5324
    (by native_decide) 5324 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5324
    (by native_decide) 5324 [1024, 512] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5324).shape = [1024, 512] := by
    rw [← hw]; exact hws
  have rs := l12b_linear sm initSM 464 0 5323 5324 5325
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12b_linear pm initPM 989 0 9591 5324 9597
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12b_linear pm initPM 990 1 9592 5324 9598
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 512 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of expert output linear `5325`. -/
theorem recon_intermediateGoal_5325_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5325
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5325 5325 9597 9598
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12b_linear5325_rel initSM initPM hSM hPM hInit)

private theorem l12b_view5326_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5326)
      (denoteGraphDistributed pm initPM 9607) (denoteGraphDistributed pm initPM 9608)
      [4096, 1024] [2048, 1024] := by
  have h := l12b_linear5325_rel initSM initPM hSM hPM hInit
  have rs := l12b_view sm initSM 465 0 5325 5326 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l12b_view pm initPM 991 0 9597 9607 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l12b_view pm initPM 992 1 9598 9608 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5326 = denoteGraphDistributed sm initSM 5325 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9607 = denoteGraphDistributed pm initPM 9597 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9608 = denoteGraphDistributed pm initPM 9598 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of expert identity view `5326`. -/
theorem recon_intermediateGoal_5326_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5326
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5326 5326 9607 9608
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12b_view5326_rel initSM initPM hSM hPM hInit)

private theorem l12b_mul_shape (x y : Tensor) (s h : Nat) (hh : 1 ≤ h)
    (hx : x.shape = [s, 1]) (hy : y.shape = [s, h]) :
    (elemwiseMul x y).shape = [s, h] := by
  simp [elemwiseMul, Tensor.mkShape, outShape2, hx, hy, Nat.max_eq_right hh]

private theorem l12b_mul5327_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5327)
      (denoteGraphDistributed pm initPM 9611) (denoteGraphDistributed pm initPM 9612)
      [4096, 1024] [2048, 1024] := by
  have hx := l12b_sigmoid5313_rel initSM initPM hSM hPM hInit
  have hy := l12b_view5326_rel initSM initPM hSM hPM hInit
  have rs := l12b_mul sm initSM 466 0 5313 5326 5327
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l12b_mul pm initPM 993 0 9551 9607 9611
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l12b_mul pm initPM 994 1 9552 9608 9612
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024
        (by omega) (by omega) (by decide) (by decide) (by decide)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs]; exact l12b_mul_shape _ _ 4096 1024 (by omega) hx.full_shape hy.full_shape
  · rw [r0]; exact l12b_mul_shape _ _ 2048 1024 (by omega) hx.shard0_shape hy.shard0_shape
  · rw [r1]; exact l12b_mul_shape _ _ 2048 1024 (by omega) hx.shard1_shape hy.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of gate/expert broadcast product `5327`. -/
theorem recon_intermediateGoal_5327_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5327
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5327 5327 9611 9612
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l12b_mul5327_rel initSM initPM hSM hPM hInit)

private def layer12SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7991, 5303, 5304, 5306, 5307], outs := [5308], params := [64, 0, 64, 8] }
private def layer12PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [15702, 9527, 9529, 9533, 9535], outs := [9537], params := [64, 0, 32, 8] }
private def layer12PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [15725, 9528, 9530, 9534, 9536], outs := [9538], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer12_sm_node460 : sm.nodes[460]'(by native_decide) = layer12SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_node981 : pm.nodes[981]'(by native_decide) = layer12PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_node984 : pm.nodes[984]'(by native_decide) = layer12PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_sm_buddies : sm.replicaBuddies layer12SmMoe = [layer12SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_buddies0 :
    pm.replicaBuddies layer12PmMoe0 = [layer12PmMoe0, layer12PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer12_pm_buddies1 :
    pm.replicaBuddies layer12PmMoe1 = [layer12PmMoe0, layer12PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful pure-distributed full-expert exact 2-TP reconstruction of the
    layer-12 MoE boundary. -/
theorem recon_intermediateGoal_5308_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5308
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l12b_token7991_rel initSM initPM hSM hPM hInit
  have hrp := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5303 5303 9527 9528
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5303_distributed initSM initPM hSM hPM hInit)
  have hrm := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5304 5304 9529 9530
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5304_distributed initSM initPM hSM hPM hInit)
  have hW13 := hInit initGoal_5306 (by native_decide)
  have hW2 := hInit initGoal_5307 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_5306, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_5307, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 9533).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9533
      layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 9534).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9534
      layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 9535).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9535
      layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 9536).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9536
      layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 5306 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9533, denoteGraphDistributed pm initPM 9534] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5306 pm.numRanks _ rfl] at hv
    simp only [initGoal_5306, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5306 = initSM 5306 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5306
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 9533 = initPM 9533 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9533
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 9534 = initPM 9534 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9534
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 5307 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9535, denoteGraphDistributed pm initPM 9536] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5307 pm.numRanks _ rfl] at hv
    simp only [initGoal_5307, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5307 = initSM 5307 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5307
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 9535 = initPM 9535 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9535
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 9536 = initPM 9536 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 9536
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5306] =
      denoteGraphDistributed sm initSM 5306 := by
    have hs : (denoteGraphDistributed sm initSM 5306).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5307] =
      denoteGraphDistributed sm initSM 5307 := by
    have hs : (denoteGraphDistributed sm initSM 5307).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hSMout : denoteGraphDistributed sm initSM 5308 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7991)
        (denoteGraphDistributed sm initSM 5303) (denoteGraphDistributed sm initSM 5304)
        [denoteGraphDistributed pm initPM 9533, denoteGraphDistributed pm initPM 9534]
        [denoteGraphDistributed pm initPM 9535, denoteGraphDistributed pm initPM 9536]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 460 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 460 layer12SmMoe 5308 hk
      (show sm.nodes[460]'hk = layer12SmMoe from layer12_sm_node460)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer12_sm_buddies]
    simp only [layer12SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7991 460 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5303 460 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5304 460 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5306 460 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5307 460 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 9537 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15702)
        (denoteGraphDistributed pm initPM 9527) (denoteGraphDistributed pm initPM 9529)
        [denoteGraphDistributed pm initPM 9533, denoteGraphDistributed pm initPM 9534]
        [denoteGraphDistributed pm initPM 9535, denoteGraphDistributed pm initPM 9536]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 981 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 981 layer12PmMoe0 9537 hk
      (show pm.nodes[981]'hk = layer12PmMoe0 from layer12_pm_node981)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer12_pm_buddies0]
    simp only [layer12PmMoe0, layer12PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15702 981 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9527 981 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9529 981 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9533 981 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9534 981 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9535 981 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9536 981 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 9538 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15725)
        (denoteGraphDistributed pm initPM 9528) (denoteGraphDistributed pm initPM 9530)
        [denoteGraphDistributed pm initPM 9533, denoteGraphDistributed pm initPM 9534]
        [denoteGraphDistributed pm initPM 9535, denoteGraphDistributed pm initPM 9536]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 984 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 984 layer12PmMoe1 9538 hk
      (show pm.nodes[984]'hk = layer12PmMoe1 from layer12_pm_node984)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer12_pm_buddies1]
    simp only [layer12PmMoe0, layer12PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15725 984 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9528 984 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9530 984 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9533 984 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9534 984 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9535 984 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 9536 984 (by native_decide) (by native_decide)]
  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 15702) (denoteGraphDistributed pm initPM 15725)
    (denoteGraphDistributed pm initPM 9527) (denoteGraphDistributed pm initPM 9528)
    (denoteGraphDistributed pm initPM 9529) (denoteGraphDistributed pm initPM 9530)
    (denoteGraphDistributed pm initPM 9533) (denoteGraphDistributed pm initPM 9534)
    (denoteGraphDistributed pm initPM 9535) (denoteGraphDistributed pm initPM 9536)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 5308 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 9537, denoteGraphDistributed pm initPM 9538] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 9537).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15702) (rp := denoteGraphDistributed pm initPM 9527)
      (rm := denoteGraphDistributed pm initPM 9529)
      (w13s := [denoteGraphDistributed pm initPM 9533, denoteGraphDistributed pm initPM 9534])
      (w2s := [denoteGraphDistributed pm initPM 9535, denoteGraphDistributed pm initPM 9536])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 9538).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15725) (rp := denoteGraphDistributed pm initPM 9528)
      (rm := denoteGraphDistributed pm initPM 9530)
      (w13s := [denoteGraphDistributed pm initPM 9533, denoteGraphDistributed pm initPM 9534])
      (w2s := [denoteGraphDistributed pm initPM 9535, denoteGraphDistributed pm initPM 9536])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 5308).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5308 5308 9537 9538
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

end TrainVerify.Denote.GeneratedPatterns
