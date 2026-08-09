/- Canonical Goal 1, layer 12: residual bypass and faithful scalar-gate branch. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLayoutRel
import denote.yoco_goals.ZigzagLinearRel
import denote.yoco_goals.ZigzagPointwiseRel
import denote.yoco_goals.ZigzagElemwiseRel
import denote.MultirefGeneral

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def l12ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5728],
    outs := [8586, 8590], params := [2] }
private def l12ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10122],
    outs := [16166, 16170], params := [2] }
private def l12ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10123],
    outs := [16174, 16178], params := [2] }

private theorem l12ZMrg_red_sm8590 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8590 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5728 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 582 l12ZMrgSmResidual
    5728 8590 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5728 8586 8590
    (by decide)

private theorem l12ZMrg_red_pm16170 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16170 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10122 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1279 l12ZMrgPmResidual0
    10122 16170 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 10122 16166 16170
    (by decide)

private theorem l12ZMrg_red_pm16178 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16178 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10123 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1280 l12ZMrgPmResidual1
    10123 16178 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 10123 16174 16178
    (by decide)

/-- The L21 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L12 attention residual transports to the exact residual
relation consumed by `goal1_l12_block3_moe_output_from_branch_inputs`. -/
theorem goal1_l12_block3_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8590)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16170)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16178)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l12ZMrg_red_sm8590 initSM, l12ZMrg_red_pm16170 initPM,
    l12ZMrg_red_pm16178 initPM]
  exact hAttention

private def l12ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5730],
    outs := [8597, 8601, 8605, 8609, 8613], params := [5] }
private def l12ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10126],
    outs := [15396, 14164, 14174, 14188, 14200], params := [5] }
private def l12ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10127],
    outs := [15398, 14165, 14175, 14189, 14201], params := [5] }
private def l12ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8605], outs := [5740],
    params := [4096, 1024] }
private def l12ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14174], outs := [10148],
    params := [2048, 1024] }
private def l12ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14175], outs := [10149],
    params := [2048, 1024] }
private def l12ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5740, 5741],
    outs := [5742] }
private def l12ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10148, 5741],
    outs := [10152] }
private def l12ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10149, 5741],
    outs := [10153] }
private def l12ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5742], outs := [5743],
    params := [4096, 1] }
private def l12ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10152], outs := [10154],
    params := [2048, 1] }
private def l12ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10153], outs := [10155],
    params := [2048, 1] }
private def l12ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5743], outs := [5744] }
private def l12ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10154], outs := [10156] }
private def l12ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10155], outs := [10157] }

private theorem l12ZMrg_red_sm8605 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8605 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5730 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 584 l12ZMrgSmRef
    5730 8605 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5730 [8597, 8601, 8605, 8609, 8613]
    5 rfl 8605 (by decide)

private theorem l12ZMrg_red_pm14174 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14174 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10126 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1283 l12ZMrgPmRef0
    10126 14174 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10126
    [15396, 14164, 14174, 14188, 14200] 5 rfl 14174 (by decide)

private theorem l12ZMrg_red_pm14175 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14175 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10127 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1284 l12ZMrgPmRef1
    10127 14175 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10127
    [15398, 14165, 14175, 14189, 14201] 5 rfl 14175 (by decide)

private theorem l12ZMrg_red_sm5740 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5740 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8605) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 586 l12ZMrgSmReshape
    8605 5740 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8605 5740 [4096, 1024]

private theorem l12ZMrg_red_pm10148 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10148 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14174) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1285 l12ZMrgPmReshape0
    14174 10148 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14174 10148 [2048, 1024]

private theorem l12ZMrg_red_pm10149 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10149 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14175) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1289 l12ZMrgPmReshape1
    14175 10149 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14175 10149 [2048, 1024]

private theorem l12ZMrg_red_sm5742 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5742 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5740)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5741) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 590 l12ZMrgSmLinear
    5740 5741 5742 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5740 5741 5742

private theorem l12ZMrg_red_pm10152 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10152 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10148)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5741) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1292 l12ZMrgPmLinear0
    10148 5741 10152 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10148 5741 10152

private theorem l12ZMrg_red_pm10153 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10153 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10149)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5741) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1297 l12ZMrgPmLinear1
    10149 5741 10153 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10149 5741 10153

private theorem l12ZMrg_red_sm5743 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5743 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5742) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 594 l12ZMrgSmView
    5742 5743 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5742 5743

private theorem l12ZMrg_red_pm10154 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10154 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10152) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1300 l12ZMrgPmView0
    10152 10154 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 10152 10154

private theorem l12ZMrg_red_pm10155 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10155 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10153) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1305 l12ZMrgPmView1
    10153 10155 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 10153 10155

private theorem l12ZMrg_red_sm5744 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5744 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5743) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 598 l12ZMrgSmSigmoid
    5743 5744 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5743 5744

private theorem l12ZMrg_red_pm10156 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10156 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10154) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1308 l12ZMrgPmSigmoid0
    10154 10156 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 10154 10156

private theorem l12ZMrg_red_pm10157 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10157 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10155) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1312 l12ZMrgPmSigmoid1
    10155 10157 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 10155 10157

private theorem l12ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5741 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5741 ∉ n.outs) := by
  native_decide

private theorem l12ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5741 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5741 := by
  have hi := (hInit initGoal_5741 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5741 pm_goal_1.numRanks _ rfl,
    show initGoal_5741.tps = [{rank := 0, tid := 5741}] from rfl,
    show initGoal_5741.ts = 5741 from rfl,
    show initGoal_5741.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5741
      (by native_decide) l12ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5741
      (by native_decide) l12ZMrg_weight_not_written.2]
  exact hi

private theorem l12ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5741).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5741 = initPM 5741 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5741
      (by native_decide) l12ZMrg_weight_not_written.2
  rw [e]
  exact hPM 5741 [1, 1024] (by native_decide)

/-- The canonical L21 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem goal1_l12_block3_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5730)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10126)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10127)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5744)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10156)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10157)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8605)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14174)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14175)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMrg_red_sm8605 initSM, l12ZMrg_red_pm14174 initPM,
      l12ZMrg_red_pm14175 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5740)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10148)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10149)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMrg_red_sm5740 initSM, l12ZMrg_red_pm10148 initPM,
      l12ZMrg_red_pm10149 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l12ZMrg_weight_eq initSM initPM hInit
  have hwShape := l12ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10152)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10153)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l12ZMrg_red_sm5742 initSM, l12ZMrg_red_pm10152 initPM,
      l12ZMrg_red_pm10153 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10154)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l12ZMrg_red_sm5743 initSM, l12ZMrg_red_pm10154 initPM,
      l12ZMrg_red_pm10155 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10154)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l12ZMrg_red_sm5744 initSM, l12ZMrg_red_pm10156 initPM,
    l12ZMrg_red_pm10157 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
