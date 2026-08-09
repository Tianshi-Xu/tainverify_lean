/- Canonical Goal 1, layer 16: residual bypass and faithful scalar-gate branch. -/
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

private def l16ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5944],
    outs := [8742, 8746], params := [2] }
private def l16ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10738],
    outs := [16294, 16298], params := [2] }
private def l16ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10739],
    outs := [16302, 16306], params := [2] }

private theorem l16ZMrg_red_sm8746 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8746 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5944 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 722 l16ZMrgSmResidual
    5944 8746 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5944 8742 8746
    (by decide)

private theorem l16ZMrg_red_pm16298 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16298 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10738 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1583 l16ZMrgPmResidual0
    10738 16298 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 10738 16294 16298
    (by decide)

private theorem l16ZMrg_red_pm16306 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16306 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10739 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1584 l16ZMrgPmResidual1
    10739 16306 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 10739 16302 16306
    (by decide)

/-- The L16 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L16 attention residual transports to the exact residual
relation consumed by `l16_zigzag_moe_output_from_branch_inputs`. -/
theorem l16_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8746)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16298)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16306)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l16ZMrg_red_sm8746 initSM, l16ZMrg_red_pm16298 initPM,
    l16ZMrg_red_pm16306 initPM]
  exact hAttention

private def l16ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5946],
    outs := [8753, 8757, 8761, 8765, 8769], params := [5] }
private def l16ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10742],
    outs := [15412, 14628, 14638, 14652, 14664], params := [5] }
private def l16ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10743],
    outs := [15414, 14629, 14639, 14653, 14665], params := [5] }
private def l16ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8761], outs := [5956],
    params := [4096, 1024] }
private def l16ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14638], outs := [10764],
    params := [2048, 1024] }
private def l16ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14639], outs := [10765],
    params := [2048, 1024] }
private def l16ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5956, 5957],
    outs := [5958] }
private def l16ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10764, 5957],
    outs := [10768] }
private def l16ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10765, 5957],
    outs := [10769] }
private def l16ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5958], outs := [5959],
    params := [4096, 1] }
private def l16ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10768], outs := [10770],
    params := [2048, 1] }
private def l16ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10769], outs := [10771],
    params := [2048, 1] }
private def l16ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5959], outs := [5960] }
private def l16ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10770], outs := [10772] }
private def l16ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10771], outs := [10773] }

private theorem l16ZMrg_red_sm8761 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8761 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5946 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 724 l16ZMrgSmRef
    5946 8761 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5946 [8753, 8757, 8761, 8765, 8769]
    5 rfl 8761 (by decide)

private theorem l16ZMrg_red_pm14638 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14638 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10742 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1587 l16ZMrgPmRef0
    10742 14638 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10742
    [15412, 14628, 14638, 14652, 14664] 5 rfl 14638 (by decide)

private theorem l16ZMrg_red_pm14639 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14639 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10743 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1588 l16ZMrgPmRef1
    10743 14639 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10743
    [15414, 14629, 14639, 14653, 14665] 5 rfl 14639 (by decide)

private theorem l16ZMrg_red_sm5956 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5956 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8761) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 726 l16ZMrgSmReshape
    8761 5956 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8761 5956 [4096, 1024]

private theorem l16ZMrg_red_pm10764 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10764 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14638) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1589 l16ZMrgPmReshape0
    14638 10764 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14638 10764 [2048, 1024]

private theorem l16ZMrg_red_pm10765 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10765 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14639) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1593 l16ZMrgPmReshape1
    14639 10765 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14639 10765 [2048, 1024]

private theorem l16ZMrg_red_sm5958 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5958 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5956)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5957) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 730 l16ZMrgSmLinear
    5956 5957 5958 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5956 5957 5958

private theorem l16ZMrg_red_pm10768 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10768 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10764)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5957) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1596 l16ZMrgPmLinear0
    10764 5957 10768 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10764 5957 10768

private theorem l16ZMrg_red_pm10769 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10769 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10765)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5957) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1601 l16ZMrgPmLinear1
    10765 5957 10769 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10765 5957 10769

private theorem l16ZMrg_red_sm5959 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5959 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5958) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 734 l16ZMrgSmView
    5958 5959 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5958 5959

private theorem l16ZMrg_red_pm10770 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10770 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10768) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1604 l16ZMrgPmView0
    10768 10770 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 10768 10770

private theorem l16ZMrg_red_pm10771 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10771 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10769) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1609 l16ZMrgPmView1
    10769 10771 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 10769 10771

private theorem l16ZMrg_red_sm5960 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5960 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5959) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 738 l16ZMrgSmSigmoid
    5959 5960 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5959 5960

private theorem l16ZMrg_red_pm10772 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10772 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10770) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1612 l16ZMrgPmSigmoid0
    10770 10772 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 10770 10772

private theorem l16ZMrg_red_pm10773 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10773 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10771) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1616 l16ZMrgPmSigmoid1
    10771 10773 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 10771 10773

private theorem l16ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5957 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5957 ∉ n.outs) := by
  native_decide

private theorem l16ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5957 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5957 := by
  have hi := (hInit initGoal_5957 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5957 pm_goal_1.numRanks _ rfl,
    show initGoal_5957.tps = [{rank := 0, tid := 5957}] from rfl,
    show initGoal_5957.ts = 5957 from rfl,
    show initGoal_5957.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5957
      (by native_decide) l16ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5957
      (by native_decide) l16ZMrg_weight_not_written.2]
  exact hi

private theorem l16ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5957).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5957 = initPM 5957 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5957
      (by native_decide) l16ZMrg_weight_not_written.2
  rw [e]
  exact hPM 5957 [1, 1024] (by native_decide)

/-- The canonical L16 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l16_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10772)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10773)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8761)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14638)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14639)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMrg_red_sm8761 initSM, l16ZMrg_red_pm14638 initPM,
      l16ZMrg_red_pm14639 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5956)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10764)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10765)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMrg_red_sm5956 initSM, l16ZMrg_red_pm10764 initPM,
      l16ZMrg_red_pm10765 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l16ZMrg_weight_eq initSM initPM hInit
  have hwShape := l16ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5958)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10768)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10769)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l16ZMrg_red_sm5958 initSM, l16ZMrg_red_pm10768 initPM,
      l16ZMrg_red_pm10769 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5959)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10770)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10771)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l16ZMrg_red_sm5959 initSM, l16ZMrg_red_pm10770 initPM,
      l16ZMrg_red_pm10771 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5959)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10770)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10771)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l16ZMrg_red_sm5960 initSM, l16ZMrg_red_pm10772 initPM,
    l16ZMrg_red_pm10773 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
