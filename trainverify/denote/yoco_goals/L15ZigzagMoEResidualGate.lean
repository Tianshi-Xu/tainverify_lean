/- Canonical Goal 1, layer 15: residual bypass and faithful scalar-gate branch. -/
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

private def l15ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5890],
    outs := [8703, 8707], params := [2] }
private def l15ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10584],
    outs := [16262, 16266], params := [2] }
private def l15ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10585],
    outs := [16270, 16274], params := [2] }

private theorem l15ZMrg_red_sm8707 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8707 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5890 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 687 l15ZMrgSmResidual
    5890 8707 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5890 8703 8707
    (by decide)

private theorem l15ZMrg_red_pm16266 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16266 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10584 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1507 l15ZMrgPmResidual0
    10584 16266 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 10584 16262 16266
    (by decide)

private theorem l15ZMrg_red_pm16274 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16274 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10585 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1508 l15ZMrgPmResidual1
    10585 16274 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 10585 16270 16274
    (by decide)

/-- The L15 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L15 attention residual transports to the exact residual
relation consumed by `l15_zigzag_moe_output_from_branch_inputs`. -/
theorem l15_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16266)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16274)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l15ZMrg_red_sm8707 initSM, l15ZMrg_red_pm16266 initPM,
    l15ZMrg_red_pm16274 initPM]
  exact hAttention

private def l15ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5892],
    outs := [8714, 8718, 8722, 8726, 8730], params := [5] }
private def l15ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10588],
    outs := [15408, 14512, 14522, 14536, 14548], params := [5] }
private def l15ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10589],
    outs := [15410, 14513, 14523, 14537, 14549], params := [5] }
private def l15ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8722], outs := [5902],
    params := [4096, 1024] }
private def l15ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14522], outs := [10610],
    params := [2048, 1024] }
private def l15ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14523], outs := [10611],
    params := [2048, 1024] }
private def l15ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5902, 5903],
    outs := [5904] }
private def l15ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10610, 5903],
    outs := [10614] }
private def l15ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10611, 5903],
    outs := [10615] }
private def l15ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5904], outs := [5905],
    params := [4096, 1] }
private def l15ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10614], outs := [10616],
    params := [2048, 1] }
private def l15ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10615], outs := [10617],
    params := [2048, 1] }
private def l15ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5905], outs := [5906] }
private def l15ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10616], outs := [10618] }
private def l15ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10617], outs := [10619] }

private theorem l15ZMrg_red_sm8722 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8722 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5892 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 689 l15ZMrgSmRef
    5892 8722 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5892 [8714, 8718, 8722, 8726, 8730]
    5 rfl 8722 (by decide)

private theorem l15ZMrg_red_pm14522 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14522 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10588 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1511 l15ZMrgPmRef0
    10588 14522 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10588
    [15408, 14512, 14522, 14536, 14548] 5 rfl 14522 (by decide)

private theorem l15ZMrg_red_pm14523 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14523 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10589 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1512 l15ZMrgPmRef1
    10589 14523 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10589
    [15410, 14513, 14523, 14537, 14549] 5 rfl 14523 (by decide)

private theorem l15ZMrg_red_sm5902 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5902 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8722) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 691 l15ZMrgSmReshape
    8722 5902 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8722 5902 [4096, 1024]

private theorem l15ZMrg_red_pm10610 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10610 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14522) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1513 l15ZMrgPmReshape0
    14522 10610 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14522 10610 [2048, 1024]

private theorem l15ZMrg_red_pm10611 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10611 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14523) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1517 l15ZMrgPmReshape1
    14523 10611 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14523 10611 [2048, 1024]

private theorem l15ZMrg_red_sm5904 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5904 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5902)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5903) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 695 l15ZMrgSmLinear
    5902 5903 5904 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5902 5903 5904

private theorem l15ZMrg_red_pm10614 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10614 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10610)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5903) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1520 l15ZMrgPmLinear0
    10610 5903 10614 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10610 5903 10614

private theorem l15ZMrg_red_pm10615 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10615 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10611)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5903) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1525 l15ZMrgPmLinear1
    10611 5903 10615 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10611 5903 10615

private theorem l15ZMrg_red_sm5905 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5905 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5904) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 699 l15ZMrgSmView
    5904 5905 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5904 5905

private theorem l15ZMrg_red_pm10616 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10616 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10614) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1528 l15ZMrgPmView0
    10614 10616 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 10614 10616

private theorem l15ZMrg_red_pm10617 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10617 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10615) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1533 l15ZMrgPmView1
    10615 10617 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 10615 10617

private theorem l15ZMrg_red_sm5906 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5906 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5905) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 703 l15ZMrgSmSigmoid
    5905 5906 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5905 5906

private theorem l15ZMrg_red_pm10618 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10618 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10616) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1536 l15ZMrgPmSigmoid0
    10616 10618 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 10616 10618

private theorem l15ZMrg_red_pm10619 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10619 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10617) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1540 l15ZMrgPmSigmoid1
    10617 10619 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 10617 10619

private theorem l15ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5903 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5903 ∉ n.outs) := by
  native_decide

private theorem l15ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5903 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5903 := by
  have hi := (hInit initGoal_5903 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5903 pm_goal_1.numRanks _ rfl,
    show initGoal_5903.tps = [{rank := 0, tid := 5903}] from rfl,
    show initGoal_5903.ts = 5903 from rfl,
    show initGoal_5903.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5903
      (by native_decide) l15ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5903
      (by native_decide) l15ZMrg_weight_not_written.2]
  exact hi

private theorem l15ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5903).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5903 = initPM 5903 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5903
      (by native_decide) l15ZMrg_weight_not_written.2
  rw [e]
  exact hPM 5903 [1, 1024] (by native_decide)

/-- The canonical L15 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l15_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5906)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10618)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10619)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14522)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14523)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMrg_red_sm8722 initSM, l15ZMrg_red_pm14522 initPM,
      l15ZMrg_red_pm14523 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5902)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10610)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10611)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMrg_red_sm5902 initSM, l15ZMrg_red_pm10610 initPM,
      l15ZMrg_red_pm10611 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l15ZMrg_weight_eq initSM initPM hInit
  have hwShape := l15ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10614)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10615)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l15ZMrg_red_sm5904 initSM, l15ZMrg_red_pm10614 initPM,
      l15ZMrg_red_pm10615 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10616)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10617)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l15ZMrg_red_sm5905 initSM, l15ZMrg_red_pm10616 initPM,
      l15ZMrg_red_pm10617 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10616)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10617)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l15ZMrg_red_sm5906 initSM, l15ZMrg_red_pm10618 initPM,
    l15ZMrg_red_pm10619 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
