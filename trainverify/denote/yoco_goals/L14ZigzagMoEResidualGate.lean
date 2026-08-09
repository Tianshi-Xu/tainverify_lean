/- Canonical Goal 1, layer 14: residual bypass and faithful scalar-gate branch. -/
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

private def l14ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5836],
    outs := [8664, 8668], params := [2] }
private def l14ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10430],
    outs := [16230, 16234], params := [2] }
private def l14ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10431],
    outs := [16238, 16242], params := [2] }

private theorem l14ZMrg_red_sm8668 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8668 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5836 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 652 l14ZMrgSmResidual
    5836 8668 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5836 8664 8668
    (by decide)

private theorem l14ZMrg_red_pm16234 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16234 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10430 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1431 l14ZMrgPmResidual0
    10430 16234 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 10430 16230 16234
    (by decide)

private theorem l14ZMrg_red_pm16242 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16242 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10431 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1432 l14ZMrgPmResidual1
    10431 16242 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 10431 16238 16242
    (by decide)

/-- The L14 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L14 attention residual transports to the exact residual
relation consumed by `l14_zigzag_moe_output_from_branch_inputs`. -/
theorem l14_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8668)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16242)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l14ZMrg_red_sm8668 initSM, l14ZMrg_red_pm16234 initPM,
    l14ZMrg_red_pm16242 initPM]
  exact hAttention

private def l14ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5838],
    outs := [8675, 8679, 8683, 8687, 8691], params := [5] }
private def l14ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10434],
    outs := [15404, 14396, 14406, 14420, 14432], params := [5] }
private def l14ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10435],
    outs := [15406, 14397, 14407, 14421, 14433], params := [5] }
private def l14ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8683], outs := [5848],
    params := [4096, 1024] }
private def l14ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14406], outs := [10456],
    params := [2048, 1024] }
private def l14ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14407], outs := [10457],
    params := [2048, 1024] }
private def l14ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5848, 5849],
    outs := [5850] }
private def l14ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10456, 5849],
    outs := [10460] }
private def l14ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10457, 5849],
    outs := [10461] }
private def l14ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5850], outs := [5851],
    params := [4096, 1] }
private def l14ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10460], outs := [10462],
    params := [2048, 1] }
private def l14ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10461], outs := [10463],
    params := [2048, 1] }
private def l14ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5851], outs := [5852] }
private def l14ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10462], outs := [10464] }
private def l14ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10463], outs := [10465] }

private theorem l14ZMrg_red_sm8683 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8683 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5838 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 654 l14ZMrgSmRef
    5838 8683 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5838 [8675, 8679, 8683, 8687, 8691]
    5 rfl 8683 (by decide)

private theorem l14ZMrg_red_pm14406 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14406 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10434 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1435 l14ZMrgPmRef0
    10434 14406 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10434
    [15404, 14396, 14406, 14420, 14432] 5 rfl 14406 (by decide)

private theorem l14ZMrg_red_pm14407 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14407 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10435 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1436 l14ZMrgPmRef1
    10435 14407 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10435
    [15406, 14397, 14407, 14421, 14433] 5 rfl 14407 (by decide)

private theorem l14ZMrg_red_sm5848 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5848 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8683) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 656 l14ZMrgSmReshape
    8683 5848 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8683 5848 [4096, 1024]

private theorem l14ZMrg_red_pm10456 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10456 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14406) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1437 l14ZMrgPmReshape0
    14406 10456 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14406 10456 [2048, 1024]

private theorem l14ZMrg_red_pm10457 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10457 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14407) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1441 l14ZMrgPmReshape1
    14407 10457 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14407 10457 [2048, 1024]

private theorem l14ZMrg_red_sm5850 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5850 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5848)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5849) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 660 l14ZMrgSmLinear
    5848 5849 5850 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5848 5849 5850

private theorem l14ZMrg_red_pm10460 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10460 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10456)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5849) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1444 l14ZMrgPmLinear0
    10456 5849 10460 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10456 5849 10460

private theorem l14ZMrg_red_pm10461 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10461 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10457)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5849) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1449 l14ZMrgPmLinear1
    10457 5849 10461 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10457 5849 10461

private theorem l14ZMrg_red_sm5851 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5851 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5850) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 664 l14ZMrgSmView
    5850 5851 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5850 5851

private theorem l14ZMrg_red_pm10462 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10462 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10460) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1452 l14ZMrgPmView0
    10460 10462 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 10460 10462

private theorem l14ZMrg_red_pm10463 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10463 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10461) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1457 l14ZMrgPmView1
    10461 10463 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 10461 10463

private theorem l14ZMrg_red_sm5852 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5852 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5851) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 668 l14ZMrgSmSigmoid
    5851 5852 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5851 5852

private theorem l14ZMrg_red_pm10464 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10464 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10462) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1460 l14ZMrgPmSigmoid0
    10462 10464 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 10462 10464

private theorem l14ZMrg_red_pm10465 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10465 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10463) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1464 l14ZMrgPmSigmoid1
    10463 10465 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 10463 10465

private theorem l14ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5849 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5849 ∉ n.outs) := by
  native_decide

private theorem l14ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5849 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5849 := by
  have hi := (hInit initGoal_5849 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5849 pm_goal_1.numRanks _ rfl,
    show initGoal_5849.tps = [{rank := 0, tid := 5849}] from rfl,
    show initGoal_5849.ts = 5849 from rfl,
    show initGoal_5849.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5849
      (by native_decide) l14ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5849
      (by native_decide) l14ZMrg_weight_not_written.2]
  exact hi

private theorem l14ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5849).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5849 = initPM 5849 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5849
      (by native_decide) l14ZMrg_weight_not_written.2
  rw [e]
  exact hPM 5849 [1, 1024] (by native_decide)

/-- The canonical L14 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l14_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10435)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5852)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10464)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10465)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8683)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14406)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14407)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMrg_red_sm8683 initSM, l14ZMrg_red_pm14406 initPM,
      l14ZMrg_red_pm14407 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5848)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10456)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10457)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMrg_red_sm5848 initSM, l14ZMrg_red_pm10456 initPM,
      l14ZMrg_red_pm10457 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l14ZMrg_weight_eq initSM initPM hInit
  have hwShape := l14ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5850)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10460)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10461)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l14ZMrg_red_sm5850 initSM, l14ZMrg_red_pm10460 initPM,
      l14ZMrg_red_pm10461 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5851)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10462)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10463)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l14ZMrg_red_sm5851 initSM, l14ZMrg_red_pm10462 initPM,
      l14ZMrg_red_pm10463 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5851)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10462)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10463)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l14ZMrg_red_sm5852 initSM, l14ZMrg_red_pm10464 initPM,
    l14ZMrg_red_pm10465 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
