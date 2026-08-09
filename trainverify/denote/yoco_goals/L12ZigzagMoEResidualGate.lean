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
  { rank := 0, op := "OpName.FW_multiref", ins := [5620],
    outs := [8508, 8512], params := [2] }
private def l12ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9812],
    outs := [16102, 16106], params := [2] }
private def l12ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9813],
    outs := [16110, 16114], params := [2] }

private theorem l12ZMrg_red_sm8512 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8512 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5620 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 512 l12ZMrgSmResidual
    5620 8512 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5620 8508 8512
    (by decide)

private theorem l12ZMrg_red_pm16106 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16106 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9812 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1127 l12ZMrgPmResidual0
    9812 16106 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 9812 16102 16106
    (by decide)

private theorem l12ZMrg_red_pm16114 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16114 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9813 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1128 l12ZMrgPmResidual1
    9813 16114 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 9813 16110 16114
    (by decide)

/-- The L21 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L12 attention residual transports to the exact residual
relation consumed by `l12_zigzag_moe_output_from_branch_inputs`. -/
theorem l12_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16114)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l12ZMrg_red_sm8512 initSM, l12ZMrg_red_pm16106 initPM,
    l12ZMrg_red_pm16114 initPM]
  exact hAttention

private def l12ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622],
    outs := [8519, 8523, 8527, 8531, 8535], params := [5] }
private def l12ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818],
    outs := [15388, 13932, 13942, 13956, 13968], params := [5] }
private def l12ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819],
    outs := [15390, 13933, 13943, 13957, 13969], params := [5] }
private def l12ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8527], outs := [5632],
    params := [4096, 1024] }
private def l12ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13942], outs := [9840],
    params := [2048, 1024] }
private def l12ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13943], outs := [9841],
    params := [2048, 1024] }
private def l12ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5632, 5633],
    outs := [5634] }
private def l12ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9840, 5633],
    outs := [9844] }
private def l12ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9841, 5633],
    outs := [9845] }
private def l12ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5634], outs := [5635],
    params := [4096, 1] }
private def l12ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9844], outs := [9846],
    params := [2048, 1] }
private def l12ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9845], outs := [9847],
    params := [2048, 1] }
private def l12ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5635], outs := [5636] }
private def l12ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9846], outs := [9848] }
private def l12ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9847], outs := [9849] }

private theorem l12ZMrg_red_sm8527 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8527 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 514 l12ZMrgSmRef
    5622 8527 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8519, 8523, 8527, 8531, 8535]
    5 rfl 8527 (by decide)

private theorem l12ZMrg_red_pm13942 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13942 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1131 l12ZMrgPmRef0
    9818 13942 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818
    [15388, 13932, 13942, 13956, 13968] 5 rfl 13942 (by decide)

private theorem l12ZMrg_red_pm13943 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13943 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1132 l12ZMrgPmRef1
    9819 13943 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819
    [15390, 13933, 13943, 13957, 13969] 5 rfl 13943 (by decide)

private theorem l12ZMrg_red_sm5632 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5632 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8527) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 516 l12ZMrgSmReshape
    8527 5632 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8527 5632 [4096, 1024]

private theorem l12ZMrg_red_pm9840 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9840 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13942) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1133 l12ZMrgPmReshape0
    13942 9840 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13942 9840 [2048, 1024]

private theorem l12ZMrg_red_pm9841 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9841 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13943) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1137 l12ZMrgPmReshape1
    13943 9841 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13943 9841 [2048, 1024]

private theorem l12ZMrg_red_sm5634 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5634 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5632)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 520 l12ZMrgSmLinear
    5632 5633 5634 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5632 5633 5634

private theorem l12ZMrg_red_pm9844 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9844 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9840)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1140 l12ZMrgPmLinear0
    9840 5633 9844 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9840 5633 9844

private theorem l12ZMrg_red_pm9845 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9845 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9841)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1145 l12ZMrgPmLinear1
    9841 5633 9845 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9841 5633 9845

private theorem l12ZMrg_red_sm5635 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5635 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5634) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 524 l12ZMrgSmView
    5634 5635 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5634 5635

private theorem l12ZMrg_red_pm9846 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9846 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9844) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1148 l12ZMrgPmView0
    9844 9846 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9844 9846

private theorem l12ZMrg_red_pm9847 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9847 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9845) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1153 l12ZMrgPmView1
    9845 9847 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9845 9847

private theorem l12ZMrg_red_sm5636 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5636 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5635) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 528 l12ZMrgSmSigmoid
    5635 5636 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5635 5636

private theorem l12ZMrg_red_pm9848 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9848 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9846) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1156 l12ZMrgPmSigmoid0
    9846 9848 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9846 9848

private theorem l12ZMrg_red_pm9849 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9849 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9847) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1160 l12ZMrgPmSigmoid1
    9847 9849 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9847 9849

private theorem l12ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5633 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5633 ∉ n.outs) := by
  native_decide

private theorem l12ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5633 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5633 := by
  have hi := (hInit initGoal_5633 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5633 pm_goal_1.numRanks _ rfl,
    show initGoal_5633.tps = [{rank := 0, tid := 5633}] from rfl,
    show initGoal_5633.ts = 5633 from rfl,
    show initGoal_5633.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5633
      (by native_decide) l12ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5633
      (by native_decide) l12ZMrg_weight_not_written.2]
  exact hi

private theorem l12ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5633).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5633 = initPM 5633 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5633
      (by native_decide) l12ZMrg_weight_not_written.2
  rw [e]
  exact hPM 5633 [1, 1024] (by native_decide)

/-- The canonical L21 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l12_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9848)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9849)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8527)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13942)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13943)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMrg_red_sm8527 initSM, l12ZMrg_red_pm13942 initPM,
      l12ZMrg_red_pm13943 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9840)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9841)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMrg_red_sm5632 initSM, l12ZMrg_red_pm9840 initPM,
      l12ZMrg_red_pm9841 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l12ZMrg_weight_eq initSM initPM hInit
  have hwShape := l12ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5634)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9844)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9845)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l12ZMrg_red_sm5634 initSM, l12ZMrg_red_pm9844 initPM,
      l12ZMrg_red_pm9845 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5635)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9846)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9847)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l12ZMrg_red_sm5635 initSM, l12ZMrg_red_pm9846 initPM,
      l12ZMrg_red_pm9847 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5635)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9846)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9847)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l12ZMrg_red_sm5636 initSM, l12ZMrg_red_pm9848 initPM,
    l12ZMrg_red_pm9849 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
