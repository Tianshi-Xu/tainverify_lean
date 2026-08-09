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

private def l12B2ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5674],
    outs := [8547, 8551], params := [2] }
private def l12B2ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9968],
    outs := [16134, 16138], params := [2] }
private def l12B2ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9969],
    outs := [16142, 16146], params := [2] }

private theorem l12B2ZMrg_red_sm8551 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8551 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5674 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 547 l12B2ZMrgSmResidual
    5674 8551 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5674 8547 8551
    (by decide)

private theorem l12B2ZMrg_red_pm16138 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16138 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9968 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1203 l12B2ZMrgPmResidual0
    9968 16138 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 9968 16134 16138
    (by decide)

private theorem l12B2ZMrg_red_pm16146 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16146 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9969 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1204 l12B2ZMrgPmResidual1
    9969 16146 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 9969 16142 16146
    (by decide)

/-- The L21 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L12 block-2 attention residual transports to the exact residual
relation consumed by `l12b2_zigzag_moe_output_from_branch_inputs`. -/
theorem l12b2_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8551)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16138)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16146)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l12B2ZMrg_red_sm8551 initSM, l12B2ZMrg_red_pm16138 initPM,
    l12B2ZMrg_red_pm16146 initPM]
  exact hAttention

private def l12B2ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5676],
    outs := [8558, 8562, 8566, 8570, 8574], params := [5] }
private def l12B2ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9972],
    outs := [15392, 14048, 14058, 14072, 14084], params := [5] }
private def l12B2ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9973],
    outs := [15394, 14049, 14059, 14073, 14085], params := [5] }
private def l12B2ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8566], outs := [5686],
    params := [4096, 1024] }
private def l12B2ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14058], outs := [9994],
    params := [2048, 1024] }
private def l12B2ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14059], outs := [9995],
    params := [2048, 1024] }
private def l12B2ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5686, 5687],
    outs := [5688] }
private def l12B2ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9994, 5687],
    outs := [9998] }
private def l12B2ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9995, 5687],
    outs := [9999] }
private def l12B2ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5688], outs := [5689],
    params := [4096, 1] }
private def l12B2ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9998], outs := [10000],
    params := [2048, 1] }
private def l12B2ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9999], outs := [10001],
    params := [2048, 1] }
private def l12B2ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5689], outs := [5690] }
private def l12B2ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10000], outs := [10002] }
private def l12B2ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10001], outs := [10003] }

private theorem l12B2ZMrg_red_sm8566 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8566 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5676 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 549 l12B2ZMrgSmRef
    5676 8566 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5676 [8558, 8562, 8566, 8570, 8574]
    5 rfl 8566 (by decide)

private theorem l12B2ZMrg_red_pm14058 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14058 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9972 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1207 l12B2ZMrgPmRef0
    9972 14058 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9972
    [15392, 14048, 14058, 14072, 14084] 5 rfl 14058 (by decide)

private theorem l12B2ZMrg_red_pm14059 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14059 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9973 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1208 l12B2ZMrgPmRef1
    9973 14059 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9973
    [15394, 14049, 14059, 14073, 14085] 5 rfl 14059 (by decide)

private theorem l12B2ZMrg_red_sm5686 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5686 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8566) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 551 l12B2ZMrgSmReshape
    8566 5686 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8566 5686 [4096, 1024]

private theorem l12B2ZMrg_red_pm9994 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9994 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14058) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1209 l12B2ZMrgPmReshape0
    14058 9994 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14058 9994 [2048, 1024]

private theorem l12B2ZMrg_red_pm9995 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9995 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14059) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1213 l12B2ZMrgPmReshape1
    14059 9995 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14059 9995 [2048, 1024]

private theorem l12B2ZMrg_red_sm5688 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5688 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5686)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5687) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 555 l12B2ZMrgSmLinear
    5686 5687 5688 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5686 5687 5688

private theorem l12B2ZMrg_red_pm9998 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9998 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9994)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5687) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1216 l12B2ZMrgPmLinear0
    9994 5687 9998 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9994 5687 9998

private theorem l12B2ZMrg_red_pm9999 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9999 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9995)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5687) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1221 l12B2ZMrgPmLinear1
    9995 5687 9999 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9995 5687 9999

private theorem l12B2ZMrg_red_sm5689 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5689 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5688) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 559 l12B2ZMrgSmView
    5688 5689 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5688 5689

private theorem l12B2ZMrg_red_pm10000 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10000 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9998) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1224 l12B2ZMrgPmView0
    9998 10000 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9998 10000

private theorem l12B2ZMrg_red_pm10001 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10001 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9999) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1229 l12B2ZMrgPmView1
    9999 10001 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9999 10001

private theorem l12B2ZMrg_red_sm5690 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5690 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5689) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 563 l12B2ZMrgSmSigmoid
    5689 5690 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5689 5690

private theorem l12B2ZMrg_red_pm10002 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10002 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10000) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1232 l12B2ZMrgPmSigmoid0
    10000 10002 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 10000 10002

private theorem l12B2ZMrg_red_pm10003 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10003 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10001) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1236 l12B2ZMrgPmSigmoid1
    10001 10003 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 10001 10003

private theorem l12B2ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5687 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5687 ∉ n.outs) := by
  native_decide

private theorem l12B2ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5687 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5687 := by
  have hi := (hInit initGoal_5687 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5687 pm_goal_1.numRanks _ rfl,
    show initGoal_5687.tps = [{rank := 0, tid := 5687}] from rfl,
    show initGoal_5687.ts = 5687 from rfl,
    show initGoal_5687.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5687
      (by native_decide) l12B2ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5687
      (by native_decide) l12B2ZMrg_weight_not_written.2]
  exact hi

private theorem l12B2ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5687).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5687 = initPM 5687 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5687
      (by native_decide) l12B2ZMrg_weight_not_written.2
  rw [e]
  exact hPM 5687 [1, 1024] (by native_decide)

/-- The canonical L21 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l12b2_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5690)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10002)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10003)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8566)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMrg_red_sm8566 initSM, l12B2ZMrg_red_pm14058 initPM,
      l12B2ZMrg_red_pm14059 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5686)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9994)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9995)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMrg_red_sm5686 initSM, l12B2ZMrg_red_pm9994 initPM,
      l12B2ZMrg_red_pm9995 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l12B2ZMrg_weight_eq initSM initPM hInit
  have hwShape := l12B2ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5688)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9999)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l12B2ZMrg_red_sm5688 initSM, l12B2ZMrg_red_pm9998 initPM,
      l12B2ZMrg_red_pm9999 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5689)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10001)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l12B2ZMrg_red_sm5689 initSM, l12B2ZMrg_red_pm10000 initPM,
      l12B2ZMrg_red_pm10001 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5689)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10001)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l12B2ZMrg_red_sm5690 initSM, l12B2ZMrg_red_pm10002 initPM,
    l12B2ZMrg_red_pm10003 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
