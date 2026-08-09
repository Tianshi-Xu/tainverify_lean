/- Canonical Goal 1, layer 18: residual bypass and faithful scalar-gate branch. -/
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

private def l18ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6052],
    outs := [8820, 8824], params := [2] }
private def l18ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11046],
    outs := [16358, 16362], params := [2] }
private def l18ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11047],
    outs := [16366, 16370], params := [2] }

private theorem l18ZMrg_red_sm8824 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8824 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6052 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 792 l18ZMrgSmResidual
    6052 8824 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 6052 8820 8824
    (by decide)

private theorem l18ZMrg_red_pm16362 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16362 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11046 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1735 l18ZMrgPmResidual0
    11046 16362 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 11046 16358 16362
    (by decide)

private theorem l18ZMrg_red_pm16370 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16370 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11047 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1736 l18ZMrgPmResidual1
    11047 16370 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 11047 16366 16370
    (by decide)

/-- The L18 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L18 attention residual transports to the exact residual
relation consumed by `l18_zigzag_moe_output_from_branch_inputs`. -/
theorem l18_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8824)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16362)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16370)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l18ZMrg_red_sm8824 initSM, l18ZMrg_red_pm16362 initPM,
    l18ZMrg_red_pm16370 initPM]
  exact hAttention

private def l18ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6054],
    outs := [8831, 8835, 8839, 8843, 8847], params := [5] }
private def l18ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11050],
    outs := [15420, 14860, 14870, 14884, 14896], params := [5] }
private def l18ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11051],
    outs := [15422, 14861, 14871, 14885, 14897], params := [5] }
private def l18ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8839], outs := [6064],
    params := [4096, 1024] }
private def l18ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14870], outs := [11072],
    params := [2048, 1024] }
private def l18ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14871], outs := [11073],
    params := [2048, 1024] }
private def l18ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6064, 6065],
    outs := [6066] }
private def l18ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11072, 6065],
    outs := [11076] }
private def l18ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11073, 6065],
    outs := [11077] }
private def l18ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6066], outs := [6067],
    params := [4096, 1] }
private def l18ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11076], outs := [11078],
    params := [2048, 1] }
private def l18ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11077], outs := [11079],
    params := [2048, 1] }
private def l18ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [6067], outs := [6068] }
private def l18ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11078], outs := [11080] }
private def l18ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11079], outs := [11081] }

private theorem l18ZMrg_red_sm8839 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8839 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6054 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 794 l18ZMrgSmRef
    6054 8839 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6054 [8831, 8835, 8839, 8843, 8847]
    5 rfl 8839 (by decide)

private theorem l18ZMrg_red_pm14870 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14870 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11050 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1739 l18ZMrgPmRef0
    11050 14870 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11050
    [15420, 14860, 14870, 14884, 14896] 5 rfl 14870 (by decide)

private theorem l18ZMrg_red_pm14871 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14871 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11051 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1740 l18ZMrgPmRef1
    11051 14871 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11051
    [15422, 14861, 14871, 14885, 14897] 5 rfl 14871 (by decide)

private theorem l18ZMrg_red_sm6064 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6064 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8839) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 796 l18ZMrgSmReshape
    8839 6064 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8839 6064 [4096, 1024]

private theorem l18ZMrg_red_pm11072 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11072 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14870) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1741 l18ZMrgPmReshape0
    14870 11072 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14870 11072 [2048, 1024]

private theorem l18ZMrg_red_pm11073 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11073 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14871) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1745 l18ZMrgPmReshape1
    14871 11073 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14871 11073 [2048, 1024]

private theorem l18ZMrg_red_sm6066 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6066 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6064)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6065) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 800 l18ZMrgSmLinear
    6064 6065 6066 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6064 6065 6066

private theorem l18ZMrg_red_pm11076 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11076 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11072)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6065) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1748 l18ZMrgPmLinear0
    11072 6065 11076 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11072 6065 11076

private theorem l18ZMrg_red_pm11077 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11077 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11073)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6065) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1753 l18ZMrgPmLinear1
    11073 6065 11077 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11073 6065 11077

private theorem l18ZMrg_red_sm6067 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6067 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 6066) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 804 l18ZMrgSmView
    6066 6067 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 6066 6067

private theorem l18ZMrg_red_pm11078 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11078 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11076) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1756 l18ZMrgPmView0
    11076 11078 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 11076 11078

private theorem l18ZMrg_red_pm11079 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11079 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11077) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1761 l18ZMrgPmView1
    11077 11079 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 11077 11079

private theorem l18ZMrg_red_sm6068 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6068 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 6067) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 808 l18ZMrgSmSigmoid
    6067 6068 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 6067 6068

private theorem l18ZMrg_red_pm11080 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11080 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11078) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1764 l18ZMrgPmSigmoid0
    11078 11080 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 11078 11080

private theorem l18ZMrg_red_pm11081 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11081 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11079) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1768 l18ZMrgPmSigmoid1
    11079 11081 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 11079 11081

private theorem l18ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6065 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6065 ∉ n.outs) := by
  native_decide

private theorem l18ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6065 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6065 := by
  have hi := (hInit initGoal_6065 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6065 pm_goal_1.numRanks _ rfl,
    show initGoal_6065.tps = [{rank := 0, tid := 6065}] from rfl,
    show initGoal_6065.ts = 6065 from rfl,
    show initGoal_6065.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6065
      (by native_decide) l18ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6065
      (by native_decide) l18ZMrg_weight_not_written.2]
  exact hi

private theorem l18ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6065).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 6065 = initPM 6065 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6065
      (by native_decide) l18ZMrg_weight_not_written.2
  rw [e]
  exact hPM 6065 [1, 1024] (by native_decide)

/-- The canonical L18 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l18_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6068)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11080)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8839)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14870)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14871)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMrg_red_sm8839 initSM, l18ZMrg_red_pm14870 initPM,
      l18ZMrg_red_pm14871 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6064)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11072)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11073)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMrg_red_sm6064 initSM, l18ZMrg_red_pm11072 initPM,
      l18ZMrg_red_pm11073 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l18ZMrg_weight_eq initSM initPM hInit
  have hwShape := l18ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6066)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11076)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11077)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l18ZMrg_red_sm6066 initSM, l18ZMrg_red_pm11076 initPM,
      l18ZMrg_red_pm11077 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6067)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11078)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11079)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l18ZMrg_red_sm6067 initSM, l18ZMrg_red_pm11078 initPM,
      l18ZMrg_red_pm11079 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6067)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11078)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11079)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l18ZMrg_red_sm6068 initSM, l18ZMrg_red_pm11080 initPM,
    l18ZMrg_red_pm11081 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
