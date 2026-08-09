/- Canonical Goal 1, layer 17: residual bypass and faithful scalar-gate branch. -/
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

private def l17ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5998],
    outs := [8781, 8785], params := [2] }
private def l17ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10892],
    outs := [16326, 16330], params := [2] }
private def l17ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10893],
    outs := [16334, 16338], params := [2] }

private theorem l17ZMrg_red_sm8785 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8785 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5998 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 757 l17ZMrgSmResidual
    5998 8785 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5998 8781 8785
    (by decide)

private theorem l17ZMrg_red_pm16330 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16330 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10892 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1659 l17ZMrgPmResidual0
    10892 16330 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 10892 16326 16330
    (by decide)

private theorem l17ZMrg_red_pm16338 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16338 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10893 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1660 l17ZMrgPmResidual1
    10893 16338 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 10893 16334 16338
    (by decide)

/-- The L17 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L17 attention residual transports to the exact residual
relation consumed by `l17_zigzag_moe_output_from_branch_inputs`. -/
theorem l17_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8785)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16330)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16338)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l17ZMrg_red_sm8785 initSM, l17ZMrg_red_pm16330 initPM,
    l17ZMrg_red_pm16338 initPM]
  exact hAttention

private def l17ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6000],
    outs := [8792, 8796, 8800, 8804, 8808], params := [5] }
private def l17ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10896],
    outs := [15416, 14744, 14754, 14768, 14780], params := [5] }
private def l17ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10897],
    outs := [15418, 14745, 14755, 14769, 14781], params := [5] }
private def l17ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8800], outs := [6010],
    params := [4096, 1024] }
private def l17ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14754], outs := [10918],
    params := [2048, 1024] }
private def l17ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14755], outs := [10919],
    params := [2048, 1024] }
private def l17ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6010, 6011],
    outs := [6012] }
private def l17ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10918, 6011],
    outs := [10922] }
private def l17ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10919, 6011],
    outs := [10923] }
private def l17ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6012], outs := [6013],
    params := [4096, 1] }
private def l17ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10922], outs := [10924],
    params := [2048, 1] }
private def l17ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10923], outs := [10925],
    params := [2048, 1] }
private def l17ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [6013], outs := [6014] }
private def l17ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10924], outs := [10926] }
private def l17ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10925], outs := [10927] }

private theorem l17ZMrg_red_sm8800 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8800 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6000 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 759 l17ZMrgSmRef
    6000 8800 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6000 [8792, 8796, 8800, 8804, 8808]
    5 rfl 8800 (by decide)

private theorem l17ZMrg_red_pm14754 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14754 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10896 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1663 l17ZMrgPmRef0
    10896 14754 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10896
    [15416, 14744, 14754, 14768, 14780] 5 rfl 14754 (by decide)

private theorem l17ZMrg_red_pm14755 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14755 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10897 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1664 l17ZMrgPmRef1
    10897 14755 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10897
    [15418, 14745, 14755, 14769, 14781] 5 rfl 14755 (by decide)

private theorem l17ZMrg_red_sm6010 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6010 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8800) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 761 l17ZMrgSmReshape
    8800 6010 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8800 6010 [4096, 1024]

private theorem l17ZMrg_red_pm10918 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10918 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14754) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1665 l17ZMrgPmReshape0
    14754 10918 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14754 10918 [2048, 1024]

private theorem l17ZMrg_red_pm10919 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10919 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14755) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1669 l17ZMrgPmReshape1
    14755 10919 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14755 10919 [2048, 1024]

private theorem l17ZMrg_red_sm6012 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6012 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6010)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6011) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 765 l17ZMrgSmLinear
    6010 6011 6012 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6010 6011 6012

private theorem l17ZMrg_red_pm10922 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10922 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10918)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6011) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1672 l17ZMrgPmLinear0
    10918 6011 10922 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10918 6011 10922

private theorem l17ZMrg_red_pm10923 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10923 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10919)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6011) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1677 l17ZMrgPmLinear1
    10919 6011 10923 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10919 6011 10923

private theorem l17ZMrg_red_sm6013 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6013 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 6012) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 769 l17ZMrgSmView
    6012 6013 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 6012 6013

private theorem l17ZMrg_red_pm10924 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10924 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10922) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1680 l17ZMrgPmView0
    10922 10924 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 10922 10924

private theorem l17ZMrg_red_pm10925 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10925 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10923) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1685 l17ZMrgPmView1
    10923 10925 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 10923 10925

private theorem l17ZMrg_red_sm6014 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6014 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 6013) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 773 l17ZMrgSmSigmoid
    6013 6014 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 6013 6014

private theorem l17ZMrg_red_pm10926 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10926 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10924) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1688 l17ZMrgPmSigmoid0
    10924 10926 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 10924 10926

private theorem l17ZMrg_red_pm10927 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10927 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10925) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1692 l17ZMrgPmSigmoid1
    10925 10927 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 10925 10927

private theorem l17ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6011 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6011 ∉ n.outs) := by
  native_decide

private theorem l17ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6011 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6011 := by
  have hi := (hInit initGoal_6011 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6011 pm_goal_1.numRanks _ rfl,
    show initGoal_6011.tps = [{rank := 0, tid := 6011}] from rfl,
    show initGoal_6011.ts = 6011 from rfl,
    show initGoal_6011.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6011
      (by native_decide) l17ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6011
      (by native_decide) l17ZMrg_weight_not_written.2]
  exact hi

private theorem l17ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6011).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 6011 = initPM 6011 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6011
      (by native_decide) l17ZMrg_weight_not_written.2
  rw [e]
  exact hPM 6011 [1, 1024] (by native_decide)

/-- The canonical L17 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l17_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6014)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10926)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10927)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8800)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14755)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMrg_red_sm8800 initSM, l17ZMrg_red_pm14754 initPM,
      l17ZMrg_red_pm14755 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6010)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10918)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10919)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMrg_red_sm6010 initSM, l17ZMrg_red_pm10918 initPM,
      l17ZMrg_red_pm10919 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l17ZMrg_weight_eq initSM initPM hInit
  have hwShape := l17ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10922)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10923)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l17ZMrg_red_sm6012 initSM, l17ZMrg_red_pm10922 initPM,
      l17ZMrg_red_pm10923 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6013)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10924)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10925)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l17ZMrg_red_sm6013 initSM, l17ZMrg_red_pm10924 initPM,
      l17ZMrg_red_pm10925 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6013)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10924)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10925)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l17ZMrg_red_sm6014 initSM, l17ZMrg_red_pm10926 initPM,
    l17ZMrg_red_pm10927 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
