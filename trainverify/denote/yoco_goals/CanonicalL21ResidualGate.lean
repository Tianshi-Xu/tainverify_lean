/- Canonical Goal 1, layer 21: residual bypass and faithful scalar-gate branch. -/
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

private def cL21rgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6160],
    outs := [8898, 8902], params := [2] }
private def cL21rgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11354],
    outs := [16422, 16426], params := [2] }
private def cL21rgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11355],
    outs := [16430, 16434], params := [2] }

private theorem cL21rg_red_sm8902 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8902 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6160 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 862 cL21rgSmResidual
    6160 8902 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 6160 8898 8902
    (by decide)

private theorem cL21rg_red_pm16426 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16426 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11354 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1887 cL21rgPmResidual0
    11354 16426 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 11354 16422 16426
    (by decide)

private theorem cL21rg_red_pm16434 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16434 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11355 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1888 cL21rgPmResidual1
    11355 16434 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 11355 16430 16434
    (by decide)

/-- The L21 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L20 output transports to the exact residual
relation consumed by `canonical_l21_output_from_branch_inputs`. -/
theorem canonical_l21_residual_from_layer20_output (initSM initPM : Store)
    (hLayer20 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8902)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16426)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL21rg_red_sm8902 initSM, cL21rg_red_pm16426 initPM,
    cL21rg_red_pm16434 initPM]
  exact hLayer20

private def cL21rgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6162],
    outs := [8909, 8913, 8917, 8921, 8925], params := [5] }
private def cL21rgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11358],
    outs := [15428, 15092, 15102, 15116, 15128], params := [5] }
private def cL21rgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11359],
    outs := [15430, 15093, 15103, 15117, 15129], params := [5] }
private def cL21rgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8917], outs := [6172],
    params := [4096, 1024] }
private def cL21rgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15102], outs := [11380],
    params := [2048, 1024] }
private def cL21rgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15103], outs := [11381],
    params := [2048, 1024] }
private def cL21rgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6172, 6173],
    outs := [6174] }
private def cL21rgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11380, 6173],
    outs := [11384] }
private def cL21rgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11381, 6173],
    outs := [11385] }
private def cL21rgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6174], outs := [6175],
    params := [4096, 1] }
private def cL21rgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11384], outs := [11386],
    params := [2048, 1] }
private def cL21rgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11385], outs := [11387],
    params := [2048, 1] }
private def cL21rgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [6175], outs := [6176] }
private def cL21rgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11386], outs := [11388] }
private def cL21rgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11387], outs := [11389] }

private theorem cL21rg_red_sm8917 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8917 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6162 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 864 cL21rgSmRef
    6162 8917 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6162 [8909, 8913, 8917, 8921, 8925]
    5 rfl 8917 (by decide)

private theorem cL21rg_red_pm15102 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15102 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11358 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1891 cL21rgPmRef0
    11358 15102 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11358
    [15428, 15092, 15102, 15116, 15128] 5 rfl 15102 (by decide)

private theorem cL21rg_red_pm15103 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15103 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11359 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1892 cL21rgPmRef1
    11359 15103 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11359
    [15430, 15093, 15103, 15117, 15129] 5 rfl 15103 (by decide)

private theorem cL21rg_red_sm6172 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6172 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8917) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 866 cL21rgSmReshape
    8917 6172 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8917 6172 [4096, 1024]

private theorem cL21rg_red_pm11380 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11380 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 15102) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1893 cL21rgPmReshape0
    15102 11380 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15102 11380 [2048, 1024]

private theorem cL21rg_red_pm11381 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11381 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 15103) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1897 cL21rgPmReshape1
    15103 11381 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15103 11381 [2048, 1024]

private theorem cL21rg_red_sm6174 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6174 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6172)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6173) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 870 cL21rgSmLinear
    6172 6173 6174 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21rgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6172 6173 6174

private theorem cL21rg_red_pm11384 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11384 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11380)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6173) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1900 cL21rgPmLinear0
    11380 6173 11384 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11380 6173 11384

private theorem cL21rg_red_pm11385 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11385 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11381)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6173) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1905 cL21rgPmLinear1
    11381 6173 11385 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11381 6173 11385

private theorem cL21rg_red_sm6175 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6175 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 6174) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 874 cL21rgSmView
    6174 6175 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 6174 6175

private theorem cL21rg_red_pm11386 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11386 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11384) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1908 cL21rgPmView0
    11384 11386 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 11384 11386

private theorem cL21rg_red_pm11387 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11387 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11385) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1913 cL21rgPmView1
    11385 11387 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 11385 11387

private theorem cL21rg_red_sm6176 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6176 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 6175) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 878 cL21rgSmSigmoid
    6175 6176 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 6175 6176

private theorem cL21rg_red_pm11388 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11388 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11386) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1916 cL21rgPmSigmoid0
    11386 11388 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 11386 11388

private theorem cL21rg_red_pm11389 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11389 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11387) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1920 cL21rgPmSigmoid1
    11387 11389 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21rgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 11387 11389

private theorem cL21rg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6173 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6173 ∉ n.outs) := by
  native_decide

private theorem cL21rg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6173 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6173 := by
  have hi := (hInit initGoal_6173 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6173 pm_goal_1.numRanks _ rfl,
    show initGoal_6173.tps = [{rank := 0, tid := 6173}] from rfl,
    show initGoal_6173.ts = 6173 from rfl,
    show initGoal_6173.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6173
      (by native_decide) cL21rg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6173
      (by native_decide) cL21rg_weight_not_written.2]
  exact hi

private theorem cL21rg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6173).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 6173 = initPM 6173 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6173
      (by native_decide) cL21rg_weight_not_written.2
  rw [e]
  exact hPM 6173 [1, 1024] (by native_decide)

/-- The canonical L21 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem canonical_l21_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11358)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11359)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6176)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11388)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11389)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8917)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15102)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15103)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21rg_red_sm8917 initSM, cL21rg_red_pm15102 initPM,
      cL21rg_red_pm15103 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6172)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11380)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11381)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21rg_red_sm6172 initSM, cL21rg_red_pm11380 initPM,
      cL21rg_red_pm11381 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := cL21rg_weight_eq initSM initPM hInit
  have hwShape := cL21rg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6174)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11384)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11385)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [cL21rg_red_sm6174 initSM, cL21rg_red_pm11384 initPM,
      cL21rg_red_pm11385 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6175)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11386)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11387)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [cL21rg_red_sm6175 initSM, cL21rg_red_pm11386 initPM,
      cL21rg_red_pm11387 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6175)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11386)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11387)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [cL21rg_red_sm6176 initSM, cL21rg_red_pm11388 initPM,
    cL21rg_red_pm11389 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
