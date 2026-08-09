/- Canonical Goal 1, layer 19: residual bypass and faithful scalar-gate branch. -/
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

private def l19ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6106],
    outs := [8859, 8863], params := [2] }
private def l19ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11200],
    outs := [16390, 16394], params := [2] }
private def l19ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11201],
    outs := [16398, 16402], params := [2] }

private theorem l19ZMrg_red_sm8863 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8863 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6106 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 827 l19ZMrgSmResidual
    6106 8863 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 6106 8859 8863
    (by decide)

private theorem l19ZMrg_red_pm16394 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16394 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11200 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1811 l19ZMrgPmResidual0
    11200 16394 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 11200 16390 16394
    (by decide)

private theorem l19ZMrg_red_pm16402 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16402 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11201 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1812 l19ZMrgPmResidual1
    11201 16402 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 11201 16398 16402
    (by decide)

/-- The L19 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L19 attention residual transports to the exact residual
relation consumed by `l19_zigzag_moe_output_from_branch_inputs`. -/
theorem l19_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8863)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16394)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16402)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l19ZMrg_red_sm8863 initSM, l19ZMrg_red_pm16394 initPM,
    l19ZMrg_red_pm16402 initPM]
  exact hAttention

private def l19ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6108],
    outs := [8870, 8874, 8878, 8882, 8886], params := [5] }
private def l19ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11204],
    outs := [15424, 14976, 14986, 15000, 15012], params := [5] }
private def l19ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11205],
    outs := [15426, 14977, 14987, 15001, 15013], params := [5] }
private def l19ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8878], outs := [6118],
    params := [4096, 1024] }
private def l19ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14986], outs := [11226],
    params := [2048, 1024] }
private def l19ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14987], outs := [11227],
    params := [2048, 1024] }
private def l19ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6118, 6119],
    outs := [6120] }
private def l19ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11226, 6119],
    outs := [11230] }
private def l19ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11227, 6119],
    outs := [11231] }
private def l19ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6120], outs := [6121],
    params := [4096, 1] }
private def l19ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11230], outs := [11232],
    params := [2048, 1] }
private def l19ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11231], outs := [11233],
    params := [2048, 1] }
private def l19ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [6121], outs := [6122] }
private def l19ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [11232], outs := [11234] }
private def l19ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [11233], outs := [11235] }

private theorem l19ZMrg_red_sm8878 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8878 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6108 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 829 l19ZMrgSmRef
    6108 8878 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6108 [8870, 8874, 8878, 8882, 8886]
    5 rfl 8878 (by decide)

private theorem l19ZMrg_red_pm14986 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14986 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11204 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1815 l19ZMrgPmRef0
    11204 14986 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11204
    [15424, 14976, 14986, 15000, 15012] 5 rfl 14986 (by decide)

private theorem l19ZMrg_red_pm14987 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14987 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11205 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1816 l19ZMrgPmRef1
    11205 14987 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11205
    [15426, 14977, 14987, 15001, 15013] 5 rfl 14987 (by decide)

private theorem l19ZMrg_red_sm6118 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6118 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8878) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 831 l19ZMrgSmReshape
    8878 6118 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8878 6118 [4096, 1024]

private theorem l19ZMrg_red_pm11226 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11226 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14986) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1817 l19ZMrgPmReshape0
    14986 11226 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14986 11226 [2048, 1024]

private theorem l19ZMrg_red_pm11227 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11227 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14987) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1821 l19ZMrgPmReshape1
    14987 11227 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14987 11227 [2048, 1024]

private theorem l19ZMrg_red_sm6120 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6120 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6118)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6119) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 835 l19ZMrgSmLinear
    6118 6119 6120 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6118 6119 6120

private theorem l19ZMrg_red_pm11230 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11230 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11226)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6119) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1824 l19ZMrgPmLinear0
    11226 6119 11230 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11226 6119 11230

private theorem l19ZMrg_red_pm11231 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11231 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11227)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6119) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1829 l19ZMrgPmLinear1
    11227 6119 11231 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11227 6119 11231

private theorem l19ZMrg_red_sm6121 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6121 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 6120) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 839 l19ZMrgSmView
    6120 6121 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 6120 6121

private theorem l19ZMrg_red_pm11232 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11232 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11230) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1832 l19ZMrgPmView0
    11230 11232 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 11230 11232

private theorem l19ZMrg_red_pm11233 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11233 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 11231) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1837 l19ZMrgPmView1
    11231 11233 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 11231 11233

private theorem l19ZMrg_red_sm6122 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6122 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 6121) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 843 l19ZMrgSmSigmoid
    6121 6122 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 6121 6122

private theorem l19ZMrg_red_pm11234 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11234 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11232) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1840 l19ZMrgPmSigmoid0
    11232 11234 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 11232 11234

private theorem l19ZMrg_red_pm11235 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11235 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 11233) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1844 l19ZMrgPmSigmoid1
    11233 11235 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 11233 11235

private theorem l19ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6119 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6119 ∉ n.outs) := by
  native_decide

private theorem l19ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6119 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6119 := by
  have hi := (hInit initGoal_6119 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6119 pm_goal_1.numRanks _ rfl,
    show initGoal_6119.tps = [{rank := 0, tid := 6119}] from rfl,
    show initGoal_6119.ts = 6119 from rfl,
    show initGoal_6119.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6119
      (by native_decide) l19ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6119
      (by native_decide) l19ZMrg_weight_not_written.2]
  exact hi

private theorem l19ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6119).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 6119 = initPM 6119 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6119
      (by native_decide) l19ZMrg_weight_not_written.2
  rw [e]
  exact hPM 6119 [1, 1024] (by native_decide)

/-- The canonical L19 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l19_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11204)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11205)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11235)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8878)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14986)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14987)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMrg_red_sm8878 initSM, l19ZMrg_red_pm14986 initPM,
      l19ZMrg_red_pm14987 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6118)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11227)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMrg_red_sm6118 initSM, l19ZMrg_red_pm11226 initPM,
      l19ZMrg_red_pm11227 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l19ZMrg_weight_eq initSM initPM hInit
  have hwShape := l19ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6120)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11231)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l19ZMrg_red_sm6120 initSM, l19ZMrg_red_pm11230 initPM,
      l19ZMrg_red_pm11231 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6121)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11233)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l19ZMrg_red_sm6121 initSM, l19ZMrg_red_pm11232 initPM,
      l19ZMrg_red_pm11233 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6121)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11232)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11233)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l19ZMrg_red_sm6122 initSM, l19ZMrg_red_pm11234 initPM,
    l19ZMrg_red_pm11235 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
