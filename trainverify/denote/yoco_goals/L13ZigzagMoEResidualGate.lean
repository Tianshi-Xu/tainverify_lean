/- Canonical Goal 1, layer 13: residual bypass and faithful scalar-gate branch. -/
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

private def l13ZMrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5782],
    outs := [8625, 8629], params := [2] }
private def l13ZMrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10276],
    outs := [16198, 16202], params := [2] }
private def l13ZMrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10277],
    outs := [16206, 16210], params := [2] }

private theorem l13ZMrg_red_sm8629 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8629 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5782 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 617 l13ZMrgSmResidual
    5782 8629 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5782 8625 8629
    (by decide)

private theorem l13ZMrg_red_pm16202 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16202 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10276 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1355 l13ZMrgPmResidual0
    10276 16202 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 10276 16198 16202
    (by decide)

private theorem l13ZMrg_red_pm16210 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10277 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1356 l13ZMrgPmResidual1
    10277 16210 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 10277 16206 16210
    (by decide)

/-- The L13 residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the L13 attention residual transports to the exact residual
relation consumed by `l13_zigzag_moe_output_from_branch_inputs`. -/
theorem l13_zigzag_moe_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8629)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [l13ZMrg_red_sm8629 initSM, l13ZMrg_red_pm16202 initPM,
    l13ZMrg_red_pm16210 initPM]
  exact hAttention

private def l13ZMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5784],
    outs := [8636, 8640, 8644, 8648, 8652], params := [5] }
private def l13ZMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10280],
    outs := [15400, 14280, 14290, 14304, 14316], params := [5] }
private def l13ZMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10281],
    outs := [15402, 14281, 14291, 14305, 14317], params := [5] }
private def l13ZMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8644], outs := [5794],
    params := [4096, 1024] }
private def l13ZMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14290], outs := [10302],
    params := [2048, 1024] }
private def l13ZMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14291], outs := [10303],
    params := [2048, 1024] }
private def l13ZMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5794, 5795],
    outs := [5796] }
private def l13ZMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10302, 5795],
    outs := [10306] }
private def l13ZMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10303, 5795],
    outs := [10307] }
private def l13ZMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5796], outs := [5797],
    params := [4096, 1] }
private def l13ZMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10306], outs := [10308],
    params := [2048, 1] }
private def l13ZMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10307], outs := [10309],
    params := [2048, 1] }
private def l13ZMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5797], outs := [5798] }
private def l13ZMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [10308], outs := [10310] }
private def l13ZMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [10309], outs := [10311] }

private theorem l13ZMrg_red_sm8644 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8644 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5784 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 619 l13ZMrgSmRef
    5784 8644 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5784 [8636, 8640, 8644, 8648, 8652]
    5 rfl 8644 (by decide)

private theorem l13ZMrg_red_pm14290 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14290 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10280 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1359 l13ZMrgPmRef0
    10280 14290 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10280
    [15400, 14280, 14290, 14304, 14316] 5 rfl 14290 (by decide)

private theorem l13ZMrg_red_pm14291 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 14291 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10281 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1360 l13ZMrgPmRef1
    10281 14291 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10281
    [15402, 14281, 14291, 14305, 14317] 5 rfl 14291 (by decide)

private theorem l13ZMrg_red_sm5794 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5794 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8644) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 621 l13ZMrgSmReshape
    8644 5794 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8644 5794 [4096, 1024]

private theorem l13ZMrg_red_pm10302 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10302 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14290) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1361 l13ZMrgPmReshape0
    14290 10302 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14290 10302 [2048, 1024]

private theorem l13ZMrg_red_pm10303 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10303 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 14291) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1365 l13ZMrgPmReshape1
    14291 10303 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14291 10303 [2048, 1024]

private theorem l13ZMrg_red_sm5796 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5796 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5794)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5795) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 625 l13ZMrgSmLinear
    5794 5795 5796 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5794 5795 5796

private theorem l13ZMrg_red_pm10306 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10306 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10302)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5795) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1368 l13ZMrgPmLinear0
    10302 5795 10306 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10302 5795 10306

private theorem l13ZMrg_red_pm10307 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10307 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10303)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5795) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1373 l13ZMrgPmLinear1
    10303 5795 10307 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10303 5795 10307

private theorem l13ZMrg_red_sm5797 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5797 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5796) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 629 l13ZMrgSmView
    5796 5797 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5796 5797

private theorem l13ZMrg_red_pm10308 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10308 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10306) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1376 l13ZMrgPmView0
    10306 10308 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 10306 10308

private theorem l13ZMrg_red_pm10309 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10309 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 10307) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1381 l13ZMrgPmView1
    10307 10309 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 10307 10309

private theorem l13ZMrg_red_sm5798 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5798 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5797) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 633 l13ZMrgSmSigmoid
    5797 5798 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5797 5798

private theorem l13ZMrg_red_pm10310 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10310 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10308) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1384 l13ZMrgPmSigmoid0
    10308 10310 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 10308 10310

private theorem l13ZMrg_red_pm10311 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10311 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 10309) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1388 l13ZMrgPmSigmoid1
    10309 10311 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 10309 10311

private theorem l13ZMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5795 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5795 ∉ n.outs) := by
  native_decide

private theorem l13ZMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5795 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5795 := by
  have hi := (hInit initGoal_5795 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5795 pm_goal_1.numRanks _ rfl,
    show initGoal_5795.tps = [{rank := 0, tid := 5795}] from rfl,
    show initGoal_5795.ts = 5795 from rfl,
    show initGoal_5795.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5795
      (by native_decide) l13ZMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5795
      (by native_decide) l13ZMrg_weight_not_written.2]
  exact hi

private theorem l13ZMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5795).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5795 = initPM 5795 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5795
      (by native_decide) l13ZMrg_weight_not_written.2
  rw [e]
  exact hPM 5795 [1, 1024] (by native_decide)

/-- The canonical L13 scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem l13_zigzag_moe_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5784)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10280)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10281)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5798)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10310)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10311)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8644)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14291)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMrg_red_sm8644 initSM, l13ZMrg_red_pm14290 initPM,
      l13ZMrg_red_pm14291 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5794)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10302)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10303)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMrg_red_sm5794 initSM, l13ZMrg_red_pm10302 initPM,
      l13ZMrg_red_pm10303 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := l13ZMrg_weight_eq initSM initPM hInit
  have hwShape := l13ZMrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5796)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10306)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10307)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l13ZMrg_red_sm5796 initSM, l13ZMrg_red_pm10306 initPM,
      l13ZMrg_red_pm10307 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5797)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10308)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10309)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [l13ZMrg_red_sm5797 initSM, l13ZMrg_red_pm10308 initPM,
      l13ZMrg_red_pm10309 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5797)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10308)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10309)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [l13ZMrg_red_sm5798 initSM, l13ZMrg_red_pm10310 initPM,
    l13ZMrg_red_pm10311 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
