/- Canonical Goal 1: cache-boundary residual bypass and faithful scalar-gate branch. -/
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

private def cKVCrgSmResidual : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5562],
    outs := [8337, 8341], params := [2] }
private def cKVCrgPmResidual0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9632],
    outs := [15806, 15810], params := [2] }
private def cKVCrgPmResidual1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9633],
    outs := [15814, 15818], params := [2] }

private theorem cKVCrg_red_sm8341 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8341 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5562 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 445 cKVCrgSmResidual
    5562 8341 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmResidual
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 5562 8337 8341
    (by decide)

private theorem cKVCrg_red_pm15810 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15810 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9632 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 987 cKVCrgPmResidual0
    9632 15810 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmResidual0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 9632 15806 15810
    (by decide)

private theorem cKVCrg_red_pm15818 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15818 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9633 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 988 cKVCrgPmResidual1
    9633 15818 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmResidual1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 9633 15814 15818
    (by decide)

/-- The cache-boundary residual inputs are the second outputs of the generated multiref
nodes, hence a relation at the attention output transports to the exact residual
relation consumed by `canonical_kv_cache_boundary_from_branch_inputs`. -/
theorem canonical_kv_cache_residual_from_attention_output (initSM initPM : Store)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5562)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9633)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8341)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15810)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cKVCrg_red_sm8341 initSM, cKVCrg_red_pm15810 initPM,
    cKVCrg_red_pm15818 initPM]
  exact hAttention

private def cKVCrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564],
    outs := [8348, 8352, 8356, 8360, 8364], params := [5] }
private def cKVCrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636],
    outs := [15384, 13796, 13806, 13820, 13832], params := [5] }
private def cKVCrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637],
    outs := [15386, 13797, 13807, 13821, 13833], params := [5] }
private def cKVCrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8356], outs := [5574],
    params := [4096, 1024] }
private def cKVCrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13806], outs := [9658],
    params := [2048, 1024] }
private def cKVCrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13807], outs := [9659],
    params := [2048, 1024] }
private def cKVCrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5574, 5575],
    outs := [5576] }
private def cKVCrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9658, 5575],
    outs := [9662] }
private def cKVCrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9659, 5575],
    outs := [9663] }
private def cKVCrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5576], outs := [5577],
    params := [4096, 1] }
private def cKVCrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9662], outs := [9664],
    params := [2048, 1] }
private def cKVCrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9663], outs := [9665],
    params := [2048, 1] }
private def cKVCrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5577], outs := [5578] }
private def cKVCrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9664], outs := [9666] }
private def cKVCrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9665], outs := [9667] }

private theorem cKVCrg_red_sm8356 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8356 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 447 cKVCrgSmRef
    5564 8356 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364]
    5 rfl 8356 (by decide)

private theorem cKVCrg_red_pm13806 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13806 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 991 cKVCrgPmRef0
    9636 13806 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636
    [15384, 13796, 13806, 13820, 13832] 5 rfl 13806 (by decide)

private theorem cKVCrg_red_pm13807 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13807 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 992 cKVCrgPmRef1
    9637 13807 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637
    [15386, 13797, 13807, 13821, 13833] 5 rfl 13807 (by decide)

private theorem cKVCrg_red_sm5574 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5574 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8356) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 449 cKVCrgSmReshape
    8356 5574 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8356 5574 [4096, 1024]

private theorem cKVCrg_red_pm9658 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9658 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13806) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 993 cKVCrgPmReshape0
    13806 9658 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13806 9658 [2048, 1024]

private theorem cKVCrg_red_pm9659 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9659 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13807) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 997 cKVCrgPmReshape1
    13807 9659 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13807 9659 [2048, 1024]

private theorem cKVCrg_red_sm5576 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5576 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5574)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5575) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 453 cKVCrgSmLinear
    5574 5575 5576 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5574 5575 5576

private theorem cKVCrg_red_pm9662 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9662 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9658)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5575) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1000 cKVCrgPmLinear0
    9658 5575 9662 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9658 5575 9662

private theorem cKVCrg_red_pm9663 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9663 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9659)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5575) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1005 cKVCrgPmLinear1
    9659 5575 9663 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9659 5575 9663

private theorem cKVCrg_red_sm5577 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5577 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5576) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 457 cKVCrgSmView
    5576 5577 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5576 5577

private theorem cKVCrg_red_pm9664 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9664 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9662) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1008 cKVCrgPmView0
    9662 9664 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9662 9664

private theorem cKVCrg_red_pm9665 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9665 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9663) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1013 cKVCrgPmView1
    9663 9665 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9663 9665

private theorem cKVCrg_red_sm5578 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5578 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5577) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 461 cKVCrgSmSigmoid
    5577 5578 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5577 5578

private theorem cKVCrg_red_pm9666 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9666 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9664) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1016 cKVCrgPmSigmoid0
    9664 9666 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9664 9666

private theorem cKVCrg_red_pm9667 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9667 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9665) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1020 cKVCrgPmSigmoid1
    9665 9667 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9665 9667

private theorem cKVCrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5575 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5575 ∉ n.outs) := by
  native_decide

private theorem cKVCrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5575 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5575 := by
  have hi := (hInit initGoal_5575 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5575 pm_goal_1.numRanks _ rfl,
    show initGoal_5575.tps = [{rank := 0, tid := 5575}] from rfl,
    show initGoal_5575.ts = 5575 from rfl,
    show initGoal_5575.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5575
      (by native_decide) cKVCrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5575
      (by native_decide) cKVCrg_weight_not_written.2]
  exact hi

private theorem cKVCrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5575).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5575 = initPM 5575 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5575
      (by native_decide) cKVCrg_weight_not_written.2
  rw [e]
  exact hPM 5575 [1, 1024] (by native_decide)

/-- The canonical cache-boundary scalar gate is derived through the real multiref,
reshape, linear, view, and sigmoid nodes. The shared weight equality and shape
are derived internally from `hInit` and `hPM`; no computed gate relation is a
caller premise. -/
theorem canonical_kv_cache_gate_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9637)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5578)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9667)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
  have hSource : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8356)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13807)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCrg_red_sm8356 initSM, cKVCrg_red_pm13806 initPM,
      cKVCrg_red_pm13807 initPM]
    exact hNorm
  have hReshape : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5574)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9658)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9659)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCrg_red_sm5574 initSM, cKVCrg_red_pm9658 initPM,
      cKVCrg_red_pm9659 initPM]
    exact Zigzag2Rel.view_id' hSource
  have hwEq := cKVCrg_weight_eq initSM initPM hInit
  have hwShape := cKVCrg_weight_shape initPM hPM
  have hLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5576)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9662)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9663)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [cKVCrg_red_sm5576 initSM, cKVCrg_red_pm9662 initPM,
      cKVCrg_red_pm9663 initPM, hwEq]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hReshape hwShape
      (by decide) (by decide) (by decide)
  have hView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5577)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9665)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1] [2048, 1] := by
    rw [cKVCrg_red_sm5577 initSM, cKVCrg_red_pm9664 initPM,
      cKVCrg_red_pm9665 initPM]
    exact Zigzag2Rel.view_id' hLinear
  obtain ⟨source0, source1, hs⟩ := hView
  have hView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5577)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9665)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1] [2048, 1] := ⟨source0, source1, hs⟩
  rw [cKVCrg_red_sm5578 initSM, cKVCrg_red_pm9666 initPM,
    cKVCrg_red_pm9667 initPM]
  exact Zigzag2Rel.sigmoid 2048 1 hView' (by decide) (by decide)

#print axioms canonical_kv_cache_residual_from_attention_output
#print axioms canonical_kv_cache_gate_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
