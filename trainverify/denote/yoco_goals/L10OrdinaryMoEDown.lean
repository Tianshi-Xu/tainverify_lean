/- Canonical Goal 1 cache-source layer: ordinary SwiGLU/down-projection branch. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.FaithfulStackGather
import denote.yoco_goals.ZigzagLayoutRel
import denote.yoco_goals.ZigzagLinearRel
import denote.yoco_goals.ZigzagPointwiseRel
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

private def l10OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5509], outs := [8296, 8300, 8304, 8308, 8312], params := [5] }

private def l10OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9472], outs := [15376, 13670, 13680, 13694, 13706], params := [5] }

private def l10OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9473], outs := [15378, 13671, 13681, 13695, 13707], params := [5] }

private def l10OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8308], outs := [5524], params := [4096, 1024] }

private def l10OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8312], outs := [5528], params := [4096, 1024] }

private def l10OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13694], outs := [9504], params := [2048, 1024] }

private def l10OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13695], outs := [9505], params := [2048, 1024] }

private def l10OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13706], outs := [9516], params := [2048, 1024] }

private def l10OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13707], outs := [9517], params := [2048, 1024] }

private def l10OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5524, 5525], outs := [5526] }

private def l10OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5528, 5529], outs := [5530] }

private def l10OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9504, 5525], outs := [9508] }

private def l10OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9505, 5525], outs := [9509] }

private def l10OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9516, 5529], outs := [9520] }

private def l10OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9517, 5529], outs := [9521] }

private def l10OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5526], outs := [5527], params := [4096, 512] }

private def l10OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5530], outs := [5531], params := [4096, 512] }

private def l10OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9508], outs := [9510], params := [2048, 512] }

private def l10OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9509], outs := [9511], params := [2048, 512] }

private def l10OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9520], outs := [9522], params := [2048, 512] }

private def l10OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9521], outs := [9523], params := [2048, 512] }

private def l10OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5527, 5531], outs := [5532] }

private def l10OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9510, 9522], outs := [9528] }

private def l10OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9511, 9523], outs := [9529] }

private def l10OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5532], outs := [5533], params := [4096, 512] }

private def l10OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9528], outs := [9530], params := [2048, 512] }

private def l10OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9529], outs := [9531], params := [2048, 512] }

private def l10OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5533, 5534], outs := [5535] }

private def l10OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9530, 5534], outs := [9536] }

private def l10OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9531, 5534], outs := [9537] }

private def l10OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5535], outs := [5536], params := [4096, 1024] }

private def l10OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9536], outs := [9538], params := [2048, 1024] }

private def l10OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9537], outs := [9539], params := [2048, 1024] }

private theorem l10OMOd_red_sm13694 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8308 =
      denoteGraphDistributedFaithful sm_goal_1 init 5509 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 408 l10OMOdSmRef
    5509 8308 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5509 [8296, 8300, 8304, 8308, 8312] 5 rfl 8308 (by decide)

private theorem l10OMOd_red_sm13706 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8312 =
      denoteGraphDistributedFaithful sm_goal_1 init 5509 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 408 l10OMOdSmRef
    5509 8312 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5509 [8296, 8300, 8304, 8308, 8312] 5 rfl 8312 (by decide)

private theorem l10OMOd_red_pm13694 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13694 =
      denoteGraphDistributedFaithful pm_goal_1 init 9472 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 907 l10OMOdPmRef0
    9472 13694 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9472 [15376, 13670, 13680, 13694, 13706] 5 rfl 13694 (by decide)

private theorem l10OMOd_red_pm13706 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13706 =
      denoteGraphDistributedFaithful pm_goal_1 init 9472 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 907 l10OMOdPmRef0
    9472 13706 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9472 [15376, 13670, 13680, 13694, 13706] 5 rfl 13706 (by decide)

private theorem l10OMOd_red_pm13695 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13695 =
      denoteGraphDistributedFaithful pm_goal_1 init 9473 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 908 l10OMOdPmRef1
    9473 13695 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9473 [15378, 13671, 13681, 13695, 13707] 5 rfl 13695 (by decide)

private theorem l10OMOd_red_pm13707 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13707 =
      denoteGraphDistributedFaithful pm_goal_1 init 9473 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 908 l10OMOdPmRef1
    9473 13707 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9473 [15378, 13671, 13681, 13695, 13707] 5 rfl 13707 (by decide)

private theorem l10OMOd_red_sm5524 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5524 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8308) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 411 l10OMOdSmReshapeA
    8308 5524 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8308 5524 [4096, 1024]

private theorem l10OMOd_red_sm5528 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5528 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8312) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 412 l10OMOdSmReshapeB
    8312 5528 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8312 5528 [4096, 1024]

private theorem l10OMOd_red_pm9504 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9504 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13694) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 910 l10OMOdPmReshapeA0
    13694 9504 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13694 9504 [2048, 1024]

private theorem l10OMOd_red_pm9505 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9505 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13695) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 914 l10OMOdPmReshapeA1
    13695 9505 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13695 9505 [2048, 1024]

private theorem l10OMOd_red_pm9516 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9516 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13706) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 911 l10OMOdPmReshapeB0
    13706 9516 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13706 9516 [2048, 1024]

private theorem l10OMOd_red_pm9517 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9517 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13707) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 915 l10OMOdPmReshapeB1
    13707 9517 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13707 9517 [2048, 1024]

private theorem l10OMOd_red_sm5527 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5527 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5526) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 419 l10OMOdSmViewA
    5526 5527 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5526 5527

private theorem l10OMOd_red_sm5531 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5531 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5530) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 420 l10OMOdSmViewB
    5530 5531 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5530 5531

private theorem l10OMOd_red_pm9510 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9510 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9508) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 925 l10OMOdPmViewA0
    9508 9510 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9508 9510

private theorem l10OMOd_red_pm9511 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9511 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9509) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 930 l10OMOdPmViewA1
    9509 9511 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9509 9511

private theorem l10OMOd_red_pm9522 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9522 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9520) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 926 l10OMOdPmViewB0
    9520 9522 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9520 9522

private theorem l10OMOd_red_pm9523 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9523 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9521) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 931 l10OMOdPmViewB1
    9521 9523 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9521 9523

private theorem l10OMOd_red_sm5533 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5533 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5532) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 424 l10OMOdSmReshapeDown
    5532 5533 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5532 5533 [4096, 512]

private theorem l10OMOd_red_pm9530 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9530 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9528) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 938 l10OMOdPmReshapeDown0
    9528 9530 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9528 9530 [2048, 512]

private theorem l10OMOd_red_pm9531 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9531 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9529) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 941 l10OMOdPmReshapeDown1
    9529 9531 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9529 9531 [2048, 512]

private theorem l10OMOd_red_sm5536 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5536 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5535) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 426 l10OMOdSmViewDown
    5535 5536 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5535 5536

private theorem l10OMOd_red_pm9538 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9538 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9536) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 946 l10OMOdPmViewDown0
    9536 9538 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9536 9538

private theorem l10OMOd_red_pm9539 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9539 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9537) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 947 l10OMOdPmViewDown1
    9537 9539 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9537 9539

private theorem l10OMOd_red_sm5526 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5526 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5524)
        (denoteGraphDistributedFaithful sm_goal_1 init 5525) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 415 l10OMOdSmLinearA
    5524 5525 5526 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5524 5525 5526

private theorem l10OMOd_red_sm5530 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5530 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5528)
        (denoteGraphDistributedFaithful sm_goal_1 init 5529) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 416 l10OMOdSmLinearB
    5528 5529 5530 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5528 5529 5530

private theorem l10OMOd_red_pm9508 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9508 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9504)
        (denoteGraphDistributedFaithful pm_goal_1 init 5525) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 917 l10OMOdPmLinearA0
    9504 5525 9508 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9504 5525 9508

private theorem l10OMOd_red_pm9509 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9509 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9505)
        (denoteGraphDistributedFaithful pm_goal_1 init 5525) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 922 l10OMOdPmLinearA1
    9505 5525 9509 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9505 5525 9509

private theorem l10OMOd_red_pm9520 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9520 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9516)
        (denoteGraphDistributedFaithful pm_goal_1 init 5529) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 918 l10OMOdPmLinearB0
    9516 5529 9520 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9516 5529 9520

private theorem l10OMOd_red_pm9521 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9521 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9517)
        (denoteGraphDistributedFaithful pm_goal_1 init 5529) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 923 l10OMOdPmLinearB1
    9517 5529 9521 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9517 5529 9521

private theorem l10OMOd_red_sm5532 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5532 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5527)
        (denoteGraphDistributedFaithful sm_goal_1 init 5531) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 423 l10OMOdSmSwi
    5527 5531 5532 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5527 5531 5532

private theorem l10OMOd_red_pm9528 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9528 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9510)
        (denoteGraphDistributedFaithful pm_goal_1 init 9522) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 933 l10OMOdPmSwi0
    9510 9522 9528 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9510 9522 9528

private theorem l10OMOd_red_pm9529 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9529 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9511)
        (denoteGraphDistributedFaithful pm_goal_1 init 9523) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 937 l10OMOdPmSwi1
    9511 9523 9529 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9511 9523 9529

private theorem l10OMOd_red_sm5535 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5535 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5533)
        (denoteGraphDistributedFaithful sm_goal_1 init 5534) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 425 l10OMOdSmLinearDown
    5533 5534 5535 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5533 5534 5535

private theorem l10OMOd_red_pm9536 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9536 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9530)
        (denoteGraphDistributedFaithful pm_goal_1 init 5534) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 942 l10OMOdPmLinearDown0
    9530 5534 9536 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9530 5534 9536

private theorem l10OMOd_red_pm9537 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9537 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9531)
        (denoteGraphDistributedFaithful pm_goal_1 init 5534) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 945 l10OMOdPmLinearDown1
    9531 5534 9537 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9531 5534 9537

private theorem l10OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l10OMOd_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ goal_1_full_initGoals) (W : Tid)
    (htp : gW.tps = [{rank := 0, tid := W}])
    (hts : gW.ts = W) (hgd : gW.gatherDim = 0) (hrep : gW.replicated = false)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM W =
      denoteGraphDistributedFaithful pm_goal_1 initPM W := by
  have hi := (hInit gW hgW).2.2
  rw [reconstructForGoal_of_not_replicated gW pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hi
  simp only [List.map, reconstructWithDim] at hi
  rw [l10OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l10OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l10OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l10OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv



private theorem ordinary_view
    {full rank0 rank1 : Tensor} {fullShape shardShape : Shape}
    (h : Ordinary2Rel full rank0 rank1 fullShape shardShape) :
    Ordinary2Rel (fw_view fullShape full) (fw_view shardShape rank0)
      (fw_view shardShape rank1) fullShape shardShape := by
  rw [fw_view_id full fullShape h.full_shape,
    fw_view_id rank0 shardShape h.rank0_shape,
    fw_view_id rank1 shardShape h.rank1_shape]
  exact h

private theorem ordinary_linear
    {full rank0 rank1 w : Tensor} (lDim inDim outDim : Nat)
    (h : Ordinary2Rel full rank0 rank1 [lDim * 2, inDim] [lDim, inDim])
    (hw : w.shape = [outDim, inDim])
    (hl : 0 < lDim) (hin : 0 < inDim) (hout : 0 < outDim) :
    Ordinary2Rel (fw_linear full w) (fw_linear rank0 w) (fw_linear rank1 w)
      [lDim * 2, outDim] [lDim, outDim] := by
  refine {
    full_value := ?_
    full_shape := fw_linear_shape_2d' (lDim * 2) inDim outDim full w h.full_shape hw
    rank0_shape := fw_linear_shape_2d' lDim inDim outDim rank0 w h.rank0_shape hw
    rank1_shape := fw_linear_shape_2d' lDim inDim outDim rank1 w h.rank1_shape hw
  }
  rw [h.full_value]
  exact fw_mix_precision_linear_allGather0_commute_2 rank0 rank1 w
    lDim inDim outDim hl hin hout h.rank0_shape h.rank1_shape hw

/-- fw_swiglu commutes with dim-0 sharding. -/
private theorem l10OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (ha : a.shape = [shard, hidden]) (hb : b.shape = [shard, hidden])
    (hc : c.shape = [shard, hidden]) (hd : d.shape = [shard, hidden]) :
    fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])
      = allGatherPrimDimN 0 2 0 [fw_swiglu a c, fw_swiglu b d] := by
  have hhead_ab : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [ha]
  have hhead_cd : (([c, d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by simp [hc]
  have hG_ab : (allGatherPrimDimN 0 2 0 [a, b]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_ab]; simp [List.set, List.getD]
  have hG_cd : (allGatherPrimDimN 0 2 0 [c, d]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_cd]; simp [List.set, List.getD]
  have hswig_shape : ∀ (g u : Tensor), u.shape = [shard, hidden] → (fw_swiglu g u).shape = [shard, hidden] := by
    intro g u hu; unfold fw_swiglu Tensor.mkShape; simp; exact hu
  have hswig_ac : (fw_swiglu a c).shape = [shard, hidden] := hswig_shape a c hc
  have hswig_bd : (fw_swiglu b d).shape = [shard, hidden] := hswig_shape b d hd
  have hhead_swig : (([fw_swiglu a c, fw_swiglu b d] : List Tensor).head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hswig_ac]
  have hRHS_shape : (allGatherPrimDimN 0 2 0 [fw_swiglu a c, fw_swiglu b d]).shape = [shard * 2, hidden] := by
    rw [allGatherPrimDimN_shape 0 2 _ [shard, hidden] hhead_swig]; simp [List.set, List.getD]
  apply Tensor.ext
  · have hLHS_shape : (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [shard * 2, hidden] := by
      unfold fw_swiglu Tensor.mkShape; simp; exact hG_cd
    rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    have hLHS_shape : (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])).shape = [shard * 2, hidden] := by
      unfold fw_swiglu Tensor.mkShape; simp; exact hG_cd
    rw [hLHS_shape] at hidx
    have hidx_bound : idx < shard * 2 * hidden := by simpa [prodShape] using hidx
    set row := idx / hidden with hrow_def
    set j := idx % hidden with hj_def
    have hj_lt : j < hidden := by rw [hj_def]; exact Nat.mod_lt _ hhid
    have hrow_lt : row < 2 * shard := by
      rw [hrow_def]; exact Nat.div_lt_iff_lt_mul hhid |>.mpr (by linarith [hidx_bound])
    set r := row / shard with hr_def
    set i := row % shard with hi_def
    have hi_lt : i < shard := by rw [hi_def]; exact Nat.mod_lt _ hshard
    have hr_lt : r < 2 := by
      rw [hr_def]; exact Nat.div_lt_iff_lt_mul hshard |>.mpr (by linarith [hrow_lt])
    have hidx_eq : idx = (r * shard + i) * hidden + j := by
      rw [hr_def, hi_def, hj_def, hrow_def]
      have h1 : row = shard * (row / shard) + row % shard := (Nat.div_add_mod row shard).symm
      have h2 : idx = hidden * (idx / hidden) + idx % hidden := (Nat.div_add_mod idx hidden).symm
      calc idx = hidden * (idx / hidden) + idx % hidden := h2
        _ = row * hidden + j := by rw [← hrow_def, ← hj_def]; ring
        _ = (shard * (row / shard) + row % shard) * hidden + j := by rw [← h1]
        _ = (row / shard * shard + row % shard) * hidden + j := by ring
    -- LHS at idx = silu(gather_ab[idx]) * gather_cd[idx]
    have hLHS_val : valAt (fw_swiglu (allGatherPrimDimN 0 2 0 [a, b]) (allGatherPrimDimN 0 2 0 [c, d])) idx
        = siluScalar (valAt (allGatherPrimDimN 0 2 0 [a, b]) idx) * valAt (allGatherPrimDimN 0 2 0 [c, d]) idx := by
      unfold fw_swiglu Tensor.mkShape valAt
      simp [hG_cd, prodShape]
      simp [hidx_bound]
    rw [hLHS_val]
    have hshapes_ab : ∀ r' (_ : r' < 2),
        (([a, b].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, ha, hb]
    have hshapes_cd : ∀ r' (_ : r' < 2),
        (([c, d].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hc, hd]
    have hshapes_swig : ∀ r' (_ : r' < 2),
        (([fw_swiglu a c, fw_swiglu b d].getD r' (zeroTensor [shard, hidden]))).shape = [shard, hidden] := by
      intro r' hr'; have : r' = 0 ∨ r' = 1 := by omega
      rcases this with h | h <;> rw [h] <;> simp [List.getD, hswig_ac, hswig_bd]
    rw [hidx_eq]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [a, b] (by omega) hshard hhid hhead_ab hshapes_ab
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [c, d] (by omega) hshard hhid hhead_cd hshapes_cd
          r hr_lt i hi_lt j hj_lt]
    rw [allGatherPrimDimN0_valAt 2 shard hidden [fw_swiglu a c, fw_swiglu b d]
          (by omega) hshard hhid hhead_swig hshapes_swig r hr_lt i hi_lt j hj_lt]
    have hr_lt' : r = 0 ∨ r = 1 := by
      interval_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hgetD_swig : [fw_swiglu a c, fw_swiglu b d].getD r (zeroTensor [shard, hidden]) =
        fw_swiglu ([a, b].getD r (zeroTensor [shard, hidden])) ([c, d].getD r (zeroTensor [shard, hidden])) := by
      rcases hr_lt' with h | h <;> rw [h] <;> simp [List.getD]
    rw [hgetD_swig]
    set g := [a, b].getD r (zeroTensor [shard, hidden]) with hg_def
    set u := [c, d].getD r (zeroTensor [shard, hidden]) with hu_def
    have hg_shape : g.shape = [shard, hidden] := hshapes_ab r hr_lt
    have hu_shape : u.shape = [shard, hidden] := hshapes_cd r hr_lt
    have hloc_bound : i * hidden + j < shard * hidden := by
      have h1 : i * hidden + j < i * hidden + hidden := by omega
      have h2 : i * hidden + hidden = (i + 1) * hidden := by ring
      have h3 : (i + 1) * hidden ≤ shard * hidden := Nat.mul_le_mul_right _ (by omega)
      omega
    unfold fw_swiglu Tensor.mkShape valAt
    simp [hu_shape, hg_shape, prodShape, hloc_bound]


private theorem ordinary_swiglu
    {fullA rankA0 rankA1 fullB rankB0 rankB1 : Tensor} (lDim hidden : Nat)
    (hA : Ordinary2Rel fullA rankA0 rankA1 [lDim * 2, hidden] [lDim, hidden])
    (hB : Ordinary2Rel fullB rankB0 rankB1 [lDim * 2, hidden] [lDim, hidden])
    (hl : 0 < lDim) (hh : 0 < hidden) :
    Ordinary2Rel (fw_swiglu fullA fullB) (fw_swiglu rankA0 rankB0)
      (fw_swiglu rankA1 rankB1) [lDim * 2, hidden] [lDim, hidden] := by
  refine {
    full_value := ?_
    full_shape := by unfold fw_swiglu Tensor.mkShape; simp; exact hB.full_shape
    rank0_shape := by unfold fw_swiglu Tensor.mkShape; simp; exact hB.rank0_shape
    rank1_shape := by unfold fw_swiglu Tensor.mkShape; simp; exact hB.rank1_shape
  }
  rw [hA.full_value, hB.full_value]
  exact l10OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5536 ↔ 9538/9539` ordinary relation. -/
theorem l10_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5532)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9528)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9529)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9538)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9539)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5533)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9530)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9531)
      [4096, 512] [2048, 512] := by
    rw [l10OMOd_red_sm5533 initSM, l10OMOd_red_pm9530 initPM, l10OMOd_red_pm9531 initPM]
    exact ordinary_view hSwi
  have hwD := l10OMOd_weight_eq initSM initPM hInit initGoal_5534 (by native_decide)
    5534 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l10OMOd_weight_shape initPM hPM 5534 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5535)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9537)
      [4096, 1024] [2048, 1024] := by
    rw [l10OMOd_red_sm5535 initSM, l10OMOd_red_pm9536 initPM,
      l10OMOd_red_pm9537 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l10OMOd_red_sm5536 initSM, l10OMOd_red_pm9538 initPM, l10OMOd_red_pm9539 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l10_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5509)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9472)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9473)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9538)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9539)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5524)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9504)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9505)
      [4096, 1024] [2048, 1024] := by
    rw [l10OMOd_red_sm5524 initSM, l10OMOd_red_pm9504 initPM,
      l10OMOd_red_pm9505 initPM, l10OMOd_red_sm13694 initSM,
      l10OMOd_red_pm13694 initPM, l10OMOd_red_pm13695 initPM]
    exact ordinary_view hNorm
  have hwA := l10OMOd_weight_eq initSM initPM hInit initGoal_5525 (by native_decide)
    5525 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l10OMOd_weight_shape initPM hPM 5525 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5526)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9508)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9509)
      [4096, 512] [2048, 512] := by
    rw [l10OMOd_red_sm5526 initSM, l10OMOd_red_pm9508 initPM,
      l10OMOd_red_pm9509 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5527)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9510)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9511)
      [4096, 512] [2048, 512] := by
    rw [l10OMOd_red_sm5527 initSM, l10OMOd_red_pm9510 initPM,
      l10OMOd_red_pm9511 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5528)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9516)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9517)
      [4096, 1024] [2048, 1024] := by
    rw [l10OMOd_red_sm5528 initSM, l10OMOd_red_pm9516 initPM,
      l10OMOd_red_pm9517 initPM, l10OMOd_red_sm13706 initSM,
      l10OMOd_red_pm13706 initPM, l10OMOd_red_pm13707 initPM]
    exact ordinary_view hNorm
  have hwB := l10OMOd_weight_eq initSM initPM hInit initGoal_5529 (by native_decide)
    5529 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l10OMOd_weight_shape initPM hPM 5529 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5530)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9520)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9521)
      [4096, 512] [2048, 512] := by
    rw [l10OMOd_red_sm5530 initSM, l10OMOd_red_pm9520 initPM,
      l10OMOd_red_pm9521 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5531)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9522)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9523)
      [4096, 512] [2048, 512] := by
    rw [l10OMOd_red_sm5531 initSM, l10OMOd_red_pm9522 initPM,
      l10OMOd_red_pm9523 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5532)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9528)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9529)
      [4096, 512] [2048, 512] := by
    rw [l10OMOd_red_sm5532 initSM, l10OMOd_red_pm9528 initPM,
      l10OMOd_red_pm9529 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l10_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l10_ordinary_moe_down_from_swiglu
#print axioms l10_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
