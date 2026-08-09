/- Canonical Goal 1, layer 16: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L16ZigzagMoEResidualGate

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

private def l16ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5946], outs := [8753, 8757, 8761, 8765, 8769], params := [5] }

private def l16ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10742], outs := [15412, 14628, 14638, 14652, 14664], params := [5] }

private def l16ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10743], outs := [15414, 14629, 14639, 14653, 14665], params := [5] }

private def l16ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8765], outs := [5961], params := [4096, 1024] }

private def l16ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8769], outs := [5965], params := [4096, 1024] }

private def l16ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14652], outs := [10774], params := [2048, 1024] }

private def l16ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14653], outs := [10775], params := [2048, 1024] }

private def l16ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14664], outs := [10786], params := [2048, 1024] }

private def l16ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14665], outs := [10787], params := [2048, 1024] }

private def l16ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5961, 5962], outs := [5963] }

private def l16ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5965, 5966], outs := [5967] }

private def l16ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10774, 5962], outs := [10778] }

private def l16ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10775, 5962], outs := [10779] }

private def l16ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10786, 5966], outs := [10790] }

private def l16ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10787, 5966], outs := [10791] }

private def l16ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5963], outs := [5964], params := [4096, 512] }

private def l16ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5967], outs := [5968], params := [4096, 512] }

private def l16ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10778], outs := [10780], params := [2048, 512] }

private def l16ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10779], outs := [10781], params := [2048, 512] }

private def l16ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10790], outs := [10792], params := [2048, 512] }

private def l16ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10791], outs := [10793], params := [2048, 512] }

private def l16ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5964, 5968], outs := [5969] }

private def l16ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10780, 10792], outs := [10798] }

private def l16ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10781, 10793], outs := [10799] }

private def l16ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5969], outs := [5970], params := [4096, 512] }

private def l16ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10798], outs := [10800], params := [2048, 512] }

private def l16ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10799], outs := [10801], params := [2048, 512] }

private def l16ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5970, 5971], outs := [5972] }

private def l16ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10800, 5971], outs := [10806] }

private def l16ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10801, 5971], outs := [10807] }

private def l16ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5972], outs := [5973], params := [4096, 1024] }

private def l16ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10806], outs := [10808], params := [2048, 1024] }

private def l16ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10807], outs := [10809], params := [2048, 1024] }

private theorem l16ZMd_red_sm8765 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8765 =
      denoteGraphDistributedFaithful sm_goal_1 init 5946 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 724 l16ZMdSmRef
    5946 8765 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5946 [8948, 8952, 8956, 8765, 8769] 5 rfl 8765 (by decide)

private theorem l16ZMd_red_sm8769 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8769 =
      denoteGraphDistributedFaithful sm_goal_1 init 5946 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 724 l16ZMdSmRef
    5946 8769 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5946 [8948, 8952, 8956, 8765, 8769] 5 rfl 8769 (by decide)

private theorem l16ZMd_red_pm14652 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14652 =
      denoteGraphDistributedFaithful pm_goal_1 init 10742 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1587 l16ZMdPmRef0
    10742 14652 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10742 [15412, 14628, 14638, 14652, 14664] 5 rfl 14652 (by decide)

private theorem l16ZMd_red_pm14664 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14664 =
      denoteGraphDistributedFaithful pm_goal_1 init 10742 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1587 l16ZMdPmRef0
    10742 14664 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10742 [15412, 14628, 14638, 14652, 14664] 5 rfl 14664 (by decide)

private theorem l16ZMd_red_pm14653 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14653 =
      denoteGraphDistributedFaithful pm_goal_1 init 10743 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1588 l16ZMdPmRef1
    10743 14653 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10743 [15414, 14629, 14639, 14653, 14665] 5 rfl 14653 (by decide)

private theorem l16ZMd_red_pm14665 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14665 =
      denoteGraphDistributedFaithful pm_goal_1 init 10743 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1588 l16ZMdPmRef1
    10743 14665 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10743 [15414, 14629, 14639, 14653, 14665] 5 rfl 14665 (by decide)

private theorem l16ZMd_red_sm5961 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5961 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8765) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 727 l16ZMdSmReshapeA
    8765 5961 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8765 5961 [4096, 1024]

private theorem l16ZMd_red_sm5965 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5965 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8769) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 728 l16ZMdSmReshapeB
    8769 5965 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8769 5965 [4096, 1024]

private theorem l16ZMd_red_pm10774 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10774 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14652) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1590 l16ZMdPmReshapeA0
    14652 10774 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14652 10774 [2048, 1024]

private theorem l16ZMd_red_pm10775 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10775 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14653) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1594 l16ZMdPmReshapeA1
    14653 10775 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14653 10775 [2048, 1024]

private theorem l16ZMd_red_pm10786 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10786 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14664) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1591 l16ZMdPmReshapeB0
    14664 10786 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14664 10786 [2048, 1024]

private theorem l16ZMd_red_pm10787 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10787 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14665) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1595 l16ZMdPmReshapeB1
    14665 10787 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14665 10787 [2048, 1024]

private theorem l16ZMd_red_sm5964 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5964 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5963) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 735 l16ZMdSmViewA
    5963 5964 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5963 5964

private theorem l16ZMd_red_sm5968 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5968 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5967) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 736 l16ZMdSmViewB
    5967 5968 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5967 5968

private theorem l16ZMd_red_pm10780 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10780 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10778) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1605 l16ZMdPmViewA0
    10778 10780 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10778 10780

private theorem l16ZMd_red_pm10781 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10781 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10779) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1610 l16ZMdPmViewA1
    10779 10781 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10779 10781

private theorem l16ZMd_red_pm10792 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10792 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10790) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1606 l16ZMdPmViewB0
    10790 10792 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10790 10792

private theorem l16ZMd_red_pm10793 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10793 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10791) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1611 l16ZMdPmViewB1
    10791 10793 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10791 10793

private theorem l16ZMd_red_sm5970 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5970 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5969) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 740 l16ZMdSmReshapeDown
    5969 5970 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5969 5970 [4096, 512]

private theorem l16ZMd_red_pm10800 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10800 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10798) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1618 l16ZMdPmReshapeDown0
    10798 10800 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10798 10800 [2048, 512]

private theorem l16ZMd_red_pm10801 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10801 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10799) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1621 l16ZMdPmReshapeDown1
    10799 10801 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10799 10801 [2048, 512]

private theorem l16ZMd_red_sm5973 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5973 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5972) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 742 l16ZMdSmViewDown
    5972 5973 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5972 5973

private theorem l16ZMd_red_pm10808 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10808 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10806) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1626 l16ZMdPmViewDown0
    10806 10808 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10806 10808

private theorem l16ZMd_red_pm10809 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10809 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10807) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1627 l16ZMdPmViewDown1
    10807 10809 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10807 10809

private theorem l16ZMd_red_sm5963 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5963 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5961)
        (denoteGraphDistributedFaithful sm_goal_1 init 5962) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 731 l16ZMdSmLinearA
    5961 5962 5963 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5961 5962 5963

private theorem l16ZMd_red_sm5967 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5967 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5965)
        (denoteGraphDistributedFaithful sm_goal_1 init 5966) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 732 l16ZMdSmLinearB
    5965 5966 5967 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5965 5966 5967

private theorem l16ZMd_red_pm10778 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10778 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10774)
        (denoteGraphDistributedFaithful pm_goal_1 init 5962) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1597 l16ZMdPmLinearA0
    10774 5962 10778 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10774 5962 10778

private theorem l16ZMd_red_pm10779 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10779 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10775)
        (denoteGraphDistributedFaithful pm_goal_1 init 5962) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1602 l16ZMdPmLinearA1
    10775 5962 10779 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10775 5962 10779

private theorem l16ZMd_red_pm10790 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10790 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10786)
        (denoteGraphDistributedFaithful pm_goal_1 init 5966) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1598 l16ZMdPmLinearB0
    10786 5966 10790 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10786 5966 10790

private theorem l16ZMd_red_pm10791 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10791 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10787)
        (denoteGraphDistributedFaithful pm_goal_1 init 5966) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1603 l16ZMdPmLinearB1
    10787 5966 10791 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10787 5966 10791

private theorem l16ZMd_red_sm5969 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5969 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5964)
        (denoteGraphDistributedFaithful sm_goal_1 init 5968) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 739 l16ZMdSmSwi
    5964 5968 5969 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5964 5968 5969

private theorem l16ZMd_red_pm10798 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10798 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10780)
        (denoteGraphDistributedFaithful pm_goal_1 init 10792) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1613 l16ZMdPmSwi0
    10780 10792 10798 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 10780 10792 10798

private theorem l16ZMd_red_pm10799 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10799 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10781)
        (denoteGraphDistributedFaithful pm_goal_1 init 10793) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1617 l16ZMdPmSwi1
    10781 10793 10799 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 10781 10793 10799

private theorem l16ZMd_red_sm5972 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5972 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5970)
        (denoteGraphDistributedFaithful sm_goal_1 init 5971) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 741 l16ZMdSmLinearDown
    5970 5971 5972 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5970 5971 5972

private theorem l16ZMd_red_pm10806 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10806 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10800)
        (denoteGraphDistributedFaithful pm_goal_1 init 5971) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1622 l16ZMdPmLinearDown0
    10800 5971 10806 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10800 5971 10806

private theorem l16ZMd_red_pm10807 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10807 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10801)
        (denoteGraphDistributedFaithful pm_goal_1 init 5971) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1625 l16ZMdPmLinearDown1
    10801 5971 10807 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10801 5971 10807

private theorem l16ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l16ZMd_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid)
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
  rw [l16ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l16ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l16ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l16ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L16 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l16_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10808)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10809)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8765)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMd_red_sm8765 initSM, l16ZMd_red_pm14652 initPM, l16ZMd_red_pm14653 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8769)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14664)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14665)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMd_red_sm8769 initSM, l16ZMd_red_pm14664 initPM, l16ZMd_red_pm14665 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5961)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10774)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10775)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMd_red_sm5961 initSM, l16ZMd_red_pm10774 initPM, l16ZMd_red_pm10775 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5965)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10786)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10787)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMd_red_sm5965 initSM, l16ZMd_red_pm10786 initPM, l16ZMd_red_pm10787 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l16ZMd_weight_eq initSM initPM hInit initGoal_5962 (by native_decide)
    5962 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l16ZMd_weight_eq initSM initPM hInit initGoal_5966 (by native_decide)
    5966 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l16ZMd_weight_shape initPM hPM 5962 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l16ZMd_weight_shape initPM hPM 5966 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5963)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10778)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10779)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l16ZMd_red_sm5963 initSM, l16ZMd_red_pm10778 initPM,
      l16ZMd_red_pm10779 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5967)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10790)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10791)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l16ZMd_red_sm5967 initSM, l16ZMd_red_pm10790 initPM,
      l16ZMd_red_pm10791 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5964)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10780)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10781)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l16ZMd_red_sm5964 initSM, l16ZMd_red_pm10780 initPM, l16ZMd_red_pm10781 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10792)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10793)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l16ZMd_red_sm5968 initSM, l16ZMd_red_pm10792 initPM, l16ZMd_red_pm10793 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5964)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10780)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10781)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10792)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10793)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10798)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10799)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l16ZMd_red_sm5969 initSM, l16ZMd_red_pm10798 initPM, l16ZMd_red_pm10799 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5970)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10800)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10801)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l16ZMd_red_sm5970 initSM, l16ZMd_red_pm10800 initPM, l16ZMd_red_pm10801 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l16ZMd_weight_eq initSM initPM hInit initGoal_5971 (by native_decide)
    5971 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l16ZMd_weight_shape initPM hPM 5971 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10807)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l16ZMd_red_sm5972 initSM, l16ZMd_red_pm10806 initPM,
      l16ZMd_red_pm10807 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l16ZMd_red_sm5973 initSM, l16ZMd_red_pm10808 initPM, l16ZMd_red_pm10809 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
