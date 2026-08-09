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

private def l12OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622], outs := [8519, 8523, 8527, 8531, 8535], params := [5] }

private def l12OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818], outs := [15388, 13932, 13942, 13956, 13968], params := [5] }

private def l12OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819], outs := [15390, 13933, 13943, 13957, 13969], params := [5] }

private def l12OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8531], outs := [5637], params := [4096, 1024] }

private def l12OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8535], outs := [5641], params := [4096, 1024] }

private def l12OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13956], outs := [9850], params := [2048, 1024] }

private def l12OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13957], outs := [9851], params := [2048, 1024] }

private def l12OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13968], outs := [9862], params := [2048, 1024] }

private def l12OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13969], outs := [9863], params := [2048, 1024] }

private def l12OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5637, 5638], outs := [5639] }

private def l12OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5641, 5642], outs := [5643] }

private def l12OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9850, 5638], outs := [9854] }

private def l12OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9851, 5638], outs := [9855] }

private def l12OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9862, 5642], outs := [9866] }

private def l12OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9863, 5642], outs := [9867] }

private def l12OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5639], outs := [5640], params := [4096, 512] }

private def l12OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5643], outs := [5644], params := [4096, 512] }

private def l12OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9854], outs := [9856], params := [2048, 512] }

private def l12OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9855], outs := [9857], params := [2048, 512] }

private def l12OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9866], outs := [9868], params := [2048, 512] }

private def l12OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9867], outs := [9869], params := [2048, 512] }

private def l12OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5640, 5644], outs := [5645] }

private def l12OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9856, 9868], outs := [9874] }

private def l12OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9857, 9869], outs := [9875] }

private def l12OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5645], outs := [5646], params := [4096, 512] }

private def l12OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9874], outs := [9876], params := [2048, 512] }

private def l12OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9875], outs := [9877], params := [2048, 512] }

private def l12OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5646, 5647], outs := [5648] }

private def l12OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9876, 5647], outs := [9882] }

private def l12OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9877, 5647], outs := [9883] }

private def l12OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5648], outs := [5649], params := [4096, 1024] }

private def l12OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9882], outs := [9884], params := [2048, 1024] }

private def l12OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9883], outs := [9885], params := [2048, 1024] }

private theorem l12OMOd_red_sm13956 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8531 =
      denoteGraphDistributedFaithful sm_goal_1 init 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 514 l12OMOdSmRef
    5622 8531 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8519, 8523, 8527, 8531, 8535] 5 rfl 8531 (by decide)

private theorem l12OMOd_red_sm13968 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8535 =
      denoteGraphDistributedFaithful sm_goal_1 init 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 514 l12OMOdSmRef
    5622 8535 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8519, 8523, 8527, 8531, 8535] 5 rfl 8535 (by decide)

private theorem l12OMOd_red_pm13956 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13956 =
      denoteGraphDistributedFaithful pm_goal_1 init 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1131 l12OMOdPmRef0
    9818 13956 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818 [15388, 13932, 13942, 13956, 13968] 5 rfl 13956 (by decide)

private theorem l12OMOd_red_pm13968 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13968 =
      denoteGraphDistributedFaithful pm_goal_1 init 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1131 l12OMOdPmRef0
    9818 13968 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818 [15388, 13932, 13942, 13956, 13968] 5 rfl 13968 (by decide)

private theorem l12OMOd_red_pm13957 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13957 =
      denoteGraphDistributedFaithful pm_goal_1 init 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1132 l12OMOdPmRef1
    9819 13957 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819 [15390, 13933, 13943, 13957, 13969] 5 rfl 13957 (by decide)

private theorem l12OMOd_red_pm13969 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13969 =
      denoteGraphDistributedFaithful pm_goal_1 init 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1132 l12OMOdPmRef1
    9819 13969 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819 [15390, 13933, 13943, 13957, 13969] 5 rfl 13969 (by decide)

private theorem l12OMOd_red_sm5637 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5637 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8531) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 517 l12OMOdSmReshapeA
    8531 5637 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8531 5637 [4096, 1024]

private theorem l12OMOd_red_sm5641 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5641 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8535) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 518 l12OMOdSmReshapeB
    8535 5641 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8535 5641 [4096, 1024]

private theorem l12OMOd_red_pm9850 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9850 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13956) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1134 l12OMOdPmReshapeA0
    13956 9850 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13956 9850 [2048, 1024]

private theorem l12OMOd_red_pm9851 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9851 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13957) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1138 l12OMOdPmReshapeA1
    13957 9851 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13957 9851 [2048, 1024]

private theorem l12OMOd_red_pm9862 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9862 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13968) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1135 l12OMOdPmReshapeB0
    13968 9862 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13968 9862 [2048, 1024]

private theorem l12OMOd_red_pm9863 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9863 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13969) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1139 l12OMOdPmReshapeB1
    13969 9863 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13969 9863 [2048, 1024]

private theorem l12OMOd_red_sm5640 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5640 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5639) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 525 l12OMOdSmViewA
    5639 5640 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5639 5640

private theorem l12OMOd_red_sm5644 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5644 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5643) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 526 l12OMOdSmViewB
    5643 5644 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5643 5644

private theorem l12OMOd_red_pm9856 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9856 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9854) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1149 l12OMOdPmViewA0
    9854 9856 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9854 9856

private theorem l12OMOd_red_pm9857 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9857 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9855) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1154 l12OMOdPmViewA1
    9855 9857 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9855 9857

private theorem l12OMOd_red_pm9868 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9868 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9866) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1150 l12OMOdPmViewB0
    9866 9868 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9866 9868

private theorem l12OMOd_red_pm9869 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9869 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9867) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1155 l12OMOdPmViewB1
    9867 9869 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9867 9869

private theorem l12OMOd_red_sm5646 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5646 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5645) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 530 l12OMOdSmReshapeDown
    5645 5646 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5645 5646 [4096, 512]

private theorem l12OMOd_red_pm9876 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9876 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9874) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1162 l12OMOdPmReshapeDown0
    9874 9876 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9874 9876 [2048, 512]

private theorem l12OMOd_red_pm9877 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9877 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9875) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1165 l12OMOdPmReshapeDown1
    9875 9877 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9875 9877 [2048, 512]

private theorem l12OMOd_red_sm5649 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5649 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5648) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 532 l12OMOdSmViewDown
    5648 5649 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5648 5649

private theorem l12OMOd_red_pm9884 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9884 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9882) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1170 l12OMOdPmViewDown0
    9882 9884 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9882 9884

private theorem l12OMOd_red_pm9885 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9885 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9883) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1171 l12OMOdPmViewDown1
    9883 9885 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9883 9885

private theorem l12OMOd_red_sm5639 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5639 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5637)
        (denoteGraphDistributedFaithful sm_goal_1 init 5638) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 521 l12OMOdSmLinearA
    5637 5638 5639 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5637 5638 5639

private theorem l12OMOd_red_sm5643 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5643 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5641)
        (denoteGraphDistributedFaithful sm_goal_1 init 5642) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 522 l12OMOdSmLinearB
    5641 5642 5643 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5641 5642 5643

private theorem l12OMOd_red_pm9854 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9854 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9850)
        (denoteGraphDistributedFaithful pm_goal_1 init 5638) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1141 l12OMOdPmLinearA0
    9850 5638 9854 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9850 5638 9854

private theorem l12OMOd_red_pm9855 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9855 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9851)
        (denoteGraphDistributedFaithful pm_goal_1 init 5638) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1146 l12OMOdPmLinearA1
    9851 5638 9855 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9851 5638 9855

private theorem l12OMOd_red_pm9866 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9866 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9862)
        (denoteGraphDistributedFaithful pm_goal_1 init 5642) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1142 l12OMOdPmLinearB0
    9862 5642 9866 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9862 5642 9866

private theorem l12OMOd_red_pm9867 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9867 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9863)
        (denoteGraphDistributedFaithful pm_goal_1 init 5642) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1147 l12OMOdPmLinearB1
    9863 5642 9867 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9863 5642 9867

private theorem l12OMOd_red_sm5645 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5645 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5640)
        (denoteGraphDistributedFaithful sm_goal_1 init 5644) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 529 l12OMOdSmSwi
    5640 5644 5645 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5640 5644 5645

private theorem l12OMOd_red_pm9874 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9874 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9856)
        (denoteGraphDistributedFaithful pm_goal_1 init 9868) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1157 l12OMOdPmSwi0
    9856 9868 9874 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9856 9868 9874

private theorem l12OMOd_red_pm9875 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9875 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9857)
        (denoteGraphDistributedFaithful pm_goal_1 init 9869) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1161 l12OMOdPmSwi1
    9857 9869 9875 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9857 9869 9875

private theorem l12OMOd_red_sm5648 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5648 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5646)
        (denoteGraphDistributedFaithful sm_goal_1 init 5647) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 531 l12OMOdSmLinearDown
    5646 5647 5648 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5646 5647 5648

private theorem l12OMOd_red_pm9882 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9882 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9876)
        (denoteGraphDistributedFaithful pm_goal_1 init 5647) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1166 l12OMOdPmLinearDown0
    9876 5647 9882 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9876 5647 9882

private theorem l12OMOd_red_pm9883 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9883 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9877)
        (denoteGraphDistributedFaithful pm_goal_1 init 5647) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1169 l12OMOdPmLinearDown1
    9877 5647 9883 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9877 5647 9883

private theorem l12OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l12OMOd_weight_eq (initSM initPM : Store)
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
  rw [l12OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l12OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l12OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l12OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l12OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l12OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5649 ↔ 9884/9885` ordinary relation. -/
theorem l12_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5645)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9874)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9875)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9885)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9876)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9877)
      [4096, 512] [2048, 512] := by
    rw [l12OMOd_red_sm5646 initSM, l12OMOd_red_pm9876 initPM, l12OMOd_red_pm9877 initPM]
    exact ordinary_view hSwi
  have hwD := l12OMOd_weight_eq initSM initPM hInit initGoal_5647 (by native_decide)
    5647 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l12OMOd_weight_shape initPM hPM 5647 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9883)
      [4096, 1024] [2048, 1024] := by
    rw [l12OMOd_red_sm5648 initSM, l12OMOd_red_pm9882 initPM,
      l12OMOd_red_pm9883 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l12OMOd_red_sm5649 initSM, l12OMOd_red_pm9884 initPM, l12OMOd_red_pm9885 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l12_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9885)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5637)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9850)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9851)
      [4096, 1024] [2048, 1024] := by
    rw [l12OMOd_red_sm5637 initSM, l12OMOd_red_pm9850 initPM,
      l12OMOd_red_pm9851 initPM, l12OMOd_red_sm13956 initSM,
      l12OMOd_red_pm13956 initPM, l12OMOd_red_pm13957 initPM]
    exact ordinary_view hNorm
  have hwA := l12OMOd_weight_eq initSM initPM hInit initGoal_5638 (by native_decide)
    5638 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l12OMOd_weight_shape initPM hPM 5638 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5639)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9854)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9855)
      [4096, 512] [2048, 512] := by
    rw [l12OMOd_red_sm5639 initSM, l12OMOd_red_pm9854 initPM,
      l12OMOd_red_pm9855 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5640)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9856)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9857)
      [4096, 512] [2048, 512] := by
    rw [l12OMOd_red_sm5640 initSM, l12OMOd_red_pm9856 initPM,
      l12OMOd_red_pm9857 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5641)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9863)
      [4096, 1024] [2048, 1024] := by
    rw [l12OMOd_red_sm5641 initSM, l12OMOd_red_pm9862 initPM,
      l12OMOd_red_pm9863 initPM, l12OMOd_red_sm13968 initSM,
      l12OMOd_red_pm13968 initPM, l12OMOd_red_pm13969 initPM]
    exact ordinary_view hNorm
  have hwB := l12OMOd_weight_eq initSM initPM hInit initGoal_5642 (by native_decide)
    5642 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l12OMOd_weight_shape initPM hPM 5642 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5643)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9866)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9867)
      [4096, 512] [2048, 512] := by
    rw [l12OMOd_red_sm5643 initSM, l12OMOd_red_pm9866 initPM,
      l12OMOd_red_pm9867 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5644)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9868)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9869)
      [4096, 512] [2048, 512] := by
    rw [l12OMOd_red_sm5644 initSM, l12OMOd_red_pm9868 initPM,
      l12OMOd_red_pm9869 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5645)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9874)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9875)
      [4096, 512] [2048, 512] := by
    rw [l12OMOd_red_sm5645 initSM, l12OMOd_red_pm9874 initPM,
      l12OMOd_red_pm9875 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l12_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l12_ordinary_moe_down_from_swiglu
#print axioms l12_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
