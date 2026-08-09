/- Canonical Goal 1, layer 12: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L12ZigzagMoEResidualGate

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

private def l12ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622], outs := [8519, 8523, 8527, 8531, 8535], params := [5] }

private def l12ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818], outs := [15388, 13932, 13942, 13956, 13968], params := [5] }

private def l12ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819], outs := [15390, 13933, 13943, 13957, 13969], params := [5] }

private def l12ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8531], outs := [5637], params := [4096, 1024] }

private def l12ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8535], outs := [5641], params := [4096, 1024] }

private def l12ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13956], outs := [9850], params := [2048, 1024] }

private def l12ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13957], outs := [9851], params := [2048, 1024] }

private def l12ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13968], outs := [9862], params := [2048, 1024] }

private def l12ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13969], outs := [9863], params := [2048, 1024] }

private def l12ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5637, 5638], outs := [5639] }

private def l12ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5641, 5642], outs := [5643] }

private def l12ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9850, 5638], outs := [9854] }

private def l12ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9851, 5638], outs := [9855] }

private def l12ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9862, 5642], outs := [9866] }

private def l12ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9863, 5642], outs := [9867] }

private def l12ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5639], outs := [5640], params := [4096, 512] }

private def l12ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5643], outs := [5644], params := [4096, 512] }

private def l12ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9854], outs := [9856], params := [2048, 512] }

private def l12ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9855], outs := [9857], params := [2048, 512] }

private def l12ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9866], outs := [9868], params := [2048, 512] }

private def l12ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9867], outs := [9869], params := [2048, 512] }

private def l12ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5640, 5644], outs := [5645] }

private def l12ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9856, 9868], outs := [9874] }

private def l12ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9857, 9869], outs := [9875] }

private def l12ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5645], outs := [5646], params := [4096, 512] }

private def l12ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9874], outs := [9876], params := [2048, 512] }

private def l12ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9875], outs := [9877], params := [2048, 512] }

private def l12ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5646, 5647], outs := [5648] }

private def l12ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9876, 5647], outs := [9882] }

private def l12ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9877, 5647], outs := [9883] }

private def l12ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5648], outs := [5649], params := [4096, 1024] }

private def l12ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9882], outs := [9884], params := [2048, 1024] }

private def l12ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9883], outs := [9885], params := [2048, 1024] }

private theorem l12ZMd_red_sm8531 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8531 =
      denoteGraphDistributedFaithful sm_goal_1 init 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 514 l12ZMdSmRef
    5622 8531 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8948, 8952, 8956, 8531, 8535] 5 rfl 8531 (by decide)

private theorem l12ZMd_red_sm8535 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8535 =
      denoteGraphDistributedFaithful sm_goal_1 init 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 514 l12ZMdSmRef
    5622 8535 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8948, 8952, 8956, 8531, 8535] 5 rfl 8535 (by decide)

private theorem l12ZMd_red_pm13956 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13956 =
      denoteGraphDistributedFaithful pm_goal_1 init 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1131 l12ZMdPmRef0
    9818 13956 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818 [15388, 13932, 13942, 13956, 13968] 5 rfl 13956 (by decide)

private theorem l12ZMd_red_pm13968 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13968 =
      denoteGraphDistributedFaithful pm_goal_1 init 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1131 l12ZMdPmRef0
    9818 13968 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818 [15388, 13932, 13942, 13956, 13968] 5 rfl 13968 (by decide)

private theorem l12ZMd_red_pm13957 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13957 =
      denoteGraphDistributedFaithful pm_goal_1 init 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1132 l12ZMdPmRef1
    9819 13957 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819 [15390, 13933, 13943, 13957, 13969] 5 rfl 13957 (by decide)

private theorem l12ZMd_red_pm13969 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13969 =
      denoteGraphDistributedFaithful pm_goal_1 init 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1132 l12ZMdPmRef1
    9819 13969 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819 [15390, 13933, 13943, 13957, 13969] 5 rfl 13969 (by decide)

private theorem l12ZMd_red_sm5637 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5637 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8531) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 517 l12ZMdSmReshapeA
    8531 5637 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8531 5637 [4096, 1024]

private theorem l12ZMd_red_sm5641 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5641 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8535) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 518 l12ZMdSmReshapeB
    8535 5641 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8535 5641 [4096, 1024]

private theorem l12ZMd_red_pm9850 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9850 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13956) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1134 l12ZMdPmReshapeA0
    13956 9850 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13956 9850 [2048, 1024]

private theorem l12ZMd_red_pm9851 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9851 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13957) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1138 l12ZMdPmReshapeA1
    13957 9851 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13957 9851 [2048, 1024]

private theorem l12ZMd_red_pm9862 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9862 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13968) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1135 l12ZMdPmReshapeB0
    13968 9862 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13968 9862 [2048, 1024]

private theorem l12ZMd_red_pm9863 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9863 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13969) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1139 l12ZMdPmReshapeB1
    13969 9863 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13969 9863 [2048, 1024]

private theorem l12ZMd_red_sm5640 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5640 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5639) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 525 l12ZMdSmViewA
    5639 5640 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5639 5640

private theorem l12ZMd_red_sm5644 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5644 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5643) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 526 l12ZMdSmViewB
    5643 5644 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5643 5644

private theorem l12ZMd_red_pm9856 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9856 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9854) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1149 l12ZMdPmViewA0
    9854 9856 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9854 9856

private theorem l12ZMd_red_pm9857 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9857 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9855) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1154 l12ZMdPmViewA1
    9855 9857 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9855 9857

private theorem l12ZMd_red_pm9868 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9868 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9866) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1150 l12ZMdPmViewB0
    9866 9868 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9866 9868

private theorem l12ZMd_red_pm9869 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9869 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9867) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1155 l12ZMdPmViewB1
    9867 9869 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9867 9869

private theorem l12ZMd_red_sm5646 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5646 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5645) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 530 l12ZMdSmReshapeDown
    5645 5646 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5645 5646 [4096, 512]

private theorem l12ZMd_red_pm9876 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9876 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9874) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1162 l12ZMdPmReshapeDown0
    9874 9876 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9874 9876 [2048, 512]

private theorem l12ZMd_red_pm9877 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9877 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9875) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1165 l12ZMdPmReshapeDown1
    9875 9877 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9875 9877 [2048, 512]

private theorem l12ZMd_red_sm5649 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5649 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5648) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 532 l12ZMdSmViewDown
    5648 5649 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5648 5649

private theorem l12ZMd_red_pm9884 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9884 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9882) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1170 l12ZMdPmViewDown0
    9882 9884 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9882 9884

private theorem l12ZMd_red_pm9885 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9885 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9883) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1171 l12ZMdPmViewDown1
    9883 9885 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9883 9885

private theorem l12ZMd_red_sm5639 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5639 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5637)
        (denoteGraphDistributedFaithful sm_goal_1 init 5638) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 521 l12ZMdSmLinearA
    5637 5638 5639 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5637 5638 5639

private theorem l12ZMd_red_sm5643 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5643 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5641)
        (denoteGraphDistributedFaithful sm_goal_1 init 5642) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 522 l12ZMdSmLinearB
    5641 5642 5643 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5641 5642 5643

private theorem l12ZMd_red_pm9854 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9854 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9850)
        (denoteGraphDistributedFaithful pm_goal_1 init 5638) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1141 l12ZMdPmLinearA0
    9850 5638 9854 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9850 5638 9854

private theorem l12ZMd_red_pm9855 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9855 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9851)
        (denoteGraphDistributedFaithful pm_goal_1 init 5638) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1146 l12ZMdPmLinearA1
    9851 5638 9855 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9851 5638 9855

private theorem l12ZMd_red_pm9866 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9866 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9862)
        (denoteGraphDistributedFaithful pm_goal_1 init 5642) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1142 l12ZMdPmLinearB0
    9862 5642 9866 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9862 5642 9866

private theorem l12ZMd_red_pm9867 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9867 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9863)
        (denoteGraphDistributedFaithful pm_goal_1 init 5642) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1147 l12ZMdPmLinearB1
    9863 5642 9867 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9863 5642 9867

private theorem l12ZMd_red_sm5645 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5645 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5640)
        (denoteGraphDistributedFaithful sm_goal_1 init 5644) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 529 l12ZMdSmSwi
    5640 5644 5645 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5640 5644 5645

private theorem l12ZMd_red_pm9874 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9874 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9856)
        (denoteGraphDistributedFaithful pm_goal_1 init 9868) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1157 l12ZMdPmSwi0
    9856 9868 9874 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9856 9868 9874

private theorem l12ZMd_red_pm9875 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9875 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9857)
        (denoteGraphDistributedFaithful pm_goal_1 init 9869) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1161 l12ZMdPmSwi1
    9857 9869 9875 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9857 9869 9875

private theorem l12ZMd_red_sm5648 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5648 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5646)
        (denoteGraphDistributedFaithful sm_goal_1 init 5647) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 531 l12ZMdSmLinearDown
    5646 5647 5648 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5646 5647 5648

private theorem l12ZMd_red_pm9882 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9882 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9876)
        (denoteGraphDistributedFaithful pm_goal_1 init 5647) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1166 l12ZMdPmLinearDown0
    9876 5647 9882 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9876 5647 9882

private theorem l12ZMd_red_pm9883 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9883 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9877)
        (denoteGraphDistributedFaithful pm_goal_1 init 5647) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1169 l12ZMdPmLinearDown1
    9877 5647 9883 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9877 5647 9883

private theorem l12ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l12ZMd_weight_eq (initSM initPM : Store)
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
  rw [l12ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l12ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l12ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l12ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L21 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l12_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5649)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9885)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8531)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13956)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13957)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm8531 initSM, l12ZMd_red_pm13956 initPM, l12ZMd_red_pm13957 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8535)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm8535 initSM, l12ZMd_red_pm13968 initPM, l12ZMd_red_pm13969 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5637)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9850)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9851)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm5637 initSM, l12ZMd_red_pm9850 initPM, l12ZMd_red_pm9851 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5641)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9863)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm5641 initSM, l12ZMd_red_pm9862 initPM, l12ZMd_red_pm9863 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l12ZMd_weight_eq initSM initPM hInit initGoal_5638 (by native_decide)
    5638 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l12ZMd_weight_eq initSM initPM hInit initGoal_5642 (by native_decide)
    5642 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l12ZMd_weight_shape initPM hPM 5638 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l12ZMd_weight_shape initPM hPM 5642 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5639)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9854)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9855)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5639 initSM, l12ZMd_red_pm9854 initPM,
      l12ZMd_red_pm9855 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5643)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9866)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9867)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5643 initSM, l12ZMd_red_pm9866 initPM,
      l12ZMd_red_pm9867 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5640)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9856)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9857)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5640 initSM, l12ZMd_red_pm9856 initPM, l12ZMd_red_pm9857 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5644)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9868)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5644 initSM, l12ZMd_red_pm9868 initPM, l12ZMd_red_pm9869 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5640)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9856)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9857)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5644)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9868)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5645)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9874)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9875)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5645 initSM, l12ZMd_red_pm9874 initPM, l12ZMd_red_pm9875 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9876)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9877)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5646 initSM, l12ZMd_red_pm9876 initPM, l12ZMd_red_pm9877 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l12ZMd_weight_eq initSM initPM hInit initGoal_5647 (by native_decide)
    5647 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l12ZMd_weight_shape initPM hPM 5647 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9883)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm5648 initSM, l12ZMd_red_pm9882 initPM,
      l12ZMd_red_pm9883 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l12ZMd_red_sm5649 initSM, l12ZMd_red_pm9884 initPM, l12ZMd_red_pm9885 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
