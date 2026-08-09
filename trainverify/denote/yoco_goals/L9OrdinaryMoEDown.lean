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

private def l9OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8244, 8248, 8252, 8256, 8260], params := [5] }

private def l9OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9308], outs := [15368, 13544, 13554, 13568, 13580], params := [5] }

private def l9OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9309], outs := [15370, 13545, 13555, 13569, 13581], params := [5] }

private def l9OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8256], outs := [5469], params := [4096, 1024] }

private def l9OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8260], outs := [5473], params := [4096, 1024] }

private def l9OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13568], outs := [9340], params := [2048, 1024] }

private def l9OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13569], outs := [9341], params := [2048, 1024] }

private def l9OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13580], outs := [9352], params := [2048, 1024] }

private def l9OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13581], outs := [9353], params := [2048, 1024] }

private def l9OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5469, 5470], outs := [5471] }

private def l9OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5473, 5474], outs := [5475] }

private def l9OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9340, 5470], outs := [9344] }

private def l9OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9341, 5470], outs := [9345] }

private def l9OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9352, 5474], outs := [9356] }

private def l9OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9353, 5474], outs := [9357] }

private def l9OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5471], outs := [5472], params := [4096, 512] }

private def l9OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5475], outs := [5476], params := [4096, 512] }

private def l9OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9344], outs := [9346], params := [2048, 512] }

private def l9OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9345], outs := [9347], params := [2048, 512] }

private def l9OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9356], outs := [9358], params := [2048, 512] }

private def l9OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9357], outs := [9359], params := [2048, 512] }

private def l9OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5472, 5476], outs := [5477] }

private def l9OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9346, 9358], outs := [9364] }

private def l9OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9347, 9359], outs := [9365] }

private def l9OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5477], outs := [5478], params := [4096, 512] }

private def l9OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9364], outs := [9366], params := [2048, 512] }

private def l9OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9365], outs := [9367], params := [2048, 512] }

private def l9OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5478, 5479], outs := [5480] }

private def l9OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9366, 5479], outs := [9372] }

private def l9OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9367, 5479], outs := [9373] }

private def l9OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5480], outs := [5481], params := [4096, 1024] }

private def l9OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9372], outs := [9374], params := [2048, 1024] }

private def l9OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9373], outs := [9375], params := [2048, 1024] }

private theorem l9OMOd_red_sm13568 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8256 =
      denoteGraphDistributedFaithful sm_goal_1 init 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 369 l9OMOdSmRef
    5454 8256 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5454 [8244, 8248, 8252, 8256, 8260] 5 rfl 8256 (by decide)

private theorem l9OMOd_red_sm13580 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8260 =
      denoteGraphDistributedFaithful sm_goal_1 init 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 369 l9OMOdSmRef
    5454 8260 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5454 [8244, 8248, 8252, 8256, 8260] 5 rfl 8260 (by decide)

private theorem l9OMOd_red_pm13568 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13568 =
      denoteGraphDistributedFaithful pm_goal_1 init 9308 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 823 l9OMOdPmRef0
    9308 13568 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9308 [15368, 13544, 13554, 13568, 13580] 5 rfl 13568 (by decide)

private theorem l9OMOd_red_pm13580 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13580 =
      denoteGraphDistributedFaithful pm_goal_1 init 9308 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 823 l9OMOdPmRef0
    9308 13580 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9308 [15368, 13544, 13554, 13568, 13580] 5 rfl 13580 (by decide)

private theorem l9OMOd_red_pm13569 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13569 =
      denoteGraphDistributedFaithful pm_goal_1 init 9309 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 824 l9OMOdPmRef1
    9309 13569 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9309 [15370, 13545, 13555, 13569, 13581] 5 rfl 13569 (by decide)

private theorem l9OMOd_red_pm13581 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13581 =
      denoteGraphDistributedFaithful pm_goal_1 init 9309 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 824 l9OMOdPmRef1
    9309 13581 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9309 [15370, 13545, 13555, 13569, 13581] 5 rfl 13581 (by decide)

private theorem l9OMOd_red_sm5469 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5469 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8256) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 372 l9OMOdSmReshapeA
    8256 5469 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8256 5469 [4096, 1024]

private theorem l9OMOd_red_sm5473 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5473 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8260) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 373 l9OMOdSmReshapeB
    8260 5473 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8260 5473 [4096, 1024]

private theorem l9OMOd_red_pm9340 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9340 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13568) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 826 l9OMOdPmReshapeA0
    13568 9340 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13568 9340 [2048, 1024]

private theorem l9OMOd_red_pm9341 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9341 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13569) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 830 l9OMOdPmReshapeA1
    13569 9341 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13569 9341 [2048, 1024]

private theorem l9OMOd_red_pm9352 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9352 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13580) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 827 l9OMOdPmReshapeB0
    13580 9352 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13580 9352 [2048, 1024]

private theorem l9OMOd_red_pm9353 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9353 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13581) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 831 l9OMOdPmReshapeB1
    13581 9353 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13581 9353 [2048, 1024]

private theorem l9OMOd_red_sm5472 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5472 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5471) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 380 l9OMOdSmViewA
    5471 5472 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5471 5472

private theorem l9OMOd_red_sm5476 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5476 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5475) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 381 l9OMOdSmViewB
    5475 5476 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5475 5476

private theorem l9OMOd_red_pm9346 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9346 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9344) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 841 l9OMOdPmViewA0
    9344 9346 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9344 9346

private theorem l9OMOd_red_pm9347 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9347 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9345) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 846 l9OMOdPmViewA1
    9345 9347 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9345 9347

private theorem l9OMOd_red_pm9358 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9358 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9356) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 842 l9OMOdPmViewB0
    9356 9358 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9356 9358

private theorem l9OMOd_red_pm9359 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9359 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9357) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 847 l9OMOdPmViewB1
    9357 9359 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9357 9359

private theorem l9OMOd_red_sm5478 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5478 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5477) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 385 l9OMOdSmReshapeDown
    5477 5478 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5477 5478 [4096, 512]

private theorem l9OMOd_red_pm9366 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9366 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9364) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 854 l9OMOdPmReshapeDown0
    9364 9366 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9364 9366 [2048, 512]

private theorem l9OMOd_red_pm9367 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9367 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9365) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 857 l9OMOdPmReshapeDown1
    9365 9367 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9365 9367 [2048, 512]

private theorem l9OMOd_red_sm5481 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5481 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5480) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 387 l9OMOdSmViewDown
    5480 5481 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5480 5481

private theorem l9OMOd_red_pm9374 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9374 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9372) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 862 l9OMOdPmViewDown0
    9372 9374 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9372 9374

private theorem l9OMOd_red_pm9375 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9375 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9373) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 863 l9OMOdPmViewDown1
    9373 9375 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9373 9375

private theorem l9OMOd_red_sm5471 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5471 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5469)
        (denoteGraphDistributedFaithful sm_goal_1 init 5470) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 376 l9OMOdSmLinearA
    5469 5470 5471 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5469 5470 5471

private theorem l9OMOd_red_sm5475 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5475 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5473)
        (denoteGraphDistributedFaithful sm_goal_1 init 5474) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 377 l9OMOdSmLinearB
    5473 5474 5475 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5473 5474 5475

private theorem l9OMOd_red_pm9344 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9344 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9340)
        (denoteGraphDistributedFaithful pm_goal_1 init 5470) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 833 l9OMOdPmLinearA0
    9340 5470 9344 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9340 5470 9344

private theorem l9OMOd_red_pm9345 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9345 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9341)
        (denoteGraphDistributedFaithful pm_goal_1 init 5470) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 838 l9OMOdPmLinearA1
    9341 5470 9345 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9341 5470 9345

private theorem l9OMOd_red_pm9356 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9356 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9352)
        (denoteGraphDistributedFaithful pm_goal_1 init 5474) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 834 l9OMOdPmLinearB0
    9352 5474 9356 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9352 5474 9356

private theorem l9OMOd_red_pm9357 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9357 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9353)
        (denoteGraphDistributedFaithful pm_goal_1 init 5474) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 839 l9OMOdPmLinearB1
    9353 5474 9357 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9353 5474 9357

private theorem l9OMOd_red_sm5477 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5477 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5472)
        (denoteGraphDistributedFaithful sm_goal_1 init 5476) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 384 l9OMOdSmSwi
    5472 5476 5477 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5472 5476 5477

private theorem l9OMOd_red_pm9364 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9364 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9346)
        (denoteGraphDistributedFaithful pm_goal_1 init 9358) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 849 l9OMOdPmSwi0
    9346 9358 9364 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9346 9358 9364

private theorem l9OMOd_red_pm9365 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9365 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9347)
        (denoteGraphDistributedFaithful pm_goal_1 init 9359) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 853 l9OMOdPmSwi1
    9347 9359 9365 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9347 9359 9365

private theorem l9OMOd_red_sm5480 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5480 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5478)
        (denoteGraphDistributedFaithful sm_goal_1 init 5479) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 386 l9OMOdSmLinearDown
    5478 5479 5480 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5478 5479 5480

private theorem l9OMOd_red_pm9372 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9372 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9366)
        (denoteGraphDistributedFaithful pm_goal_1 init 5479) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 858 l9OMOdPmLinearDown0
    9366 5479 9372 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9366 5479 9372

private theorem l9OMOd_red_pm9373 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9373 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9367)
        (denoteGraphDistributedFaithful pm_goal_1 init 5479) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 861 l9OMOdPmLinearDown1
    9367 5479 9373 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9367 5479 9373

private theorem l9OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l9OMOd_weight_eq (initSM initPM : Store)
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
  rw [l9OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l9OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l9OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l9OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l9OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l9OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5481 ↔ 9374/9375` ordinary relation. -/
theorem l9_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5477)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9364)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9365)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5481)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9374)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9375)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9366)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9367)
      [4096, 512] [2048, 512] := by
    rw [l9OMOd_red_sm5478 initSM, l9OMOd_red_pm9366 initPM, l9OMOd_red_pm9367 initPM]
    exact ordinary_view hSwi
  have hwD := l9OMOd_weight_eq initSM initPM hInit initGoal_5479 (by native_decide)
    5479 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l9OMOd_weight_shape initPM hPM 5479 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5480)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9372)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9373)
      [4096, 1024] [2048, 1024] := by
    rw [l9OMOd_red_sm5480 initSM, l9OMOd_red_pm9372 initPM,
      l9OMOd_red_pm9373 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l9OMOd_red_sm5481 initSM, l9OMOd_red_pm9374 initPM, l9OMOd_red_pm9375 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l9_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9308)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9309)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5481)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9374)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9375)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5469)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9340)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9341)
      [4096, 1024] [2048, 1024] := by
    rw [l9OMOd_red_sm5469 initSM, l9OMOd_red_pm9340 initPM,
      l9OMOd_red_pm9341 initPM, l9OMOd_red_sm13568 initSM,
      l9OMOd_red_pm13568 initPM, l9OMOd_red_pm13569 initPM]
    exact ordinary_view hNorm
  have hwA := l9OMOd_weight_eq initSM initPM hInit initGoal_5470 (by native_decide)
    5470 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l9OMOd_weight_shape initPM hPM 5470 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5471)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9344)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9345)
      [4096, 512] [2048, 512] := by
    rw [l9OMOd_red_sm5471 initSM, l9OMOd_red_pm9344 initPM,
      l9OMOd_red_pm9345 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5472)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9346)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9347)
      [4096, 512] [2048, 512] := by
    rw [l9OMOd_red_sm5472 initSM, l9OMOd_red_pm9346 initPM,
      l9OMOd_red_pm9347 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5473)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9352)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9353)
      [4096, 1024] [2048, 1024] := by
    rw [l9OMOd_red_sm5473 initSM, l9OMOd_red_pm9352 initPM,
      l9OMOd_red_pm9353 initPM, l9OMOd_red_sm13580 initSM,
      l9OMOd_red_pm13580 initPM, l9OMOd_red_pm13581 initPM]
    exact ordinary_view hNorm
  have hwB := l9OMOd_weight_eq initSM initPM hInit initGoal_5474 (by native_decide)
    5474 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l9OMOd_weight_shape initPM hPM 5474 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5475)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9356)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9357)
      [4096, 512] [2048, 512] := by
    rw [l9OMOd_red_sm5475 initSM, l9OMOd_red_pm9356 initPM,
      l9OMOd_red_pm9357 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5476)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9358)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9359)
      [4096, 512] [2048, 512] := by
    rw [l9OMOd_red_sm5476 initSM, l9OMOd_red_pm9358 initPM,
      l9OMOd_red_pm9359 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5477)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9364)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9365)
      [4096, 512] [2048, 512] := by
    rw [l9OMOd_red_sm5477 initSM, l9OMOd_red_pm9364 initPM,
      l9OMOd_red_pm9365 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l9_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l9_ordinary_moe_down_from_swiglu
#print axioms l9_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
