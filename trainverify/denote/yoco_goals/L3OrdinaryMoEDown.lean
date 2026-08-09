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

private def l3OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5124], outs := [7932, 7936, 7940, 7944, 7948], params := [5] }

private def l3OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8324], outs := [15320, 12788, 12798, 12812, 12824], params := [5] }

private def l3OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8325], outs := [15322, 12789, 12799, 12813, 12825], params := [5] }

private def l3OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7944], outs := [5139], params := [4096, 1024] }

private def l3OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7948], outs := [5143], params := [4096, 1024] }

private def l3OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12812], outs := [8356], params := [2048, 1024] }

private def l3OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12813], outs := [8357], params := [2048, 1024] }

private def l3OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12824], outs := [8368], params := [2048, 1024] }

private def l3OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12825], outs := [8369], params := [2048, 1024] }

private def l3OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5139, 5140], outs := [5141] }

private def l3OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5143, 5144], outs := [5145] }

private def l3OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8356, 5140], outs := [8360] }

private def l3OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8357, 5140], outs := [8361] }

private def l3OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8368, 5144], outs := [8372] }

private def l3OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8369, 5144], outs := [8373] }

private def l3OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5141], outs := [5142], params := [4096, 512] }

private def l3OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5145], outs := [5146], params := [4096, 512] }

private def l3OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8360], outs := [8362], params := [2048, 512] }

private def l3OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8361], outs := [8363], params := [2048, 512] }

private def l3OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8372], outs := [8374], params := [2048, 512] }

private def l3OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8373], outs := [8375], params := [2048, 512] }

private def l3OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5142, 5146], outs := [5147] }

private def l3OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [8362, 8374], outs := [8380] }

private def l3OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [8363, 8375], outs := [8381] }

private def l3OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5147], outs := [5148], params := [4096, 512] }

private def l3OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8380], outs := [8382], params := [2048, 512] }

private def l3OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [8381], outs := [8383], params := [2048, 512] }

private def l3OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5148, 5149], outs := [5150] }

private def l3OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8382, 5149], outs := [8388] }

private def l3OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8383, 5149], outs := [8389] }

private def l3OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5150], outs := [5151], params := [4096, 1024] }

private def l3OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8388], outs := [8390], params := [2048, 1024] }

private def l3OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8389], outs := [8391], params := [2048, 1024] }

private theorem l3OMOd_red_sm12812 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7944 =
      denoteGraphDistributedFaithful sm_goal_1 init 5124 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 135 l3OMOdSmRef
    5124 7944 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5124 [7932, 7936, 7940, 7944, 7948] 5 rfl 7944 (by decide)

private theorem l3OMOd_red_sm12824 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7948 =
      denoteGraphDistributedFaithful sm_goal_1 init 5124 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 135 l3OMOdSmRef
    5124 7948 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5124 [7932, 7936, 7940, 7944, 7948] 5 rfl 7948 (by decide)

private theorem l3OMOd_red_pm12812 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12812 =
      denoteGraphDistributedFaithful pm_goal_1 init 8324 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 319 l3OMOdPmRef0
    8324 12812 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8324 [15320, 12788, 12798, 12812, 12824] 5 rfl 12812 (by decide)

private theorem l3OMOd_red_pm12824 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12824 =
      denoteGraphDistributedFaithful pm_goal_1 init 8324 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 319 l3OMOdPmRef0
    8324 12824 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8324 [15320, 12788, 12798, 12812, 12824] 5 rfl 12824 (by decide)

private theorem l3OMOd_red_pm12813 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12813 =
      denoteGraphDistributedFaithful pm_goal_1 init 8325 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 320 l3OMOdPmRef1
    8325 12813 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8325 [15322, 12789, 12799, 12813, 12825] 5 rfl 12813 (by decide)

private theorem l3OMOd_red_pm12825 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12825 =
      denoteGraphDistributedFaithful pm_goal_1 init 8325 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 320 l3OMOdPmRef1
    8325 12825 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8325 [15322, 12789, 12799, 12813, 12825] 5 rfl 12825 (by decide)

private theorem l3OMOd_red_sm5139 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5139 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7944) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 138 l3OMOdSmReshapeA
    7944 5139 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7944 5139 [4096, 1024]

private theorem l3OMOd_red_sm5143 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5143 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7948) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 139 l3OMOdSmReshapeB
    7948 5143 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7948 5143 [4096, 1024]

private theorem l3OMOd_red_pm8356 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8356 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12812) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 322 l3OMOdPmReshapeA0
    12812 8356 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12812 8356 [2048, 1024]

private theorem l3OMOd_red_pm8357 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8357 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12813) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 326 l3OMOdPmReshapeA1
    12813 8357 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12813 8357 [2048, 1024]

private theorem l3OMOd_red_pm8368 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8368 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12824) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 323 l3OMOdPmReshapeB0
    12824 8368 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12824 8368 [2048, 1024]

private theorem l3OMOd_red_pm8369 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8369 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12825) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 327 l3OMOdPmReshapeB1
    12825 8369 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12825 8369 [2048, 1024]

private theorem l3OMOd_red_sm5142 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5142 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5141) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 146 l3OMOdSmViewA
    5141 5142 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5141 5142

private theorem l3OMOd_red_sm5146 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5146 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5145) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 147 l3OMOdSmViewB
    5145 5146 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5145 5146

private theorem l3OMOd_red_pm8362 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8362 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8360) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 337 l3OMOdPmViewA0
    8360 8362 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8360 8362

private theorem l3OMOd_red_pm8363 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8363 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8361) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 342 l3OMOdPmViewA1
    8361 8363 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8361 8363

private theorem l3OMOd_red_pm8374 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8374 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8372) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 338 l3OMOdPmViewB0
    8372 8374 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8372 8374

private theorem l3OMOd_red_pm8375 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8375 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8373) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 343 l3OMOdPmViewB1
    8373 8375 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8373 8375

private theorem l3OMOd_red_sm5148 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5148 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5147) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 151 l3OMOdSmReshapeDown
    5147 5148 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5147 5148 [4096, 512]

private theorem l3OMOd_red_pm8382 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8382 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8380) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 350 l3OMOdPmReshapeDown0
    8380 8382 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 8380 8382 [2048, 512]

private theorem l3OMOd_red_pm8383 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8383 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8381) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 353 l3OMOdPmReshapeDown1
    8381 8383 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 8381 8383 [2048, 512]

private theorem l3OMOd_red_sm5151 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5151 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5150) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 153 l3OMOdSmViewDown
    5150 5151 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5150 5151

private theorem l3OMOd_red_pm8390 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8390 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8388) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 358 l3OMOdPmViewDown0
    8388 8390 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 8388 8390

private theorem l3OMOd_red_pm8391 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8391 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8389) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 359 l3OMOdPmViewDown1
    8389 8391 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 8389 8391

private theorem l3OMOd_red_sm5141 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5141 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5139)
        (denoteGraphDistributedFaithful sm_goal_1 init 5140) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 142 l3OMOdSmLinearA
    5139 5140 5141 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5139 5140 5141

private theorem l3OMOd_red_sm5145 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5145 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5143)
        (denoteGraphDistributedFaithful sm_goal_1 init 5144) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 143 l3OMOdSmLinearB
    5143 5144 5145 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5143 5144 5145

private theorem l3OMOd_red_pm8360 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8360 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8356)
        (denoteGraphDistributedFaithful pm_goal_1 init 5140) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 329 l3OMOdPmLinearA0
    8356 5140 8360 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8356 5140 8360

private theorem l3OMOd_red_pm8361 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8361 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8357)
        (denoteGraphDistributedFaithful pm_goal_1 init 5140) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 334 l3OMOdPmLinearA1
    8357 5140 8361 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8357 5140 8361

private theorem l3OMOd_red_pm8372 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8372 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8368)
        (denoteGraphDistributedFaithful pm_goal_1 init 5144) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 330 l3OMOdPmLinearB0
    8368 5144 8372 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8368 5144 8372

private theorem l3OMOd_red_pm8373 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8373 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8369)
        (denoteGraphDistributedFaithful pm_goal_1 init 5144) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 335 l3OMOdPmLinearB1
    8369 5144 8373 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8369 5144 8373

private theorem l3OMOd_red_sm5147 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5147 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5142)
        (denoteGraphDistributedFaithful sm_goal_1 init 5146) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 150 l3OMOdSmSwi
    5142 5146 5147 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5142 5146 5147

private theorem l3OMOd_red_pm8380 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8380 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8362)
        (denoteGraphDistributedFaithful pm_goal_1 init 8374) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 345 l3OMOdPmSwi0
    8362 8374 8380 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 8362 8374 8380

private theorem l3OMOd_red_pm8381 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8381 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8363)
        (denoteGraphDistributedFaithful pm_goal_1 init 8375) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 349 l3OMOdPmSwi1
    8363 8375 8381 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 8363 8375 8381

private theorem l3OMOd_red_sm5150 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5150 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5148)
        (denoteGraphDistributedFaithful sm_goal_1 init 5149) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 152 l3OMOdSmLinearDown
    5148 5149 5150 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5148 5149 5150

private theorem l3OMOd_red_pm8388 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8388 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8382)
        (denoteGraphDistributedFaithful pm_goal_1 init 5149) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 354 l3OMOdPmLinearDown0
    8382 5149 8388 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8382 5149 8388

private theorem l3OMOd_red_pm8389 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8389 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8383)
        (denoteGraphDistributedFaithful pm_goal_1 init 5149) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 357 l3OMOdPmLinearDown1
    8383 5149 8389 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8383 5149 8389

private theorem l3OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l3OMOd_weight_eq (initSM initPM : Store)
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
  rw [l3OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l3OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l3OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l3OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l3OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l3OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5151 ↔ 8390/8391` ordinary relation. -/
theorem l3_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5147)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8380)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8381)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5151)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8390)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8391)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5148)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8382)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8383)
      [4096, 512] [2048, 512] := by
    rw [l3OMOd_red_sm5148 initSM, l3OMOd_red_pm8382 initPM, l3OMOd_red_pm8383 initPM]
    exact ordinary_view hSwi
  have hwD := l3OMOd_weight_eq initSM initPM hInit initGoal_5149 (by native_decide)
    5149 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l3OMOd_weight_shape initPM hPM 5149 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5150)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8388)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8389)
      [4096, 1024] [2048, 1024] := by
    rw [l3OMOd_red_sm5150 initSM, l3OMOd_red_pm8388 initPM,
      l3OMOd_red_pm8389 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l3OMOd_red_sm5151 initSM, l3OMOd_red_pm8390 initPM, l3OMOd_red_pm8391 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l3_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5124)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8325)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5151)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8390)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8391)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5139)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8356)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8357)
      [4096, 1024] [2048, 1024] := by
    rw [l3OMOd_red_sm5139 initSM, l3OMOd_red_pm8356 initPM,
      l3OMOd_red_pm8357 initPM, l3OMOd_red_sm12812 initSM,
      l3OMOd_red_pm12812 initPM, l3OMOd_red_pm12813 initPM]
    exact ordinary_view hNorm
  have hwA := l3OMOd_weight_eq initSM initPM hInit initGoal_5140 (by native_decide)
    5140 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l3OMOd_weight_shape initPM hPM 5140 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5141)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8360)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8361)
      [4096, 512] [2048, 512] := by
    rw [l3OMOd_red_sm5141 initSM, l3OMOd_red_pm8360 initPM,
      l3OMOd_red_pm8361 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5142)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8362)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8363)
      [4096, 512] [2048, 512] := by
    rw [l3OMOd_red_sm5142 initSM, l3OMOd_red_pm8362 initPM,
      l3OMOd_red_pm8363 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5143)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8368)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8369)
      [4096, 1024] [2048, 1024] := by
    rw [l3OMOd_red_sm5143 initSM, l3OMOd_red_pm8368 initPM,
      l3OMOd_red_pm8369 initPM, l3OMOd_red_sm12824 initSM,
      l3OMOd_red_pm12824 initPM, l3OMOd_red_pm12825 initPM]
    exact ordinary_view hNorm
  have hwB := l3OMOd_weight_eq initSM initPM hInit initGoal_5144 (by native_decide)
    5144 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l3OMOd_weight_shape initPM hPM 5144 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5145)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8372)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8373)
      [4096, 512] [2048, 512] := by
    rw [l3OMOd_red_sm5145 initSM, l3OMOd_red_pm8372 initPM,
      l3OMOd_red_pm8373 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5146)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8374)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8375)
      [4096, 512] [2048, 512] := by
    rw [l3OMOd_red_sm5146 initSM, l3OMOd_red_pm8374 initPM,
      l3OMOd_red_pm8375 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5147)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8380)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8381)
      [4096, 512] [2048, 512] := by
    rw [l3OMOd_red_sm5147 initSM, l3OMOd_red_pm8380 initPM,
      l3OMOd_red_pm8381 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l3_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l3_ordinary_moe_down_from_swiglu
#print axioms l3_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
