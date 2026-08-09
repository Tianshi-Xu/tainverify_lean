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

private def l5OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5234], outs := [8036, 8040, 8044, 8048, 8052], params := [5] }

private def l5OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8652], outs := [15336, 13040, 13050, 13064, 13076], params := [5] }

private def l5OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8653], outs := [15338, 13041, 13051, 13065, 13077], params := [5] }

private def l5OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8048], outs := [5249], params := [4096, 1024] }

private def l5OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8052], outs := [5253], params := [4096, 1024] }

private def l5OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13064], outs := [8684], params := [2048, 1024] }

private def l5OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13065], outs := [8685], params := [2048, 1024] }

private def l5OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13076], outs := [8696], params := [2048, 1024] }

private def l5OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13077], outs := [8697], params := [2048, 1024] }

private def l5OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5249, 5250], outs := [5251] }

private def l5OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5253, 5254], outs := [5255] }

private def l5OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8684, 5250], outs := [8688] }

private def l5OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8685, 5250], outs := [8689] }

private def l5OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8696, 5254], outs := [8700] }

private def l5OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8697, 5254], outs := [8701] }

private def l5OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5251], outs := [5252], params := [4096, 512] }

private def l5OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5255], outs := [5256], params := [4096, 512] }

private def l5OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8688], outs := [8690], params := [2048, 512] }

private def l5OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8689], outs := [8691], params := [2048, 512] }

private def l5OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8700], outs := [8702], params := [2048, 512] }

private def l5OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8701], outs := [8703], params := [2048, 512] }

private def l5OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5252, 5256], outs := [5257] }

private def l5OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [8690, 8702], outs := [8708] }

private def l5OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [8691, 8703], outs := [8709] }

private def l5OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5257], outs := [5258], params := [4096, 512] }

private def l5OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8708], outs := [8710], params := [2048, 512] }

private def l5OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [8709], outs := [8711], params := [2048, 512] }

private def l5OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5258, 5259], outs := [5260] }

private def l5OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8710, 5259], outs := [8716] }

private def l5OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8711, 5259], outs := [8717] }

private def l5OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5260], outs := [5261], params := [4096, 1024] }

private def l5OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8716], outs := [8718], params := [2048, 1024] }

private def l5OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8717], outs := [8719], params := [2048, 1024] }

private theorem l5OMOd_red_sm13064 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8048 =
      denoteGraphDistributedFaithful sm_goal_1 init 5234 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 213 l5OMOdSmRef
    5234 8048 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5234 [8036, 8040, 8044, 8048, 8052] 5 rfl 8048 (by decide)

private theorem l5OMOd_red_sm13076 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8052 =
      denoteGraphDistributedFaithful sm_goal_1 init 5234 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 213 l5OMOdSmRef
    5234 8052 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5234 [8036, 8040, 8044, 8048, 8052] 5 rfl 8052 (by decide)

private theorem l5OMOd_red_pm13064 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13064 =
      denoteGraphDistributedFaithful pm_goal_1 init 8652 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 487 l5OMOdPmRef0
    8652 13064 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8652 [15336, 13040, 13050, 13064, 13076] 5 rfl 13064 (by decide)

private theorem l5OMOd_red_pm13076 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13076 =
      denoteGraphDistributedFaithful pm_goal_1 init 8652 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 487 l5OMOdPmRef0
    8652 13076 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8652 [15336, 13040, 13050, 13064, 13076] 5 rfl 13076 (by decide)

private theorem l5OMOd_red_pm13065 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13065 =
      denoteGraphDistributedFaithful pm_goal_1 init 8653 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 488 l5OMOdPmRef1
    8653 13065 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8653 [15338, 13041, 13051, 13065, 13077] 5 rfl 13065 (by decide)

private theorem l5OMOd_red_pm13077 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13077 =
      denoteGraphDistributedFaithful pm_goal_1 init 8653 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 488 l5OMOdPmRef1
    8653 13077 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8653 [15338, 13041, 13051, 13065, 13077] 5 rfl 13077 (by decide)

private theorem l5OMOd_red_sm5249 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5249 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8048) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 216 l5OMOdSmReshapeA
    8048 5249 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8048 5249 [4096, 1024]

private theorem l5OMOd_red_sm5253 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5253 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8052) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 217 l5OMOdSmReshapeB
    8052 5253 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8052 5253 [4096, 1024]

private theorem l5OMOd_red_pm8684 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8684 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13064) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 490 l5OMOdPmReshapeA0
    13064 8684 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13064 8684 [2048, 1024]

private theorem l5OMOd_red_pm8685 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8685 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13065) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 494 l5OMOdPmReshapeA1
    13065 8685 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13065 8685 [2048, 1024]

private theorem l5OMOd_red_pm8696 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8696 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13076) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 491 l5OMOdPmReshapeB0
    13076 8696 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13076 8696 [2048, 1024]

private theorem l5OMOd_red_pm8697 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8697 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13077) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 495 l5OMOdPmReshapeB1
    13077 8697 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13077 8697 [2048, 1024]

private theorem l5OMOd_red_sm5252 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5252 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5251) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 224 l5OMOdSmViewA
    5251 5252 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5251 5252

private theorem l5OMOd_red_sm5256 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5256 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5255) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 225 l5OMOdSmViewB
    5255 5256 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5255 5256

private theorem l5OMOd_red_pm8690 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8690 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8688) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 505 l5OMOdPmViewA0
    8688 8690 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8688 8690

private theorem l5OMOd_red_pm8691 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8691 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8689) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 510 l5OMOdPmViewA1
    8689 8691 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8689 8691

private theorem l5OMOd_red_pm8702 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8702 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8700) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 506 l5OMOdPmViewB0
    8700 8702 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8700 8702

private theorem l5OMOd_red_pm8703 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8703 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8701) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 511 l5OMOdPmViewB1
    8701 8703 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8701 8703

private theorem l5OMOd_red_sm5258 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5258 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5257) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 229 l5OMOdSmReshapeDown
    5257 5258 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5257 5258 [4096, 512]

private theorem l5OMOd_red_pm8710 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8710 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8708) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 518 l5OMOdPmReshapeDown0
    8708 8710 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 8708 8710 [2048, 512]

private theorem l5OMOd_red_pm8711 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8711 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8709) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 521 l5OMOdPmReshapeDown1
    8709 8711 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 8709 8711 [2048, 512]

private theorem l5OMOd_red_sm5261 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5261 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5260) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 231 l5OMOdSmViewDown
    5260 5261 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5260 5261

private theorem l5OMOd_red_pm8718 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8718 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8716) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 526 l5OMOdPmViewDown0
    8716 8718 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 8716 8718

private theorem l5OMOd_red_pm8719 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8719 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8717) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 527 l5OMOdPmViewDown1
    8717 8719 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 8717 8719

private theorem l5OMOd_red_sm5251 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5251 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5249)
        (denoteGraphDistributedFaithful sm_goal_1 init 5250) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 220 l5OMOdSmLinearA
    5249 5250 5251 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5249 5250 5251

private theorem l5OMOd_red_sm5255 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5255 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5253)
        (denoteGraphDistributedFaithful sm_goal_1 init 5254) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 221 l5OMOdSmLinearB
    5253 5254 5255 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5253 5254 5255

private theorem l5OMOd_red_pm8688 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8688 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8684)
        (denoteGraphDistributedFaithful pm_goal_1 init 5250) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 497 l5OMOdPmLinearA0
    8684 5250 8688 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8684 5250 8688

private theorem l5OMOd_red_pm8689 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8689 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8685)
        (denoteGraphDistributedFaithful pm_goal_1 init 5250) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 502 l5OMOdPmLinearA1
    8685 5250 8689 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8685 5250 8689

private theorem l5OMOd_red_pm8700 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8700 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8696)
        (denoteGraphDistributedFaithful pm_goal_1 init 5254) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 498 l5OMOdPmLinearB0
    8696 5254 8700 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8696 5254 8700

private theorem l5OMOd_red_pm8701 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8701 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8697)
        (denoteGraphDistributedFaithful pm_goal_1 init 5254) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 503 l5OMOdPmLinearB1
    8697 5254 8701 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8697 5254 8701

private theorem l5OMOd_red_sm5257 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5257 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5252)
        (denoteGraphDistributedFaithful sm_goal_1 init 5256) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 228 l5OMOdSmSwi
    5252 5256 5257 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5252 5256 5257

private theorem l5OMOd_red_pm8708 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8708 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8690)
        (denoteGraphDistributedFaithful pm_goal_1 init 8702) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 513 l5OMOdPmSwi0
    8690 8702 8708 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 8690 8702 8708

private theorem l5OMOd_red_pm8709 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8709 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8691)
        (denoteGraphDistributedFaithful pm_goal_1 init 8703) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 517 l5OMOdPmSwi1
    8691 8703 8709 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 8691 8703 8709

private theorem l5OMOd_red_sm5260 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5260 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5258)
        (denoteGraphDistributedFaithful sm_goal_1 init 5259) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 230 l5OMOdSmLinearDown
    5258 5259 5260 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5258 5259 5260

private theorem l5OMOd_red_pm8716 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8716 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8710)
        (denoteGraphDistributedFaithful pm_goal_1 init 5259) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 522 l5OMOdPmLinearDown0
    8710 5259 8716 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8710 5259 8716

private theorem l5OMOd_red_pm8717 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8717 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8711)
        (denoteGraphDistributedFaithful pm_goal_1 init 5259) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 525 l5OMOdPmLinearDown1
    8711 5259 8717 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8711 5259 8717

private theorem l5OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l5OMOd_weight_eq (initSM initPM : Store)
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
  rw [l5OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l5OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l5OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l5OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l5OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l5OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5261 ↔ 8718/8719` ordinary relation. -/
theorem l5_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5257)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8709)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5261)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8718)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8719)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5258)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8710)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8711)
      [4096, 512] [2048, 512] := by
    rw [l5OMOd_red_sm5258 initSM, l5OMOd_red_pm8710 initPM, l5OMOd_red_pm8711 initPM]
    exact ordinary_view hSwi
  have hwD := l5OMOd_weight_eq initSM initPM hInit initGoal_5259 (by native_decide)
    5259 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l5OMOd_weight_shape initPM hPM 5259 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5260)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8716)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8717)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMOd_red_sm5260 initSM, l5OMOd_red_pm8716 initPM,
      l5OMOd_red_pm8717 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l5OMOd_red_sm5261 initSM, l5OMOd_red_pm8718 initPM, l5OMOd_red_pm8719 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l5_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8653)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5261)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8718)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8719)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5249)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8684)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8685)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMOd_red_sm5249 initSM, l5OMOd_red_pm8684 initPM,
      l5OMOd_red_pm8685 initPM, l5OMOd_red_sm13064 initSM,
      l5OMOd_red_pm13064 initPM, l5OMOd_red_pm13065 initPM]
    exact ordinary_view hNorm
  have hwA := l5OMOd_weight_eq initSM initPM hInit initGoal_5250 (by native_decide)
    5250 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l5OMOd_weight_shape initPM hPM 5250 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5251)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8688)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8689)
      [4096, 512] [2048, 512] := by
    rw [l5OMOd_red_sm5251 initSM, l5OMOd_red_pm8688 initPM,
      l5OMOd_red_pm8689 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5252)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8690)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8691)
      [4096, 512] [2048, 512] := by
    rw [l5OMOd_red_sm5252 initSM, l5OMOd_red_pm8690 initPM,
      l5OMOd_red_pm8691 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5253)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8696)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8697)
      [4096, 1024] [2048, 1024] := by
    rw [l5OMOd_red_sm5253 initSM, l5OMOd_red_pm8696 initPM,
      l5OMOd_red_pm8697 initPM, l5OMOd_red_sm13076 initSM,
      l5OMOd_red_pm13076 initPM, l5OMOd_red_pm13077 initPM]
    exact ordinary_view hNorm
  have hwB := l5OMOd_weight_eq initSM initPM hInit initGoal_5254 (by native_decide)
    5254 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l5OMOd_weight_shape initPM hPM 5254 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8700)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8701)
      [4096, 512] [2048, 512] := by
    rw [l5OMOd_red_sm5255 initSM, l5OMOd_red_pm8700 initPM,
      l5OMOd_red_pm8701 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5256)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8703)
      [4096, 512] [2048, 512] := by
    rw [l5OMOd_red_sm5256 initSM, l5OMOd_red_pm8702 initPM,
      l5OMOd_red_pm8703 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5257)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8709)
      [4096, 512] [2048, 512] := by
    rw [l5OMOd_red_sm5257 initSM, l5OMOd_red_pm8708 initPM,
      l5OMOd_red_pm8709 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l5_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l5_ordinary_moe_down_from_swiglu
#print axioms l5_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
