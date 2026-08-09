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

private def l6OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5289], outs := [8088, 8092, 8096, 8100, 8104], params := [5] }

private def l6OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8816], outs := [15344, 13166, 13176, 13190, 13202], params := [5] }

private def l6OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8817], outs := [15346, 13167, 13177, 13191, 13203], params := [5] }

private def l6OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8100], outs := [5304], params := [4096, 1024] }

private def l6OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8104], outs := [5308], params := [4096, 1024] }

private def l6OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13190], outs := [8848], params := [2048, 1024] }

private def l6OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13191], outs := [8849], params := [2048, 1024] }

private def l6OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13202], outs := [8860], params := [2048, 1024] }

private def l6OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13203], outs := [8861], params := [2048, 1024] }

private def l6OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5304, 5305], outs := [5306] }

private def l6OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5308, 5309], outs := [5310] }

private def l6OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8848, 5305], outs := [8852] }

private def l6OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8849, 5305], outs := [8853] }

private def l6OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8860, 5309], outs := [8864] }

private def l6OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8861, 5309], outs := [8865] }

private def l6OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5306], outs := [5307], params := [4096, 512] }

private def l6OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5310], outs := [5311], params := [4096, 512] }

private def l6OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8852], outs := [8854], params := [2048, 512] }

private def l6OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8853], outs := [8855], params := [2048, 512] }

private def l6OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8864], outs := [8866], params := [2048, 512] }

private def l6OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8865], outs := [8867], params := [2048, 512] }

private def l6OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5307, 5311], outs := [5312] }

private def l6OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [8854, 8866], outs := [8872] }

private def l6OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [8855, 8867], outs := [8873] }

private def l6OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5312], outs := [5313], params := [4096, 512] }

private def l6OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8872], outs := [8874], params := [2048, 512] }

private def l6OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [8873], outs := [8875], params := [2048, 512] }

private def l6OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5313, 5314], outs := [5315] }

private def l6OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8874, 5314], outs := [8880] }

private def l6OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8875, 5314], outs := [8881] }

private def l6OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5315], outs := [5316], params := [4096, 1024] }

private def l6OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8880], outs := [8882], params := [2048, 1024] }

private def l6OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8881], outs := [8883], params := [2048, 1024] }

private theorem l6OMOd_red_sm13190 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8100 =
      denoteGraphDistributedFaithful sm_goal_1 init 5289 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 252 l6OMOdSmRef
    5289 8100 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5289 [8088, 8092, 8096, 8100, 8104] 5 rfl 8100 (by decide)

private theorem l6OMOd_red_sm13202 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8104 =
      denoteGraphDistributedFaithful sm_goal_1 init 5289 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 252 l6OMOdSmRef
    5289 8104 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5289 [8088, 8092, 8096, 8100, 8104] 5 rfl 8104 (by decide)

private theorem l6OMOd_red_pm13190 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13190 =
      denoteGraphDistributedFaithful pm_goal_1 init 8816 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 571 l6OMOdPmRef0
    8816 13190 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8816 [15344, 13166, 13176, 13190, 13202] 5 rfl 13190 (by decide)

private theorem l6OMOd_red_pm13202 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13202 =
      denoteGraphDistributedFaithful pm_goal_1 init 8816 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 571 l6OMOdPmRef0
    8816 13202 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8816 [15344, 13166, 13176, 13190, 13202] 5 rfl 13202 (by decide)

private theorem l6OMOd_red_pm13191 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13191 =
      denoteGraphDistributedFaithful pm_goal_1 init 8817 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 572 l6OMOdPmRef1
    8817 13191 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8817 [15346, 13167, 13177, 13191, 13203] 5 rfl 13191 (by decide)

private theorem l6OMOd_red_pm13203 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13203 =
      denoteGraphDistributedFaithful pm_goal_1 init 8817 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 572 l6OMOdPmRef1
    8817 13203 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8817 [15346, 13167, 13177, 13191, 13203] 5 rfl 13203 (by decide)

private theorem l6OMOd_red_sm5304 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5304 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8100) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 255 l6OMOdSmReshapeA
    8100 5304 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8100 5304 [4096, 1024]

private theorem l6OMOd_red_sm5308 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5308 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8104) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 256 l6OMOdSmReshapeB
    8104 5308 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8104 5308 [4096, 1024]

private theorem l6OMOd_red_pm8848 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8848 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13190) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 574 l6OMOdPmReshapeA0
    13190 8848 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13190 8848 [2048, 1024]

private theorem l6OMOd_red_pm8849 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8849 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13191) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 578 l6OMOdPmReshapeA1
    13191 8849 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13191 8849 [2048, 1024]

private theorem l6OMOd_red_pm8860 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8860 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13202) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 575 l6OMOdPmReshapeB0
    13202 8860 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13202 8860 [2048, 1024]

private theorem l6OMOd_red_pm8861 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8861 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13203) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 579 l6OMOdPmReshapeB1
    13203 8861 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13203 8861 [2048, 1024]

private theorem l6OMOd_red_sm5307 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5307 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5306) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 263 l6OMOdSmViewA
    5306 5307 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5306 5307

private theorem l6OMOd_red_sm5311 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5311 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5310) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 264 l6OMOdSmViewB
    5310 5311 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5310 5311

private theorem l6OMOd_red_pm8854 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8854 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8852) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 589 l6OMOdPmViewA0
    8852 8854 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8852 8854

private theorem l6OMOd_red_pm8855 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8855 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8853) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 594 l6OMOdPmViewA1
    8853 8855 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8853 8855

private theorem l6OMOd_red_pm8866 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8866 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8864) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 590 l6OMOdPmViewB0
    8864 8866 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8864 8866

private theorem l6OMOd_red_pm8867 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8867 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8865) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 595 l6OMOdPmViewB1
    8865 8867 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8865 8867

private theorem l6OMOd_red_sm5313 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5313 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5312) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 268 l6OMOdSmReshapeDown
    5312 5313 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5312 5313 [4096, 512]

private theorem l6OMOd_red_pm8874 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8874 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8872) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 602 l6OMOdPmReshapeDown0
    8872 8874 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 8872 8874 [2048, 512]

private theorem l6OMOd_red_pm8875 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8875 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8873) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 605 l6OMOdPmReshapeDown1
    8873 8875 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 8873 8875 [2048, 512]

private theorem l6OMOd_red_sm5316 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5316 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5315) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 270 l6OMOdSmViewDown
    5315 5316 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5315 5316

private theorem l6OMOd_red_pm8882 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8882 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8880) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 610 l6OMOdPmViewDown0
    8880 8882 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 8880 8882

private theorem l6OMOd_red_pm8883 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8883 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8881) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 611 l6OMOdPmViewDown1
    8881 8883 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 8881 8883

private theorem l6OMOd_red_sm5306 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5306 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5304)
        (denoteGraphDistributedFaithful sm_goal_1 init 5305) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 259 l6OMOdSmLinearA
    5304 5305 5306 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5304 5305 5306

private theorem l6OMOd_red_sm5310 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5310 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5308)
        (denoteGraphDistributedFaithful sm_goal_1 init 5309) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 260 l6OMOdSmLinearB
    5308 5309 5310 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5308 5309 5310

private theorem l6OMOd_red_pm8852 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8852 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8848)
        (denoteGraphDistributedFaithful pm_goal_1 init 5305) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 581 l6OMOdPmLinearA0
    8848 5305 8852 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8848 5305 8852

private theorem l6OMOd_red_pm8853 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8853 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8849)
        (denoteGraphDistributedFaithful pm_goal_1 init 5305) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 586 l6OMOdPmLinearA1
    8849 5305 8853 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8849 5305 8853

private theorem l6OMOd_red_pm8864 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8864 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8860)
        (denoteGraphDistributedFaithful pm_goal_1 init 5309) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 582 l6OMOdPmLinearB0
    8860 5309 8864 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8860 5309 8864

private theorem l6OMOd_red_pm8865 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8865 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8861)
        (denoteGraphDistributedFaithful pm_goal_1 init 5309) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 587 l6OMOdPmLinearB1
    8861 5309 8865 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8861 5309 8865

private theorem l6OMOd_red_sm5312 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5312 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5307)
        (denoteGraphDistributedFaithful sm_goal_1 init 5311) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 267 l6OMOdSmSwi
    5307 5311 5312 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5307 5311 5312

private theorem l6OMOd_red_pm8872 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8872 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8854)
        (denoteGraphDistributedFaithful pm_goal_1 init 8866) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 597 l6OMOdPmSwi0
    8854 8866 8872 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 8854 8866 8872

private theorem l6OMOd_red_pm8873 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8873 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8855)
        (denoteGraphDistributedFaithful pm_goal_1 init 8867) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 601 l6OMOdPmSwi1
    8855 8867 8873 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 8855 8867 8873

private theorem l6OMOd_red_sm5315 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5315 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5313)
        (denoteGraphDistributedFaithful sm_goal_1 init 5314) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 269 l6OMOdSmLinearDown
    5313 5314 5315 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5313 5314 5315

private theorem l6OMOd_red_pm8880 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8880 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8874)
        (denoteGraphDistributedFaithful pm_goal_1 init 5314) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 606 l6OMOdPmLinearDown0
    8874 5314 8880 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8874 5314 8880

private theorem l6OMOd_red_pm8881 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8881 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8875)
        (denoteGraphDistributedFaithful pm_goal_1 init 5314) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 609 l6OMOdPmLinearDown1
    8875 5314 8881 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8875 5314 8881

private theorem l6OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l6OMOd_weight_eq (initSM initPM : Store)
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
  rw [l6OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l6OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l6OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l6OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l6OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l6OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5316 ↔ 8882/8883` ordinary relation. -/
theorem l6_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5312)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8872)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8873)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5316)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8883)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5313)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8874)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8875)
      [4096, 512] [2048, 512] := by
    rw [l6OMOd_red_sm5313 initSM, l6OMOd_red_pm8874 initPM, l6OMOd_red_pm8875 initPM]
    exact ordinary_view hSwi
  have hwD := l6OMOd_weight_eq initSM initPM hInit initGoal_5314 (by native_decide)
    5314 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l6OMOd_weight_shape initPM hPM 5314 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5315)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8880)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8881)
      [4096, 1024] [2048, 1024] := by
    rw [l6OMOd_red_sm5315 initSM, l6OMOd_red_pm8880 initPM,
      l6OMOd_red_pm8881 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l6OMOd_red_sm5316 initSM, l6OMOd_red_pm8882 initPM, l6OMOd_red_pm8883 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l6_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5289)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8816)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8817)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5316)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8883)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5304)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8848)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8849)
      [4096, 1024] [2048, 1024] := by
    rw [l6OMOd_red_sm5304 initSM, l6OMOd_red_pm8848 initPM,
      l6OMOd_red_pm8849 initPM, l6OMOd_red_sm13190 initSM,
      l6OMOd_red_pm13190 initPM, l6OMOd_red_pm13191 initPM]
    exact ordinary_view hNorm
  have hwA := l6OMOd_weight_eq initSM initPM hInit initGoal_5305 (by native_decide)
    5305 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l6OMOd_weight_shape initPM hPM 5305 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5306)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8852)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8853)
      [4096, 512] [2048, 512] := by
    rw [l6OMOd_red_sm5306 initSM, l6OMOd_red_pm8852 initPM,
      l6OMOd_red_pm8853 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5307)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8854)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8855)
      [4096, 512] [2048, 512] := by
    rw [l6OMOd_red_sm5307 initSM, l6OMOd_red_pm8854 initPM,
      l6OMOd_red_pm8855 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5308)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8860)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8861)
      [4096, 1024] [2048, 1024] := by
    rw [l6OMOd_red_sm5308 initSM, l6OMOd_red_pm8860 initPM,
      l6OMOd_red_pm8861 initPM, l6OMOd_red_sm13202 initSM,
      l6OMOd_red_pm13202 initPM, l6OMOd_red_pm13203 initPM]
    exact ordinary_view hNorm
  have hwB := l6OMOd_weight_eq initSM initPM hInit initGoal_5309 (by native_decide)
    5309 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l6OMOd_weight_shape initPM hPM 5309 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5310)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8864)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8865)
      [4096, 512] [2048, 512] := by
    rw [l6OMOd_red_sm5310 initSM, l6OMOd_red_pm8864 initPM,
      l6OMOd_red_pm8865 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5311)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8866)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8867)
      [4096, 512] [2048, 512] := by
    rw [l6OMOd_red_sm5311 initSM, l6OMOd_red_pm8866 initPM,
      l6OMOd_red_pm8867 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5312)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8872)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8873)
      [4096, 512] [2048, 512] := by
    rw [l6OMOd_red_sm5312 initSM, l6OMOd_red_pm8872 initPM,
      l6OMOd_red_pm8873 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l6_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l6_ordinary_moe_down_from_swiglu
#print axioms l6_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
