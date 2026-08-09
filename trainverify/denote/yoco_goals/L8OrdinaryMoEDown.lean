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

private def l8OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5399], outs := [8192, 8196, 8200, 8204, 8208], params := [5] }

private def l8OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9144], outs := [15360, 13418, 13428, 13442, 13454], params := [5] }

private def l8OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9145], outs := [15362, 13419, 13429, 13443, 13455], params := [5] }

private def l8OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8204], outs := [5414], params := [4096, 1024] }

private def l8OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8208], outs := [5418], params := [4096, 1024] }

private def l8OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13442], outs := [9176], params := [2048, 1024] }

private def l8OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13443], outs := [9177], params := [2048, 1024] }

private def l8OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13454], outs := [9188], params := [2048, 1024] }

private def l8OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13455], outs := [9189], params := [2048, 1024] }

private def l8OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5414, 5415], outs := [5416] }

private def l8OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5418, 5419], outs := [5420] }

private def l8OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9176, 5415], outs := [9180] }

private def l8OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9177, 5415], outs := [9181] }

private def l8OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9188, 5419], outs := [9192] }

private def l8OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9189, 5419], outs := [9193] }

private def l8OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5416], outs := [5417], params := [4096, 512] }

private def l8OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5420], outs := [5421], params := [4096, 512] }

private def l8OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9180], outs := [9182], params := [2048, 512] }

private def l8OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9181], outs := [9183], params := [2048, 512] }

private def l8OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9192], outs := [9194], params := [2048, 512] }

private def l8OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9193], outs := [9195], params := [2048, 512] }

private def l8OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5417, 5421], outs := [5422] }

private def l8OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9182, 9194], outs := [9200] }

private def l8OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9183, 9195], outs := [9201] }

private def l8OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5422], outs := [5423], params := [4096, 512] }

private def l8OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9200], outs := [9202], params := [2048, 512] }

private def l8OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9201], outs := [9203], params := [2048, 512] }

private def l8OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5423, 5424], outs := [5425] }

private def l8OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9202, 5424], outs := [9208] }

private def l8OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9203, 5424], outs := [9209] }

private def l8OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5425], outs := [5426], params := [4096, 1024] }

private def l8OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9208], outs := [9210], params := [2048, 1024] }

private def l8OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9209], outs := [9211], params := [2048, 1024] }

private theorem l8OMOd_red_sm13442 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8204 =
      denoteGraphDistributedFaithful sm_goal_1 init 5399 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 330 l8OMOdSmRef
    5399 8204 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5399 [8192, 8196, 8200, 8204, 8208] 5 rfl 8204 (by decide)

private theorem l8OMOd_red_sm13454 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8208 =
      denoteGraphDistributedFaithful sm_goal_1 init 5399 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 330 l8OMOdSmRef
    5399 8208 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5399 [8192, 8196, 8200, 8204, 8208] 5 rfl 8208 (by decide)

private theorem l8OMOd_red_pm13442 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13442 =
      denoteGraphDistributedFaithful pm_goal_1 init 9144 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 739 l8OMOdPmRef0
    9144 13442 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9144 [15360, 13418, 13428, 13442, 13454] 5 rfl 13442 (by decide)

private theorem l8OMOd_red_pm13454 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13454 =
      denoteGraphDistributedFaithful pm_goal_1 init 9144 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 739 l8OMOdPmRef0
    9144 13454 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9144 [15360, 13418, 13428, 13442, 13454] 5 rfl 13454 (by decide)

private theorem l8OMOd_red_pm13443 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13443 =
      denoteGraphDistributedFaithful pm_goal_1 init 9145 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 740 l8OMOdPmRef1
    9145 13443 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9145 [15362, 13419, 13429, 13443, 13455] 5 rfl 13443 (by decide)

private theorem l8OMOd_red_pm13455 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13455 =
      denoteGraphDistributedFaithful pm_goal_1 init 9145 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 740 l8OMOdPmRef1
    9145 13455 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9145 [15362, 13419, 13429, 13443, 13455] 5 rfl 13455 (by decide)

private theorem l8OMOd_red_sm5414 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5414 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8204) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 333 l8OMOdSmReshapeA
    8204 5414 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8204 5414 [4096, 1024]

private theorem l8OMOd_red_sm5418 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5418 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8208) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 334 l8OMOdSmReshapeB
    8208 5418 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8208 5418 [4096, 1024]

private theorem l8OMOd_red_pm9176 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9176 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13442) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 742 l8OMOdPmReshapeA0
    13442 9176 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13442 9176 [2048, 1024]

private theorem l8OMOd_red_pm9177 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9177 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13443) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 746 l8OMOdPmReshapeA1
    13443 9177 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13443 9177 [2048, 1024]

private theorem l8OMOd_red_pm9188 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9188 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13454) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 743 l8OMOdPmReshapeB0
    13454 9188 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13454 9188 [2048, 1024]

private theorem l8OMOd_red_pm9189 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9189 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13455) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 747 l8OMOdPmReshapeB1
    13455 9189 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13455 9189 [2048, 1024]

private theorem l8OMOd_red_sm5417 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5417 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5416) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 341 l8OMOdSmViewA
    5416 5417 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5416 5417

private theorem l8OMOd_red_sm5421 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5421 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5420) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 342 l8OMOdSmViewB
    5420 5421 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5420 5421

private theorem l8OMOd_red_pm9182 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9182 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9180) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 757 l8OMOdPmViewA0
    9180 9182 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9180 9182

private theorem l8OMOd_red_pm9183 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9183 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9181) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 762 l8OMOdPmViewA1
    9181 9183 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9181 9183

private theorem l8OMOd_red_pm9194 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9194 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9192) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 758 l8OMOdPmViewB0
    9192 9194 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9192 9194

private theorem l8OMOd_red_pm9195 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9195 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9193) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 763 l8OMOdPmViewB1
    9193 9195 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9193 9195

private theorem l8OMOd_red_sm5423 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5423 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5422) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 346 l8OMOdSmReshapeDown
    5422 5423 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5422 5423 [4096, 512]

private theorem l8OMOd_red_pm9202 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9202 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9200) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 770 l8OMOdPmReshapeDown0
    9200 9202 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9200 9202 [2048, 512]

private theorem l8OMOd_red_pm9203 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9203 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9201) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 773 l8OMOdPmReshapeDown1
    9201 9203 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9201 9203 [2048, 512]

private theorem l8OMOd_red_sm5426 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5426 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5425) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 348 l8OMOdSmViewDown
    5425 5426 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5425 5426

private theorem l8OMOd_red_pm9210 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9210 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9208) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 778 l8OMOdPmViewDown0
    9208 9210 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9208 9210

private theorem l8OMOd_red_pm9211 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9211 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9209) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 779 l8OMOdPmViewDown1
    9209 9211 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9209 9211

private theorem l8OMOd_red_sm5416 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5416 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5414)
        (denoteGraphDistributedFaithful sm_goal_1 init 5415) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 337 l8OMOdSmLinearA
    5414 5415 5416 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5414 5415 5416

private theorem l8OMOd_red_sm5420 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5420 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5418)
        (denoteGraphDistributedFaithful sm_goal_1 init 5419) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 338 l8OMOdSmLinearB
    5418 5419 5420 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5418 5419 5420

private theorem l8OMOd_red_pm9180 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9180 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9176)
        (denoteGraphDistributedFaithful pm_goal_1 init 5415) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 749 l8OMOdPmLinearA0
    9176 5415 9180 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9176 5415 9180

private theorem l8OMOd_red_pm9181 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9181 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9177)
        (denoteGraphDistributedFaithful pm_goal_1 init 5415) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 754 l8OMOdPmLinearA1
    9177 5415 9181 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9177 5415 9181

private theorem l8OMOd_red_pm9192 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9192 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9188)
        (denoteGraphDistributedFaithful pm_goal_1 init 5419) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 750 l8OMOdPmLinearB0
    9188 5419 9192 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9188 5419 9192

private theorem l8OMOd_red_pm9193 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9193 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9189)
        (denoteGraphDistributedFaithful pm_goal_1 init 5419) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 755 l8OMOdPmLinearB1
    9189 5419 9193 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9189 5419 9193

private theorem l8OMOd_red_sm5422 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5422 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5417)
        (denoteGraphDistributedFaithful sm_goal_1 init 5421) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 345 l8OMOdSmSwi
    5417 5421 5422 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5417 5421 5422

private theorem l8OMOd_red_pm9200 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9200 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9182)
        (denoteGraphDistributedFaithful pm_goal_1 init 9194) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 765 l8OMOdPmSwi0
    9182 9194 9200 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9182 9194 9200

private theorem l8OMOd_red_pm9201 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9201 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9183)
        (denoteGraphDistributedFaithful pm_goal_1 init 9195) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 769 l8OMOdPmSwi1
    9183 9195 9201 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9183 9195 9201

private theorem l8OMOd_red_sm5425 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5425 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5423)
        (denoteGraphDistributedFaithful sm_goal_1 init 5424) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 347 l8OMOdSmLinearDown
    5423 5424 5425 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5423 5424 5425

private theorem l8OMOd_red_pm9208 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9208 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9202)
        (denoteGraphDistributedFaithful pm_goal_1 init 5424) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 774 l8OMOdPmLinearDown0
    9202 5424 9208 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9202 5424 9208

private theorem l8OMOd_red_pm9209 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9209 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9203)
        (denoteGraphDistributedFaithful pm_goal_1 init 5424) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 777 l8OMOdPmLinearDown1
    9203 5424 9209 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9203 5424 9209

private theorem l8OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l8OMOd_weight_eq (initSM initPM : Store)
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
  rw [l8OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l8OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l8OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l8OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l8OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l8OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5426 ↔ 9210/9211` ordinary relation. -/
theorem l8_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5422)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9201)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5426)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9211)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5423)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9203)
      [4096, 512] [2048, 512] := by
    rw [l8OMOd_red_sm5423 initSM, l8OMOd_red_pm9202 initPM, l8OMOd_red_pm9203 initPM]
    exact ordinary_view hSwi
  have hwD := l8OMOd_weight_eq initSM initPM hInit initGoal_5424 (by native_decide)
    5424 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l8OMOd_weight_shape initPM hPM 5424 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5425)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9208)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9209)
      [4096, 1024] [2048, 1024] := by
    rw [l8OMOd_red_sm5425 initSM, l8OMOd_red_pm9208 initPM,
      l8OMOd_red_pm9209 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l8OMOd_red_sm5426 initSM, l8OMOd_red_pm9210 initPM, l8OMOd_red_pm9211 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l8_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5399)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9144)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9145)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5426)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9211)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5414)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9176)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9177)
      [4096, 1024] [2048, 1024] := by
    rw [l8OMOd_red_sm5414 initSM, l8OMOd_red_pm9176 initPM,
      l8OMOd_red_pm9177 initPM, l8OMOd_red_sm13442 initSM,
      l8OMOd_red_pm13442 initPM, l8OMOd_red_pm13443 initPM]
    exact ordinary_view hNorm
  have hwA := l8OMOd_weight_eq initSM initPM hInit initGoal_5415 (by native_decide)
    5415 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l8OMOd_weight_shape initPM hPM 5415 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5416)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9180)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9181)
      [4096, 512] [2048, 512] := by
    rw [l8OMOd_red_sm5416 initSM, l8OMOd_red_pm9180 initPM,
      l8OMOd_red_pm9181 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5417)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9182)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9183)
      [4096, 512] [2048, 512] := by
    rw [l8OMOd_red_sm5417 initSM, l8OMOd_red_pm9182 initPM,
      l8OMOd_red_pm9183 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5418)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9188)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9189)
      [4096, 1024] [2048, 1024] := by
    rw [l8OMOd_red_sm5418 initSM, l8OMOd_red_pm9188 initPM,
      l8OMOd_red_pm9189 initPM, l8OMOd_red_sm13454 initSM,
      l8OMOd_red_pm13454 initPM, l8OMOd_red_pm13455 initPM]
    exact ordinary_view hNorm
  have hwB := l8OMOd_weight_eq initSM initPM hInit initGoal_5419 (by native_decide)
    5419 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l8OMOd_weight_shape initPM hPM 5419 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5420)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9192)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9193)
      [4096, 512] [2048, 512] := by
    rw [l8OMOd_red_sm5420 initSM, l8OMOd_red_pm9192 initPM,
      l8OMOd_red_pm9193 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5421)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9194)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9195)
      [4096, 512] [2048, 512] := by
    rw [l8OMOd_red_sm5421 initSM, l8OMOd_red_pm9194 initPM,
      l8OMOd_red_pm9195 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5422)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9201)
      [4096, 512] [2048, 512] := by
    rw [l8OMOd_red_sm5422 initSM, l8OMOd_red_pm9200 initPM,
      l8OMOd_red_pm9201 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l8_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l8_ordinary_moe_down_from_swiglu
#print axioms l8_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
