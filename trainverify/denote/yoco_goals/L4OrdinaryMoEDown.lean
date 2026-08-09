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

private def l4OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5179], outs := [7984, 7988, 7992, 7996, 8000], params := [5] }

private def l4OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8488], outs := [15328, 12914, 12924, 12938, 12950], params := [5] }

private def l4OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8489], outs := [15330, 12915, 12925, 12939, 12951], params := [5] }

private def l4OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7996], outs := [5194], params := [4096, 1024] }

private def l4OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8000], outs := [5198], params := [4096, 1024] }

private def l4OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12938], outs := [8520], params := [2048, 1024] }

private def l4OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12939], outs := [8521], params := [2048, 1024] }

private def l4OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12950], outs := [8532], params := [2048, 1024] }

private def l4OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12951], outs := [8533], params := [2048, 1024] }

private def l4OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5194, 5195], outs := [5196] }

private def l4OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5198, 5199], outs := [5200] }

private def l4OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8520, 5195], outs := [8524] }

private def l4OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8521, 5195], outs := [8525] }

private def l4OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8532, 5199], outs := [8536] }

private def l4OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8533, 5199], outs := [8537] }

private def l4OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5196], outs := [5197], params := [4096, 512] }

private def l4OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5200], outs := [5201], params := [4096, 512] }

private def l4OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8524], outs := [8526], params := [2048, 512] }

private def l4OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8525], outs := [8527], params := [2048, 512] }

private def l4OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8536], outs := [8538], params := [2048, 512] }

private def l4OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8537], outs := [8539], params := [2048, 512] }

private def l4OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5197, 5201], outs := [5202] }

private def l4OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [8526, 8538], outs := [8544] }

private def l4OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [8527, 8539], outs := [8545] }

private def l4OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5202], outs := [5203], params := [4096, 512] }

private def l4OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8544], outs := [8546], params := [2048, 512] }

private def l4OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [8545], outs := [8547], params := [2048, 512] }

private def l4OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5203, 5204], outs := [5205] }

private def l4OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8546, 5204], outs := [8552] }

private def l4OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8547, 5204], outs := [8553] }

private def l4OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5205], outs := [5206], params := [4096, 1024] }

private def l4OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8552], outs := [8554], params := [2048, 1024] }

private def l4OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8553], outs := [8555], params := [2048, 1024] }

private theorem l4OMOd_red_sm12938 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7996 =
      denoteGraphDistributedFaithful sm_goal_1 init 5179 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 174 l4OMOdSmRef
    5179 7996 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5179 [7984, 7988, 7992, 7996, 8000] 5 rfl 7996 (by decide)

private theorem l4OMOd_red_sm12950 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8000 =
      denoteGraphDistributedFaithful sm_goal_1 init 5179 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 174 l4OMOdSmRef
    5179 8000 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5179 [7984, 7988, 7992, 7996, 8000] 5 rfl 8000 (by decide)

private theorem l4OMOd_red_pm12938 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12938 =
      denoteGraphDistributedFaithful pm_goal_1 init 8488 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 403 l4OMOdPmRef0
    8488 12938 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8488 [15328, 12914, 12924, 12938, 12950] 5 rfl 12938 (by decide)

private theorem l4OMOd_red_pm12950 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12950 =
      denoteGraphDistributedFaithful pm_goal_1 init 8488 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 403 l4OMOdPmRef0
    8488 12950 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8488 [15328, 12914, 12924, 12938, 12950] 5 rfl 12950 (by decide)

private theorem l4OMOd_red_pm12939 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12939 =
      denoteGraphDistributedFaithful pm_goal_1 init 8489 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 404 l4OMOdPmRef1
    8489 12939 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8489 [15330, 12915, 12925, 12939, 12951] 5 rfl 12939 (by decide)

private theorem l4OMOd_red_pm12951 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12951 =
      denoteGraphDistributedFaithful pm_goal_1 init 8489 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 404 l4OMOdPmRef1
    8489 12951 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8489 [15330, 12915, 12925, 12939, 12951] 5 rfl 12951 (by decide)

private theorem l4OMOd_red_sm5194 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5194 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7996) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 177 l4OMOdSmReshapeA
    7996 5194 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7996 5194 [4096, 1024]

private theorem l4OMOd_red_sm5198 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5198 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8000) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 178 l4OMOdSmReshapeB
    8000 5198 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8000 5198 [4096, 1024]

private theorem l4OMOd_red_pm8520 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8520 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12938) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 406 l4OMOdPmReshapeA0
    12938 8520 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12938 8520 [2048, 1024]

private theorem l4OMOd_red_pm8521 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8521 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12939) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 410 l4OMOdPmReshapeA1
    12939 8521 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12939 8521 [2048, 1024]

private theorem l4OMOd_red_pm8532 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8532 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12950) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 407 l4OMOdPmReshapeB0
    12950 8532 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12950 8532 [2048, 1024]

private theorem l4OMOd_red_pm8533 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8533 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12951) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 411 l4OMOdPmReshapeB1
    12951 8533 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12951 8533 [2048, 1024]

private theorem l4OMOd_red_sm5197 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5197 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5196) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 185 l4OMOdSmViewA
    5196 5197 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5196 5197

private theorem l4OMOd_red_sm5201 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5201 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5200) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 186 l4OMOdSmViewB
    5200 5201 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5200 5201

private theorem l4OMOd_red_pm8526 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8526 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8524) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 421 l4OMOdPmViewA0
    8524 8526 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8524 8526

private theorem l4OMOd_red_pm8527 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8527 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8525) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 426 l4OMOdPmViewA1
    8525 8527 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8525 8527

private theorem l4OMOd_red_pm8538 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8538 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8536) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 422 l4OMOdPmViewB0
    8536 8538 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8536 8538

private theorem l4OMOd_red_pm8539 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8539 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8537) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 427 l4OMOdPmViewB1
    8537 8539 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8537 8539

private theorem l4OMOd_red_sm5203 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5203 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5202) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 190 l4OMOdSmReshapeDown
    5202 5203 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5202 5203 [4096, 512]

private theorem l4OMOd_red_pm8546 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8546 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8544) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 434 l4OMOdPmReshapeDown0
    8544 8546 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 8544 8546 [2048, 512]

private theorem l4OMOd_red_pm8547 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8547 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8545) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 437 l4OMOdPmReshapeDown1
    8545 8547 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 8545 8547 [2048, 512]

private theorem l4OMOd_red_sm5206 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5206 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5205) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 192 l4OMOdSmViewDown
    5205 5206 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5205 5206

private theorem l4OMOd_red_pm8554 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8554 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8552) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 442 l4OMOdPmViewDown0
    8552 8554 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 8552 8554

private theorem l4OMOd_red_pm8555 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8555 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8553) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 443 l4OMOdPmViewDown1
    8553 8555 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 8553 8555

private theorem l4OMOd_red_sm5196 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5196 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5194)
        (denoteGraphDistributedFaithful sm_goal_1 init 5195) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 181 l4OMOdSmLinearA
    5194 5195 5196 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5194 5195 5196

private theorem l4OMOd_red_sm5200 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5200 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5198)
        (denoteGraphDistributedFaithful sm_goal_1 init 5199) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 182 l4OMOdSmLinearB
    5198 5199 5200 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5198 5199 5200

private theorem l4OMOd_red_pm8524 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8524 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8520)
        (denoteGraphDistributedFaithful pm_goal_1 init 5195) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 413 l4OMOdPmLinearA0
    8520 5195 8524 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8520 5195 8524

private theorem l4OMOd_red_pm8525 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8525 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8521)
        (denoteGraphDistributedFaithful pm_goal_1 init 5195) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 418 l4OMOdPmLinearA1
    8521 5195 8525 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8521 5195 8525

private theorem l4OMOd_red_pm8536 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8536 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8532)
        (denoteGraphDistributedFaithful pm_goal_1 init 5199) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 414 l4OMOdPmLinearB0
    8532 5199 8536 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8532 5199 8536

private theorem l4OMOd_red_pm8537 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8537 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8533)
        (denoteGraphDistributedFaithful pm_goal_1 init 5199) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 419 l4OMOdPmLinearB1
    8533 5199 8537 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8533 5199 8537

private theorem l4OMOd_red_sm5202 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5202 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5197)
        (denoteGraphDistributedFaithful sm_goal_1 init 5201) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 189 l4OMOdSmSwi
    5197 5201 5202 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5197 5201 5202

private theorem l4OMOd_red_pm8544 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8544 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8526)
        (denoteGraphDistributedFaithful pm_goal_1 init 8538) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 429 l4OMOdPmSwi0
    8526 8538 8544 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 8526 8538 8544

private theorem l4OMOd_red_pm8545 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8545 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8527)
        (denoteGraphDistributedFaithful pm_goal_1 init 8539) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 433 l4OMOdPmSwi1
    8527 8539 8545 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 8527 8539 8545

private theorem l4OMOd_red_sm5205 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5205 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5203)
        (denoteGraphDistributedFaithful sm_goal_1 init 5204) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 191 l4OMOdSmLinearDown
    5203 5204 5205 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5203 5204 5205

private theorem l4OMOd_red_pm8552 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8552 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8546)
        (denoteGraphDistributedFaithful pm_goal_1 init 5204) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 438 l4OMOdPmLinearDown0
    8546 5204 8552 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8546 5204 8552

private theorem l4OMOd_red_pm8553 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8553 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8547)
        (denoteGraphDistributedFaithful pm_goal_1 init 5204) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 441 l4OMOdPmLinearDown1
    8547 5204 8553 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8547 5204 8553

private theorem l4OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l4OMOd_weight_eq (initSM initPM : Store)
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
  rw [l4OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l4OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l4OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l4OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l4OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l4OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5206 ↔ 8554/8555` ordinary relation. -/
theorem l4_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8544)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8545)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8555)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5203)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8546)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8547)
      [4096, 512] [2048, 512] := by
    rw [l4OMOd_red_sm5203 initSM, l4OMOd_red_pm8546 initPM, l4OMOd_red_pm8547 initPM]
    exact ordinary_view hSwi
  have hwD := l4OMOd_weight_eq initSM initPM hInit initGoal_5204 (by native_decide)
    5204 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l4OMOd_weight_shape initPM hPM 5204 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5205)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8552)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8553)
      [4096, 1024] [2048, 1024] := by
    rw [l4OMOd_red_sm5205 initSM, l4OMOd_red_pm8552 initPM,
      l4OMOd_red_pm8553 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l4OMOd_red_sm5206 initSM, l4OMOd_red_pm8554 initPM, l4OMOd_red_pm8555 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l4_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5179)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8488)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8489)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8554)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8555)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5194)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8520)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8521)
      [4096, 1024] [2048, 1024] := by
    rw [l4OMOd_red_sm5194 initSM, l4OMOd_red_pm8520 initPM,
      l4OMOd_red_pm8521 initPM, l4OMOd_red_sm12938 initSM,
      l4OMOd_red_pm12938 initPM, l4OMOd_red_pm12939 initPM]
    exact ordinary_view hNorm
  have hwA := l4OMOd_weight_eq initSM initPM hInit initGoal_5195 (by native_decide)
    5195 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l4OMOd_weight_shape initPM hPM 5195 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5196)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8524)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8525)
      [4096, 512] [2048, 512] := by
    rw [l4OMOd_red_sm5196 initSM, l4OMOd_red_pm8524 initPM,
      l4OMOd_red_pm8525 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5197)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8526)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8527)
      [4096, 512] [2048, 512] := by
    rw [l4OMOd_red_sm5197 initSM, l4OMOd_red_pm8526 initPM,
      l4OMOd_red_pm8527 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5198)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8532)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8533)
      [4096, 1024] [2048, 1024] := by
    rw [l4OMOd_red_sm5198 initSM, l4OMOd_red_pm8532 initPM,
      l4OMOd_red_pm8533 initPM, l4OMOd_red_sm12950 initSM,
      l4OMOd_red_pm12950 initPM, l4OMOd_red_pm12951 initPM]
    exact ordinary_view hNorm
  have hwB := l4OMOd_weight_eq initSM initPM hInit initGoal_5199 (by native_decide)
    5199 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l4OMOd_weight_shape initPM hPM 5199 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8537)
      [4096, 512] [2048, 512] := by
    rw [l4OMOd_red_sm5200 initSM, l4OMOd_red_pm8536 initPM,
      l4OMOd_red_pm8537 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8538)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8539)
      [4096, 512] [2048, 512] := by
    rw [l4OMOd_red_sm5201 initSM, l4OMOd_red_pm8538 initPM,
      l4OMOd_red_pm8539 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8544)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8545)
      [4096, 512] [2048, 512] := by
    rw [l4OMOd_red_sm5202 initSM, l4OMOd_red_pm8544 initPM,
      l4OMOd_red_pm8545 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l4_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l4_ordinary_moe_down_from_swiglu
#print axioms l4_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
