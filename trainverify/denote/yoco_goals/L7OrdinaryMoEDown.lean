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

private def l7OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5344], outs := [8140, 8144, 8148, 8152, 8156], params := [5] }

private def l7OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8980], outs := [15352, 13292, 13302, 13316, 13328], params := [5] }

private def l7OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8981], outs := [15354, 13293, 13303, 13317, 13329], params := [5] }

private def l7OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8152], outs := [5359], params := [4096, 1024] }

private def l7OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8156], outs := [5363], params := [4096, 1024] }

private def l7OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13316], outs := [9012], params := [2048, 1024] }

private def l7OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13317], outs := [9013], params := [2048, 1024] }

private def l7OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13328], outs := [9024], params := [2048, 1024] }

private def l7OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13329], outs := [9025], params := [2048, 1024] }

private def l7OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5359, 5360], outs := [5361] }

private def l7OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5363, 5364], outs := [5365] }

private def l7OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9012, 5360], outs := [9016] }

private def l7OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9013, 5360], outs := [9017] }

private def l7OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9024, 5364], outs := [9028] }

private def l7OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9025, 5364], outs := [9029] }

private def l7OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5361], outs := [5362], params := [4096, 512] }

private def l7OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5365], outs := [5366], params := [4096, 512] }

private def l7OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9016], outs := [9018], params := [2048, 512] }

private def l7OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9017], outs := [9019], params := [2048, 512] }

private def l7OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9028], outs := [9030], params := [2048, 512] }

private def l7OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9029], outs := [9031], params := [2048, 512] }

private def l7OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5362, 5366], outs := [5367] }

private def l7OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9018, 9030], outs := [9036] }

private def l7OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9019, 9031], outs := [9037] }

private def l7OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5367], outs := [5368], params := [4096, 512] }

private def l7OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9036], outs := [9038], params := [2048, 512] }

private def l7OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9037], outs := [9039], params := [2048, 512] }

private def l7OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5368, 5369], outs := [5370] }

private def l7OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9038, 5369], outs := [9044] }

private def l7OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9039, 5369], outs := [9045] }

private def l7OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5370], outs := [5371], params := [4096, 1024] }

private def l7OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9044], outs := [9046], params := [2048, 1024] }

private def l7OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9045], outs := [9047], params := [2048, 1024] }

private theorem l7OMOd_red_sm13316 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8152 =
      denoteGraphDistributedFaithful sm_goal_1 init 5344 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 291 l7OMOdSmRef
    5344 8152 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5344 [8140, 8144, 8148, 8152, 8156] 5 rfl 8152 (by decide)

private theorem l7OMOd_red_sm13328 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8156 =
      denoteGraphDistributedFaithful sm_goal_1 init 5344 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 291 l7OMOdSmRef
    5344 8156 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5344 [8140, 8144, 8148, 8152, 8156] 5 rfl 8156 (by decide)

private theorem l7OMOd_red_pm13316 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13316 =
      denoteGraphDistributedFaithful pm_goal_1 init 8980 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 655 l7OMOdPmRef0
    8980 13316 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8980 [15352, 13292, 13302, 13316, 13328] 5 rfl 13316 (by decide)

private theorem l7OMOd_red_pm13328 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13328 =
      denoteGraphDistributedFaithful pm_goal_1 init 8980 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 655 l7OMOdPmRef0
    8980 13328 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8980 [15352, 13292, 13302, 13316, 13328] 5 rfl 13328 (by decide)

private theorem l7OMOd_red_pm13317 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13317 =
      denoteGraphDistributedFaithful pm_goal_1 init 8981 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 656 l7OMOdPmRef1
    8981 13317 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8981 [15354, 13293, 13303, 13317, 13329] 5 rfl 13317 (by decide)

private theorem l7OMOd_red_pm13329 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13329 =
      denoteGraphDistributedFaithful pm_goal_1 init 8981 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 656 l7OMOdPmRef1
    8981 13329 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8981 [15354, 13293, 13303, 13317, 13329] 5 rfl 13329 (by decide)

private theorem l7OMOd_red_sm5359 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5359 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8152) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 294 l7OMOdSmReshapeA
    8152 5359 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8152 5359 [4096, 1024]

private theorem l7OMOd_red_sm5363 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5363 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8156) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 295 l7OMOdSmReshapeB
    8156 5363 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8156 5363 [4096, 1024]

private theorem l7OMOd_red_pm9012 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9012 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13316) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 658 l7OMOdPmReshapeA0
    13316 9012 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13316 9012 [2048, 1024]

private theorem l7OMOd_red_pm9013 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9013 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13317) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 662 l7OMOdPmReshapeA1
    13317 9013 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13317 9013 [2048, 1024]

private theorem l7OMOd_red_pm9024 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9024 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13328) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 659 l7OMOdPmReshapeB0
    13328 9024 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13328 9024 [2048, 1024]

private theorem l7OMOd_red_pm9025 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9025 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13329) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 663 l7OMOdPmReshapeB1
    13329 9025 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13329 9025 [2048, 1024]

private theorem l7OMOd_red_sm5362 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5362 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5361) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 302 l7OMOdSmViewA
    5361 5362 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5361 5362

private theorem l7OMOd_red_sm5366 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5366 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5365) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 303 l7OMOdSmViewB
    5365 5366 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5365 5366

private theorem l7OMOd_red_pm9018 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9018 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9016) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 673 l7OMOdPmViewA0
    9016 9018 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9016 9018

private theorem l7OMOd_red_pm9019 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9019 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9017) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 678 l7OMOdPmViewA1
    9017 9019 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9017 9019

private theorem l7OMOd_red_pm9030 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9030 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9028) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 674 l7OMOdPmViewB0
    9028 9030 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9028 9030

private theorem l7OMOd_red_pm9031 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9031 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9029) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 679 l7OMOdPmViewB1
    9029 9031 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9029 9031

private theorem l7OMOd_red_sm5368 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5368 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5367) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 307 l7OMOdSmReshapeDown
    5367 5368 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5367 5368 [4096, 512]

private theorem l7OMOd_red_pm9038 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9038 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9036) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 686 l7OMOdPmReshapeDown0
    9036 9038 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9036 9038 [2048, 512]

private theorem l7OMOd_red_pm9039 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9039 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9037) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 689 l7OMOdPmReshapeDown1
    9037 9039 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9037 9039 [2048, 512]

private theorem l7OMOd_red_sm5371 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5371 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5370) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 309 l7OMOdSmViewDown
    5370 5371 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5370 5371

private theorem l7OMOd_red_pm9046 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9046 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9044) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 694 l7OMOdPmViewDown0
    9044 9046 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9044 9046

private theorem l7OMOd_red_pm9047 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9047 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9045) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 695 l7OMOdPmViewDown1
    9045 9047 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9045 9047

private theorem l7OMOd_red_sm5361 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5361 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5359)
        (denoteGraphDistributedFaithful sm_goal_1 init 5360) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 298 l7OMOdSmLinearA
    5359 5360 5361 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5359 5360 5361

private theorem l7OMOd_red_sm5365 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5365 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5363)
        (denoteGraphDistributedFaithful sm_goal_1 init 5364) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 299 l7OMOdSmLinearB
    5363 5364 5365 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5363 5364 5365

private theorem l7OMOd_red_pm9016 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9016 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9012)
        (denoteGraphDistributedFaithful pm_goal_1 init 5360) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 665 l7OMOdPmLinearA0
    9012 5360 9016 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9012 5360 9016

private theorem l7OMOd_red_pm9017 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9017 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9013)
        (denoteGraphDistributedFaithful pm_goal_1 init 5360) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 670 l7OMOdPmLinearA1
    9013 5360 9017 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9013 5360 9017

private theorem l7OMOd_red_pm9028 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9028 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9024)
        (denoteGraphDistributedFaithful pm_goal_1 init 5364) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 666 l7OMOdPmLinearB0
    9024 5364 9028 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9024 5364 9028

private theorem l7OMOd_red_pm9029 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9029 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9025)
        (denoteGraphDistributedFaithful pm_goal_1 init 5364) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 671 l7OMOdPmLinearB1
    9025 5364 9029 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9025 5364 9029

private theorem l7OMOd_red_sm5367 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5367 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5362)
        (denoteGraphDistributedFaithful sm_goal_1 init 5366) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 306 l7OMOdSmSwi
    5362 5366 5367 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5362 5366 5367

private theorem l7OMOd_red_pm9036 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9036 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9018)
        (denoteGraphDistributedFaithful pm_goal_1 init 9030) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 681 l7OMOdPmSwi0
    9018 9030 9036 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9018 9030 9036

private theorem l7OMOd_red_pm9037 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9037 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9019)
        (denoteGraphDistributedFaithful pm_goal_1 init 9031) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 685 l7OMOdPmSwi1
    9019 9031 9037 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9019 9031 9037

private theorem l7OMOd_red_sm5370 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5370 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5368)
        (denoteGraphDistributedFaithful sm_goal_1 init 5369) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 308 l7OMOdSmLinearDown
    5368 5369 5370 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5368 5369 5370

private theorem l7OMOd_red_pm9044 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9044 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9038)
        (denoteGraphDistributedFaithful pm_goal_1 init 5369) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 690 l7OMOdPmLinearDown0
    9038 5369 9044 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9038 5369 9044

private theorem l7OMOd_red_pm9045 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9045 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9039)
        (denoteGraphDistributedFaithful pm_goal_1 init 5369) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 693 l7OMOdPmLinearDown1
    9039 5369 9045 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9039 5369 9045

private theorem l7OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l7OMOd_weight_eq (initSM initPM : Store)
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
  rw [l7OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l7OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l7OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l7OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l7OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l7OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5371 ↔ 9046/9047` ordinary relation. -/
theorem l7_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5367)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9036)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9037)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5371)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9047)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5368)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9038)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9039)
      [4096, 512] [2048, 512] := by
    rw [l7OMOd_red_sm5368 initSM, l7OMOd_red_pm9038 initPM, l7OMOd_red_pm9039 initPM]
    exact ordinary_view hSwi
  have hwD := l7OMOd_weight_eq initSM initPM hInit initGoal_5369 (by native_decide)
    5369 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l7OMOd_weight_shape initPM hPM 5369 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5370)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9045)
      [4096, 1024] [2048, 1024] := by
    rw [l7OMOd_red_sm5370 initSM, l7OMOd_red_pm9044 initPM,
      l7OMOd_red_pm9045 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l7OMOd_red_sm5371 initSM, l7OMOd_red_pm9046 initPM, l7OMOd_red_pm9047 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l7_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5344)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8980)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8981)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5371)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9047)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5359)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9013)
      [4096, 1024] [2048, 1024] := by
    rw [l7OMOd_red_sm5359 initSM, l7OMOd_red_pm9012 initPM,
      l7OMOd_red_pm9013 initPM, l7OMOd_red_sm13316 initSM,
      l7OMOd_red_pm13316 initPM, l7OMOd_red_pm13317 initPM]
    exact ordinary_view hNorm
  have hwA := l7OMOd_weight_eq initSM initPM hInit initGoal_5360 (by native_decide)
    5360 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l7OMOd_weight_shape initPM hPM 5360 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5361)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9017)
      [4096, 512] [2048, 512] := by
    rw [l7OMOd_red_sm5361 initSM, l7OMOd_red_pm9016 initPM,
      l7OMOd_red_pm9017 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5362)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9018)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9019)
      [4096, 512] [2048, 512] := by
    rw [l7OMOd_red_sm5362 initSM, l7OMOd_red_pm9018 initPM,
      l7OMOd_red_pm9019 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5363)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9024)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9025)
      [4096, 1024] [2048, 1024] := by
    rw [l7OMOd_red_sm5363 initSM, l7OMOd_red_pm9024 initPM,
      l7OMOd_red_pm9025 initPM, l7OMOd_red_sm13328 initSM,
      l7OMOd_red_pm13328 initPM, l7OMOd_red_pm13329 initPM]
    exact ordinary_view hNorm
  have hwB := l7OMOd_weight_eq initSM initPM hInit initGoal_5364 (by native_decide)
    5364 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l7OMOd_weight_shape initPM hPM 5364 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5365)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9028)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9029)
      [4096, 512] [2048, 512] := by
    rw [l7OMOd_red_sm5365 initSM, l7OMOd_red_pm9028 initPM,
      l7OMOd_red_pm9029 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5366)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9030)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9031)
      [4096, 512] [2048, 512] := by
    rw [l7OMOd_red_sm5366 initSM, l7OMOd_red_pm9030 initPM,
      l7OMOd_red_pm9031 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5367)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9036)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9037)
      [4096, 512] [2048, 512] := by
    rw [l7OMOd_red_sm5367 initSM, l7OMOd_red_pm9036 initPM,
      l7OMOd_red_pm9037 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l7_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l7_ordinary_moe_down_from_swiglu
#print axioms l7_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
