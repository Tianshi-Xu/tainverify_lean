/- Canonical Goal 1 cache-source layer: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.CanonicalKVCacheBoundary
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

private def cKVCdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564], outs := [8348, 8352, 8356, 8360, 8364], params := [5] }

private def cKVCdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636], outs := [15384, 13796, 13806, 13820, 13832], params := [5] }

private def cKVCdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637], outs := [15386, 13797, 13807, 13821, 13833], params := [5] }

private def cKVCdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8360], outs := [5579], params := [4096, 1024] }

private def cKVCdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8364], outs := [5583], params := [4096, 1024] }

private def cKVCdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13820], outs := [9668], params := [2048, 1024] }

private def cKVCdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13821], outs := [9669], params := [2048, 1024] }

private def cKVCdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13832], outs := [9680], params := [2048, 1024] }

private def cKVCdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13833], outs := [9681], params := [2048, 1024] }

private def cKVCdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5579, 5580], outs := [5581] }

private def cKVCdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5583, 5584], outs := [5585] }

private def cKVCdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9668, 5580], outs := [9672] }

private def cKVCdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9669, 5580], outs := [9673] }

private def cKVCdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9680, 5584], outs := [9684] }

private def cKVCdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9681, 5584], outs := [9685] }

private def cKVCdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5581], outs := [5582], params := [4096, 512] }

private def cKVCdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5585], outs := [5586], params := [4096, 512] }

private def cKVCdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9672], outs := [9674], params := [2048, 512] }

private def cKVCdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9673], outs := [9675], params := [2048, 512] }

private def cKVCdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9684], outs := [9686], params := [2048, 512] }

private def cKVCdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9685], outs := [9687], params := [2048, 512] }

private def cKVCdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5582, 5586], outs := [5587] }

private def cKVCdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9674, 9686], outs := [9692] }

private def cKVCdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9675, 9687], outs := [9693] }

private def cKVCdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5587], outs := [5588], params := [4096, 512] }

private def cKVCdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9692], outs := [9694], params := [2048, 512] }

private def cKVCdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9693], outs := [9695], params := [2048, 512] }

private def cKVCdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5588, 5589], outs := [5590] }

private def cKVCdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9694, 5589], outs := [9700] }

private def cKVCdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9695, 5589], outs := [9701] }

private def cKVCdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5590], outs := [5591], params := [4096, 1024] }

private def cKVCdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9700], outs := [9702], params := [2048, 1024] }

private def cKVCdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9701], outs := [9703], params := [2048, 1024] }

private theorem cKVCd_red_sm13820 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8360 =
      denoteGraphDistributedFaithful sm_goal_1 init 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 447 cKVCdSmRef
    5564 8360 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364] 5 rfl 8360 (by decide)

private theorem cKVCd_red_sm13832 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8364 =
      denoteGraphDistributedFaithful sm_goal_1 init 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 447 cKVCdSmRef
    5564 8364 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364] 5 rfl 8364 (by decide)

private theorem cKVCd_red_pm13820 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13820 =
      denoteGraphDistributedFaithful pm_goal_1 init 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 991 cKVCdPmRef0
    9636 13820 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636 [15384, 13796, 13806, 13820, 13832] 5 rfl 13820 (by decide)

private theorem cKVCd_red_pm13832 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13832 =
      denoteGraphDistributedFaithful pm_goal_1 init 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 991 cKVCdPmRef0
    9636 13832 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636 [15384, 13796, 13806, 13820, 13832] 5 rfl 13832 (by decide)

private theorem cKVCd_red_pm13821 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13821 =
      denoteGraphDistributedFaithful pm_goal_1 init 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 992 cKVCdPmRef1
    9637 13821 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637 [15386, 13797, 13807, 13821, 13833] 5 rfl 13821 (by decide)

private theorem cKVCd_red_pm13833 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13833 =
      denoteGraphDistributedFaithful pm_goal_1 init 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 992 cKVCdPmRef1
    9637 13833 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637 [15386, 13797, 13807, 13821, 13833] 5 rfl 13833 (by decide)

private theorem cKVCd_red_sm5579 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5579 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8360) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 450 cKVCdSmReshapeA
    8360 5579 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8360 5579 [4096, 1024]

private theorem cKVCd_red_sm5583 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5583 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8364) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 451 cKVCdSmReshapeB
    8364 5583 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8364 5583 [4096, 1024]

private theorem cKVCd_red_pm9668 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9668 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13820) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 994 cKVCdPmReshapeA0
    13820 9668 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13820 9668 [2048, 1024]

private theorem cKVCd_red_pm9669 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9669 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13821) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 998 cKVCdPmReshapeA1
    13821 9669 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13821 9669 [2048, 1024]

private theorem cKVCd_red_pm9680 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9680 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13832) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 995 cKVCdPmReshapeB0
    13832 9680 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13832 9680 [2048, 1024]

private theorem cKVCd_red_pm9681 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9681 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13833) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 999 cKVCdPmReshapeB1
    13833 9681 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13833 9681 [2048, 1024]

private theorem cKVCd_red_sm5582 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5582 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5581) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 458 cKVCdSmViewA
    5581 5582 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5581 5582

private theorem cKVCd_red_sm5586 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5586 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5585) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 459 cKVCdSmViewB
    5585 5586 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5585 5586

private theorem cKVCd_red_pm9674 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9674 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9672) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1009 cKVCdPmViewA0
    9672 9674 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9672 9674

private theorem cKVCd_red_pm9675 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9675 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9673) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1014 cKVCdPmViewA1
    9673 9675 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9673 9675

private theorem cKVCd_red_pm9686 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9686 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9684) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1010 cKVCdPmViewB0
    9684 9686 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9684 9686

private theorem cKVCd_red_pm9687 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9687 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9685) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1015 cKVCdPmViewB1
    9685 9687 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9685 9687

private theorem cKVCd_red_sm5588 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5588 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5587) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 463 cKVCdSmReshapeDown
    5587 5588 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5587 5588 [4096, 512]

private theorem cKVCd_red_pm9694 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9694 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9692) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1022 cKVCdPmReshapeDown0
    9692 9694 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9692 9694 [2048, 512]

private theorem cKVCd_red_pm9695 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9695 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9693) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1025 cKVCdPmReshapeDown1
    9693 9695 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9693 9695 [2048, 512]

private theorem cKVCd_red_sm5591 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5591 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5590) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 465 cKVCdSmViewDown
    5590 5591 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5590 5591

private theorem cKVCd_red_pm9702 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9702 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9700) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1030 cKVCdPmViewDown0
    9700 9702 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9700 9702

private theorem cKVCd_red_pm9703 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9703 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9701) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1031 cKVCdPmViewDown1
    9701 9703 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9701 9703

private theorem cKVCd_red_sm5581 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5581 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5579)
        (denoteGraphDistributedFaithful sm_goal_1 init 5580) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 454 cKVCdSmLinearA
    5579 5580 5581 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5579 5580 5581

private theorem cKVCd_red_sm5585 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5585 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5583)
        (denoteGraphDistributedFaithful sm_goal_1 init 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 455 cKVCdSmLinearB
    5583 5584 5585 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5583 5584 5585

private theorem cKVCd_red_pm9672 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9672 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9668)
        (denoteGraphDistributedFaithful pm_goal_1 init 5580) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1001 cKVCdPmLinearA0
    9668 5580 9672 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9668 5580 9672

private theorem cKVCd_red_pm9673 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9673 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9669)
        (denoteGraphDistributedFaithful pm_goal_1 init 5580) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1006 cKVCdPmLinearA1
    9669 5580 9673 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9669 5580 9673

private theorem cKVCd_red_pm9684 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9684 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9680)
        (denoteGraphDistributedFaithful pm_goal_1 init 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1002 cKVCdPmLinearB0
    9680 5584 9684 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9680 5584 9684

private theorem cKVCd_red_pm9685 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9685 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9681)
        (denoteGraphDistributedFaithful pm_goal_1 init 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1007 cKVCdPmLinearB1
    9681 5584 9685 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9681 5584 9685

private theorem cKVCd_red_sm5587 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5587 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5582)
        (denoteGraphDistributedFaithful sm_goal_1 init 5586) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 462 cKVCdSmSwi
    5582 5586 5587 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5582 5586 5587

private theorem cKVCd_red_pm9692 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9692 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9674)
        (denoteGraphDistributedFaithful pm_goal_1 init 9686) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1017 cKVCdPmSwi0
    9674 9686 9692 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9674 9686 9692

private theorem cKVCd_red_pm9693 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9693 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9675)
        (denoteGraphDistributedFaithful pm_goal_1 init 9687) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1021 cKVCdPmSwi1
    9675 9687 9693 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9675 9687 9693

private theorem cKVCd_red_sm5590 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5590 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5588)
        (denoteGraphDistributedFaithful sm_goal_1 init 5589) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 464 cKVCdSmLinearDown
    5588 5589 5590 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5588 5589 5590

private theorem cKVCd_red_pm9700 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9700 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9694)
        (denoteGraphDistributedFaithful pm_goal_1 init 5589) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1026 cKVCdPmLinearDown0
    9694 5589 9700 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9694 5589 9700

private theorem cKVCd_red_pm9701 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9701 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9695)
        (denoteGraphDistributedFaithful pm_goal_1 init 5589) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1029 cKVCdPmLinearDown1
    9695 5589 9701 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9695 5589 9701

private theorem cKVCd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem cKVCd_weight_eq (initSM initPM : Store)
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
  rw [cKVCd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    cKVCd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem cKVCd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [cKVCd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 cache-source SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem canonical_kv_cache_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9637)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5591)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9703)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8360)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13820)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13821)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCd_red_sm13820 initSM, cKVCd_red_pm13820 initPM, cKVCd_red_pm13821 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8364)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13832)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 13833)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCd_red_sm13832 initSM, cKVCd_red_pm13832 initPM, cKVCd_red_pm13833 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5579)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9668)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9669)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCd_red_sm5579 initSM, cKVCd_red_pm9668 initPM, cKVCd_red_pm9669 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5583)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9680)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9681)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCd_red_sm5583 initSM, cKVCd_red_pm9680 initPM, cKVCd_red_pm9681 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := cKVCd_weight_eq initSM initPM hInit initGoal_5580 (by native_decide)
    5580 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := cKVCd_weight_eq initSM initPM hInit initGoal_5584 (by native_decide)
    5584 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := cKVCd_weight_shape initPM hPM 5580 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := cKVCd_weight_shape initPM hPM 5584 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5581)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9672)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9673)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cKVCd_red_sm5581 initSM, cKVCd_red_pm9672 initPM,
      cKVCd_red_pm9673 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9684)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9685)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cKVCd_red_sm5585 initSM, cKVCd_red_pm9684 initPM,
      cKVCd_red_pm9685 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5582)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9675)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cKVCd_red_sm5582 initSM, cKVCd_red_pm9674 initPM, cKVCd_red_pm9675 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5586)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9686)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9687)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cKVCd_red_sm5586 initSM, cKVCd_red_pm9686 initPM, cKVCd_red_pm9687 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5582)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9675)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5586)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9686)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9687)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5587)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9692)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9693)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cKVCd_red_sm5587 initSM, cKVCd_red_pm9692 initPM, cKVCd_red_pm9693 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9694)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9695)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cKVCd_red_sm5588 initSM, cKVCd_red_pm9694 initPM, cKVCd_red_pm9695 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := cKVCd_weight_eq initSM initPM hInit initGoal_5589 (by native_decide)
    5589 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := cKVCd_weight_shape initPM hPM 5589 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5590)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9700)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9701)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCd_red_sm5590 initSM, cKVCd_red_pm9700 initPM,
      cKVCd_red_pm9701 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [cKVCd_red_sm5591 initSM, cKVCd_red_pm9702 initPM, cKVCd_red_pm9703 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

#print axioms canonical_kv_cache_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns