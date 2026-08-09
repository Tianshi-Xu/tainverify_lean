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

private def cKVCOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564], outs := [8348, 8352, 8356, 8360, 8364], params := [5] }

private def cKVCOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636], outs := [15384, 13796, 13806, 13820, 13832], params := [5] }

private def cKVCOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637], outs := [15386, 13797, 13807, 13821, 13833], params := [5] }

private def cKVCOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8360], outs := [5579], params := [4096, 1024] }

private def cKVCOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8364], outs := [5583], params := [4096, 1024] }

private def cKVCOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13820], outs := [9668], params := [2048, 1024] }

private def cKVCOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13821], outs := [9669], params := [2048, 1024] }

private def cKVCOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13832], outs := [9680], params := [2048, 1024] }

private def cKVCOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13833], outs := [9681], params := [2048, 1024] }

private def cKVCOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5579, 5580], outs := [5581] }

private def cKVCOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5583, 5584], outs := [5585] }

private def cKVCOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9668, 5580], outs := [9672] }

private def cKVCOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9669, 5580], outs := [9673] }

private def cKVCOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9680, 5584], outs := [9684] }

private def cKVCOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9681, 5584], outs := [9685] }

private def cKVCOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5581], outs := [5582], params := [4096, 512] }

private def cKVCOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5585], outs := [5586], params := [4096, 512] }

private def cKVCOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9672], outs := [9674], params := [2048, 512] }

private def cKVCOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9673], outs := [9675], params := [2048, 512] }

private def cKVCOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9684], outs := [9686], params := [2048, 512] }

private def cKVCOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9685], outs := [9687], params := [2048, 512] }

private def cKVCOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5582, 5586], outs := [5587] }

private def cKVCOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [9674, 9686], outs := [9692] }

private def cKVCOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [9675, 9687], outs := [9693] }

private def cKVCOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5587], outs := [5588], params := [4096, 512] }

private def cKVCOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9692], outs := [9694], params := [2048, 512] }

private def cKVCOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9693], outs := [9695], params := [2048, 512] }

private def cKVCOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5588, 5589], outs := [5590] }

private def cKVCOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9694, 5589], outs := [9700] }

private def cKVCOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9695, 5589], outs := [9701] }

private def cKVCOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5590], outs := [5591], params := [4096, 1024] }

private def cKVCOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9700], outs := [9702], params := [2048, 1024] }

private def cKVCOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9701], outs := [9703], params := [2048, 1024] }

private theorem cKVCOd_red_sm13820 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8360 =
      denoteGraphDistributedFaithful sm_goal_1 init 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 447 cKVCOdSmRef
    5564 8360 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364] 5 rfl 8360 (by decide)

private theorem cKVCOd_red_sm13832 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8364 =
      denoteGraphDistributedFaithful sm_goal_1 init 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 447 cKVCOdSmRef
    5564 8364 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364] 5 rfl 8364 (by decide)

private theorem cKVCOd_red_pm13820 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13820 =
      denoteGraphDistributedFaithful pm_goal_1 init 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 991 cKVCOdPmRef0
    9636 13820 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636 [15384, 13796, 13806, 13820, 13832] 5 rfl 13820 (by decide)

private theorem cKVCOd_red_pm13832 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13832 =
      denoteGraphDistributedFaithful pm_goal_1 init 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 991 cKVCOdPmRef0
    9636 13832 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636 [15384, 13796, 13806, 13820, 13832] 5 rfl 13832 (by decide)

private theorem cKVCOd_red_pm13821 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13821 =
      denoteGraphDistributedFaithful pm_goal_1 init 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 992 cKVCOdPmRef1
    9637 13821 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637 [15386, 13797, 13807, 13821, 13833] 5 rfl 13821 (by decide)

private theorem cKVCOd_red_pm13833 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 13833 =
      denoteGraphDistributedFaithful pm_goal_1 init 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 992 cKVCOdPmRef1
    9637 13833 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637 [15386, 13797, 13807, 13821, 13833] 5 rfl 13833 (by decide)

private theorem cKVCOd_red_sm5579 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5579 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8360) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 450 cKVCOdSmReshapeA
    8360 5579 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8360 5579 [4096, 1024]

private theorem cKVCOd_red_sm5583 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5583 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8364) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 451 cKVCOdSmReshapeB
    8364 5583 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8364 5583 [4096, 1024]

private theorem cKVCOd_red_pm9668 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9668 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13820) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 994 cKVCOdPmReshapeA0
    13820 9668 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13820 9668 [2048, 1024]

private theorem cKVCOd_red_pm9669 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9669 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13821) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 998 cKVCOdPmReshapeA1
    13821 9669 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13821 9669 [2048, 1024]

private theorem cKVCOd_red_pm9680 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9680 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13832) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 995 cKVCOdPmReshapeB0
    13832 9680 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13832 9680 [2048, 1024]

private theorem cKVCOd_red_pm9681 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9681 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 13833) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 999 cKVCOdPmReshapeB1
    13833 9681 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13833 9681 [2048, 1024]

private theorem cKVCOd_red_sm5582 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5582 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5581) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 458 cKVCOdSmViewA
    5581 5582 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5581 5582

private theorem cKVCOd_red_sm5586 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5586 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5585) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 459 cKVCOdSmViewB
    5585 5586 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5585 5586

private theorem cKVCOd_red_pm9674 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9674 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9672) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1009 cKVCOdPmViewA0
    9672 9674 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9672 9674

private theorem cKVCOd_red_pm9675 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9675 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9673) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1014 cKVCOdPmViewA1
    9673 9675 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9673 9675

private theorem cKVCOd_red_pm9686 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9686 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9684) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1010 cKVCOdPmViewB0
    9684 9686 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 9684 9686

private theorem cKVCOd_red_pm9687 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9687 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9685) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1015 cKVCOdPmViewB1
    9685 9687 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 9685 9687

private theorem cKVCOd_red_sm5588 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5588 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5587) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 463 cKVCOdSmReshapeDown
    5587 5588 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5587 5588 [4096, 512]

private theorem cKVCOd_red_pm9694 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9694 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9692) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1022 cKVCOdPmReshapeDown0
    9692 9694 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 9692 9694 [2048, 512]

private theorem cKVCOd_red_pm9695 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9695 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 9693) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1025 cKVCOdPmReshapeDown1
    9693 9695 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 9693 9695 [2048, 512]

private theorem cKVCOd_red_sm5591 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5591 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5590) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 465 cKVCOdSmViewDown
    5590 5591 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5590 5591

private theorem cKVCOd_red_pm9702 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9702 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9700) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1030 cKVCOdPmViewDown0
    9700 9702 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 9700 9702

private theorem cKVCOd_red_pm9703 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9703 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 9701) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1031 cKVCOdPmViewDown1
    9701 9703 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 9701 9703

private theorem cKVCOd_red_sm5581 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5581 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5579)
        (denoteGraphDistributedFaithful sm_goal_1 init 5580) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 454 cKVCOdSmLinearA
    5579 5580 5581 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5579 5580 5581

private theorem cKVCOd_red_sm5585 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5585 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5583)
        (denoteGraphDistributedFaithful sm_goal_1 init 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 455 cKVCOdSmLinearB
    5583 5584 5585 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5583 5584 5585

private theorem cKVCOd_red_pm9672 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9672 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9668)
        (denoteGraphDistributedFaithful pm_goal_1 init 5580) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1001 cKVCOdPmLinearA0
    9668 5580 9672 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9668 5580 9672

private theorem cKVCOd_red_pm9673 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9673 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9669)
        (denoteGraphDistributedFaithful pm_goal_1 init 5580) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1006 cKVCOdPmLinearA1
    9669 5580 9673 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9669 5580 9673

private theorem cKVCOd_red_pm9684 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9684 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9680)
        (denoteGraphDistributedFaithful pm_goal_1 init 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1002 cKVCOdPmLinearB0
    9680 5584 9684 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9680 5584 9684

private theorem cKVCOd_red_pm9685 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9685 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9681)
        (denoteGraphDistributedFaithful pm_goal_1 init 5584) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1007 cKVCOdPmLinearB1
    9681 5584 9685 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9681 5584 9685

private theorem cKVCOd_red_sm5587 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5587 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5582)
        (denoteGraphDistributedFaithful sm_goal_1 init 5586) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 462 cKVCOdSmSwi
    5582 5586 5587 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5582 5586 5587

private theorem cKVCOd_red_pm9692 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9692 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9674)
        (denoteGraphDistributedFaithful pm_goal_1 init 9686) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1017 cKVCOdPmSwi0
    9674 9686 9692 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 9674 9686 9692

private theorem cKVCOd_red_pm9693 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9693 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 9675)
        (denoteGraphDistributedFaithful pm_goal_1 init 9687) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1021 cKVCOdPmSwi1
    9675 9687 9693 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 9675 9687 9693

private theorem cKVCOd_red_sm5590 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5590 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5588)
        (denoteGraphDistributedFaithful sm_goal_1 init 5589) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 464 cKVCOdSmLinearDown
    5588 5589 5590 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5588 5589 5590

private theorem cKVCOd_red_pm9700 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9700 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9694)
        (denoteGraphDistributedFaithful pm_goal_1 init 5589) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1026 cKVCOdPmLinearDown0
    9694 5589 9700 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9694 5589 9700

private theorem cKVCOd_red_pm9701 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 9701 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 9695)
        (denoteGraphDistributedFaithful pm_goal_1 init 5589) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1029 cKVCOdPmLinearDown1
    9695 5589 9701 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9695 5589 9701

private theorem cKVCOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem cKVCOd_weight_eq (initSM initPM : Store)
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
  rw [cKVCOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    cKVCOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem cKVCOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [cKVCOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem cKVCOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact cKVCOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5591 ↔ 9702/9703` ordinary relation. -/
theorem canonical_kv_cache_ordinary_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5587)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9692)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9693)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5591)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9703)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9694)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9695)
      [4096, 512] [2048, 512] := by
    rw [cKVCOd_red_sm5588 initSM, cKVCOd_red_pm9694 initPM, cKVCOd_red_pm9695 initPM]
    exact ordinary_view hSwi
  have hwD := cKVCOd_weight_eq initSM initPM hInit initGoal_5589 (by native_decide)
    5589 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := cKVCOd_weight_shape initPM hPM 5589 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5590)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9700)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9701)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCOd_red_sm5590 initSM, cKVCOd_red_pm9700 initPM,
      cKVCOd_red_pm9701 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [cKVCOd_red_sm5591 initSM, cKVCOd_red_pm9702 initPM, cKVCOd_red_pm9703 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem canonical_kv_cache_ordinary_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9637)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5591)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9703)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5579)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9668)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9669)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCOd_red_sm5579 initSM, cKVCOd_red_pm9668 initPM,
      cKVCOd_red_pm9669 initPM, cKVCOd_red_sm13820 initSM,
      cKVCOd_red_pm13820 initPM, cKVCOd_red_pm13821 initPM]
    exact ordinary_view hNorm
  have hwA := cKVCOd_weight_eq initSM initPM hInit initGoal_5580 (by native_decide)
    5580 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := cKVCOd_weight_shape initPM hPM 5580 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5581)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9672)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9673)
      [4096, 512] [2048, 512] := by
    rw [cKVCOd_red_sm5581 initSM, cKVCOd_red_pm9672 initPM,
      cKVCOd_red_pm9673 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5582)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9675)
      [4096, 512] [2048, 512] := by
    rw [cKVCOd_red_sm5582 initSM, cKVCOd_red_pm9674 initPM,
      cKVCOd_red_pm9675 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5583)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9680)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9681)
      [4096, 1024] [2048, 1024] := by
    rw [cKVCOd_red_sm5583 initSM, cKVCOd_red_pm9680 initPM,
      cKVCOd_red_pm9681 initPM, cKVCOd_red_sm13832 initSM,
      cKVCOd_red_pm13832 initPM, cKVCOd_red_pm13833 initPM]
    exact ordinary_view hNorm
  have hwB := cKVCOd_weight_eq initSM initPM hInit initGoal_5584 (by native_decide)
    5584 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := cKVCOd_weight_shape initPM hPM 5584 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9684)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9685)
      [4096, 512] [2048, 512] := by
    rw [cKVCOd_red_sm5585 initSM, cKVCOd_red_pm9684 initPM,
      cKVCOd_red_pm9685 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5586)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9686)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9687)
      [4096, 512] [2048, 512] := by
    rw [cKVCOd_red_sm5586 initSM, cKVCOd_red_pm9686 initPM,
      cKVCOd_red_pm9687 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5587)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9692)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9693)
      [4096, 512] [2048, 512] := by
    rw [cKVCOd_red_sm5587 initSM, cKVCOd_red_pm9692 initPM,
      cKVCOd_red_pm9693 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact canonical_kv_cache_ordinary_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms canonical_kv_cache_ordinary_down_from_swiglu
#print axioms canonical_kv_cache_ordinary_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
