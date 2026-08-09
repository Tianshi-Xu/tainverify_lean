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

private def l1OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5014], outs := [7828, 7832, 7836, 7840, 7844], params := [5] }

private def l1OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7996], outs := [15304, 12536, 12546, 12560, 12572], params := [5] }

private def l1OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7997], outs := [15306, 12537, 12547, 12561, 12573], params := [5] }

private def l1OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7840], outs := [5029], params := [4096, 1024] }

private def l1OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7844], outs := [5033], params := [4096, 1024] }

private def l1OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12560], outs := [8028], params := [2048, 1024] }

private def l1OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12561], outs := [8029], params := [2048, 1024] }

private def l1OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12572], outs := [8040], params := [2048, 1024] }

private def l1OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12573], outs := [8041], params := [2048, 1024] }

private def l1OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5029, 5030], outs := [5031] }

private def l1OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5033, 5034], outs := [5035] }

private def l1OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8028, 5030], outs := [8032] }

private def l1OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8029, 5030], outs := [8033] }

private def l1OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8040, 5034], outs := [8044] }

private def l1OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8041, 5034], outs := [8045] }

private def l1OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5031], outs := [5032], params := [4096, 512] }

private def l1OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5035], outs := [5036], params := [4096, 512] }

private def l1OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8032], outs := [8034], params := [2048, 512] }

private def l1OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8033], outs := [8035], params := [2048, 512] }

private def l1OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8044], outs := [8046], params := [2048, 512] }

private def l1OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8045], outs := [8047], params := [2048, 512] }

private def l1OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5032, 5036], outs := [5037] }

private def l1OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [8034, 8046], outs := [8052] }

private def l1OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [8035, 8047], outs := [8053] }

private def l1OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5037], outs := [5038], params := [4096, 512] }

private def l1OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8052], outs := [8054], params := [2048, 512] }

private def l1OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [8053], outs := [8055], params := [2048, 512] }

private def l1OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5038, 5039], outs := [5040] }

private def l1OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8054, 5039], outs := [8060] }

private def l1OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8055, 5039], outs := [8061] }

private def l1OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5040], outs := [5041], params := [4096, 1024] }

private def l1OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8060], outs := [8062], params := [2048, 1024] }

private def l1OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8061], outs := [8063], params := [2048, 1024] }

private theorem l1OMOd_red_sm12560 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7840 =
      denoteGraphDistributedFaithful sm_goal_1 init 5014 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 57 l1OMOdSmRef
    5014 7840 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5014 [7828, 7832, 7836, 7840, 7844] 5 rfl 7840 (by decide)

private theorem l1OMOd_red_sm12572 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7844 =
      denoteGraphDistributedFaithful sm_goal_1 init 5014 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 57 l1OMOdSmRef
    5014 7844 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5014 [7828, 7832, 7836, 7840, 7844] 5 rfl 7844 (by decide)

private theorem l1OMOd_red_pm12560 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12560 =
      denoteGraphDistributedFaithful pm_goal_1 init 7996 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 151 l1OMOdPmRef0
    7996 12560 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7996 [15304, 12536, 12546, 12560, 12572] 5 rfl 12560 (by decide)

private theorem l1OMOd_red_pm12572 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12572 =
      denoteGraphDistributedFaithful pm_goal_1 init 7996 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 151 l1OMOdPmRef0
    7996 12572 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7996 [15304, 12536, 12546, 12560, 12572] 5 rfl 12572 (by decide)

private theorem l1OMOd_red_pm12561 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12561 =
      denoteGraphDistributedFaithful pm_goal_1 init 7997 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 152 l1OMOdPmRef1
    7997 12561 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7997 [15306, 12537, 12547, 12561, 12573] 5 rfl 12561 (by decide)

private theorem l1OMOd_red_pm12573 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12573 =
      denoteGraphDistributedFaithful pm_goal_1 init 7997 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 152 l1OMOdPmRef1
    7997 12573 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7997 [15306, 12537, 12547, 12561, 12573] 5 rfl 12573 (by decide)

private theorem l1OMOd_red_sm5029 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5029 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7840) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 60 l1OMOdSmReshapeA
    7840 5029 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7840 5029 [4096, 1024]

private theorem l1OMOd_red_sm5033 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5033 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7844) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 61 l1OMOdSmReshapeB
    7844 5033 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7844 5033 [4096, 1024]

private theorem l1OMOd_red_pm8028 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8028 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12560) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 154 l1OMOdPmReshapeA0
    12560 8028 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12560 8028 [2048, 1024]

private theorem l1OMOd_red_pm8029 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8029 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12561) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 158 l1OMOdPmReshapeA1
    12561 8029 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12561 8029 [2048, 1024]

private theorem l1OMOd_red_pm8040 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8040 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12572) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 155 l1OMOdPmReshapeB0
    12572 8040 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12572 8040 [2048, 1024]

private theorem l1OMOd_red_pm8041 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8041 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12573) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 159 l1OMOdPmReshapeB1
    12573 8041 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12573 8041 [2048, 1024]

private theorem l1OMOd_red_sm5032 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5032 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5031) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 68 l1OMOdSmViewA
    5031 5032 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5031 5032

private theorem l1OMOd_red_sm5036 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5036 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5035) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 69 l1OMOdSmViewB
    5035 5036 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5035 5036

private theorem l1OMOd_red_pm8034 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8034 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8032) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 169 l1OMOdPmViewA0
    8032 8034 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8032 8034

private theorem l1OMOd_red_pm8035 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8035 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8033) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 174 l1OMOdPmViewA1
    8033 8035 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8033 8035

private theorem l1OMOd_red_pm8046 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8046 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8044) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 170 l1OMOdPmViewB0
    8044 8046 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 8044 8046

private theorem l1OMOd_red_pm8047 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8047 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8045) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 175 l1OMOdPmViewB1
    8045 8047 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 8045 8047

private theorem l1OMOd_red_sm5038 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5038 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5037) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 73 l1OMOdSmReshapeDown
    5037 5038 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5037 5038 [4096, 512]

private theorem l1OMOd_red_pm8054 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8054 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8052) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 182 l1OMOdPmReshapeDown0
    8052 8054 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 8052 8054 [2048, 512]

private theorem l1OMOd_red_pm8055 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8055 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 8053) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 185 l1OMOdPmReshapeDown1
    8053 8055 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 8053 8055 [2048, 512]

private theorem l1OMOd_red_sm5041 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5041 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5040) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 75 l1OMOdSmViewDown
    5040 5041 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5040 5041

private theorem l1OMOd_red_pm8062 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8062 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8060) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 190 l1OMOdPmViewDown0
    8060 8062 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 8060 8062

private theorem l1OMOd_red_pm8063 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8063 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 8061) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 191 l1OMOdPmViewDown1
    8061 8063 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 8061 8063

private theorem l1OMOd_red_sm5031 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5031 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5029)
        (denoteGraphDistributedFaithful sm_goal_1 init 5030) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 64 l1OMOdSmLinearA
    5029 5030 5031 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5029 5030 5031

private theorem l1OMOd_red_sm5035 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5035 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5033)
        (denoteGraphDistributedFaithful sm_goal_1 init 5034) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 65 l1OMOdSmLinearB
    5033 5034 5035 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5033 5034 5035

private theorem l1OMOd_red_pm8032 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8032 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8028)
        (denoteGraphDistributedFaithful pm_goal_1 init 5030) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 161 l1OMOdPmLinearA0
    8028 5030 8032 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8028 5030 8032

private theorem l1OMOd_red_pm8033 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8033 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8029)
        (denoteGraphDistributedFaithful pm_goal_1 init 5030) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 166 l1OMOdPmLinearA1
    8029 5030 8033 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8029 5030 8033

private theorem l1OMOd_red_pm8044 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8044 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8040)
        (denoteGraphDistributedFaithful pm_goal_1 init 5034) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 162 l1OMOdPmLinearB0
    8040 5034 8044 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8040 5034 8044

private theorem l1OMOd_red_pm8045 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8045 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8041)
        (denoteGraphDistributedFaithful pm_goal_1 init 5034) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 167 l1OMOdPmLinearB1
    8041 5034 8045 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8041 5034 8045

private theorem l1OMOd_red_sm5037 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5037 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5032)
        (denoteGraphDistributedFaithful sm_goal_1 init 5036) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 72 l1OMOdSmSwi
    5032 5036 5037 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5032 5036 5037

private theorem l1OMOd_red_pm8052 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8052 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8034)
        (denoteGraphDistributedFaithful pm_goal_1 init 8046) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 177 l1OMOdPmSwi0
    8034 8046 8052 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 8034 8046 8052

private theorem l1OMOd_red_pm8053 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8053 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 8035)
        (denoteGraphDistributedFaithful pm_goal_1 init 8047) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 181 l1OMOdPmSwi1
    8035 8047 8053 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 8035 8047 8053

private theorem l1OMOd_red_sm5040 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5040 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5038)
        (denoteGraphDistributedFaithful sm_goal_1 init 5039) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 74 l1OMOdSmLinearDown
    5038 5039 5040 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5038 5039 5040

private theorem l1OMOd_red_pm8060 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8060 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8054)
        (denoteGraphDistributedFaithful pm_goal_1 init 5039) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 186 l1OMOdPmLinearDown0
    8054 5039 8060 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8054 5039 8060

private theorem l1OMOd_red_pm8061 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 8061 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 8055)
        (denoteGraphDistributedFaithful pm_goal_1 init 5039) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 189 l1OMOdPmLinearDown1
    8055 5039 8061 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8055 5039 8061

private theorem l1OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l1OMOd_weight_eq (initSM initPM : Store)
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
  rw [l1OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l1OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l1OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l1OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l1OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l1OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `5041 ↔ 8062/8063` ordinary relation. -/
theorem l1_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5037)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8053)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5041)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8063)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5038)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8055)
      [4096, 512] [2048, 512] := by
    rw [l1OMOd_red_sm5038 initSM, l1OMOd_red_pm8054 initPM, l1OMOd_red_pm8055 initPM]
    exact ordinary_view hSwi
  have hwD := l1OMOd_weight_eq initSM initPM hInit initGoal_5039 (by native_decide)
    5039 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l1OMOd_weight_shape initPM hPM 5039 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5040)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8061)
      [4096, 1024] [2048, 1024] := by
    rw [l1OMOd_red_sm5040 initSM, l1OMOd_red_pm8060 initPM,
      l1OMOd_red_pm8061 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l1OMOd_red_sm5041 initSM, l1OMOd_red_pm8062 initPM, l1OMOd_red_pm8063 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l1_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5014)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7996)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7997)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5041)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8063)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5029)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8028)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8029)
      [4096, 1024] [2048, 1024] := by
    rw [l1OMOd_red_sm5029 initSM, l1OMOd_red_pm8028 initPM,
      l1OMOd_red_pm8029 initPM, l1OMOd_red_sm12560 initSM,
      l1OMOd_red_pm12560 initPM, l1OMOd_red_pm12561 initPM]
    exact ordinary_view hNorm
  have hwA := l1OMOd_weight_eq initSM initPM hInit initGoal_5030 (by native_decide)
    5030 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l1OMOd_weight_shape initPM hPM 5030 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8032)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8033)
      [4096, 512] [2048, 512] := by
    rw [l1OMOd_red_sm5031 initSM, l1OMOd_red_pm8032 initPM,
      l1OMOd_red_pm8033 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5032)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8034)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8035)
      [4096, 512] [2048, 512] := by
    rw [l1OMOd_red_sm5032 initSM, l1OMOd_red_pm8034 initPM,
      l1OMOd_red_pm8035 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5033)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8040)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8041)
      [4096, 1024] [2048, 1024] := by
    rw [l1OMOd_red_sm5033 initSM, l1OMOd_red_pm8040 initPM,
      l1OMOd_red_pm8041 initPM, l1OMOd_red_sm12572 initSM,
      l1OMOd_red_pm12572 initPM, l1OMOd_red_pm12573 initPM]
    exact ordinary_view hNorm
  have hwB := l1OMOd_weight_eq initSM initPM hInit initGoal_5034 (by native_decide)
    5034 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l1OMOd_weight_shape initPM hPM 5034 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5035)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8045)
      [4096, 512] [2048, 512] := by
    rw [l1OMOd_red_sm5035 initSM, l1OMOd_red_pm8044 initPM,
      l1OMOd_red_pm8045 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5036)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8047)
      [4096, 512] [2048, 512] := by
    rw [l1OMOd_red_sm5036 initSM, l1OMOd_red_pm8046 initPM,
      l1OMOd_red_pm8047 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5037)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8053)
      [4096, 512] [2048, 512] := by
    rw [l1OMOd_red_sm5037 initSM, l1OMOd_red_pm8052 initPM,
      l1OMOd_red_pm8053 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l1_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l1_ordinary_moe_down_from_swiglu
#print axioms l1_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
