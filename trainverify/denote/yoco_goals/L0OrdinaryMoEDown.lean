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

private def l0OMOdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4959], outs := [7776, 7780, 7784, 7788, 7792], params := [5] }

private def l0OMOdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7832], outs := [15296, 12410, 12420, 12434, 12446], params := [5] }

private def l0OMOdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7833], outs := [15298, 12411, 12421, 12435, 12447], params := [5] }

private def l0OMOdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7788], outs := [4974], params := [4096, 1024] }

private def l0OMOdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7792], outs := [4978], params := [4096, 1024] }

private def l0OMOdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12434], outs := [7864], params := [2048, 1024] }

private def l0OMOdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12435], outs := [7865], params := [2048, 1024] }

private def l0OMOdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12446], outs := [7876], params := [2048, 1024] }

private def l0OMOdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12447], outs := [7877], params := [2048, 1024] }

private def l0OMOdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4974, 4975], outs := [4976] }

private def l0OMOdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4978, 4979], outs := [4980] }

private def l0OMOdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7864, 4975], outs := [7868] }

private def l0OMOdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7865, 4975], outs := [7869] }

private def l0OMOdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7876, 4979], outs := [7880] }

private def l0OMOdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7877, 4979], outs := [7881] }

private def l0OMOdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [4976], outs := [4977], params := [4096, 512] }

private def l0OMOdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [4980], outs := [4981], params := [4096, 512] }

private def l0OMOdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [7868], outs := [7870], params := [2048, 512] }

private def l0OMOdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [7869], outs := [7871], params := [2048, 512] }

private def l0OMOdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [7880], outs := [7882], params := [2048, 512] }

private def l0OMOdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [7881], outs := [7883], params := [2048, 512] }

private def l0OMOdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [4977, 4981], outs := [4982] }

private def l0OMOdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [7870, 7882], outs := [7888] }

private def l0OMOdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [7871, 7883], outs := [7889] }

private def l0OMOdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [4982], outs := [4983], params := [4096, 512] }

private def l0OMOdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7888], outs := [7890], params := [2048, 512] }

private def l0OMOdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [7889], outs := [7891], params := [2048, 512] }

private def l0OMOdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4983, 4984], outs := [4985] }

private def l0OMOdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7890, 4984], outs := [7896] }

private def l0OMOdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7891, 4984], outs := [7897] }

private def l0OMOdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [4985], outs := [4986], params := [4096, 1024] }

private def l0OMOdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [7896], outs := [7898], params := [2048, 1024] }

private def l0OMOdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [7897], outs := [7899], params := [2048, 1024] }

private theorem l0OMOd_red_sm12434 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7788 =
      denoteGraphDistributedFaithful sm_goal_1 init 4959 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 18 l0OMOdSmRef
    4959 7788 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 4959 [7776, 7780, 7784, 7788, 7792] 5 rfl 7788 (by decide)

private theorem l0OMOd_red_sm12446 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 7792 =
      denoteGraphDistributedFaithful sm_goal_1 init 4959 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 18 l0OMOdSmRef
    4959 7792 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 4959 [7776, 7780, 7784, 7788, 7792] 5 rfl 7792 (by decide)

private theorem l0OMOd_red_pm12434 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12434 =
      denoteGraphDistributedFaithful pm_goal_1 init 7832 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 67 l0OMOdPmRef0
    7832 12434 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7832 [15296, 12410, 12420, 12434, 12446] 5 rfl 12434 (by decide)

private theorem l0OMOd_red_pm12446 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12446 =
      denoteGraphDistributedFaithful pm_goal_1 init 7832 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 67 l0OMOdPmRef0
    7832 12446 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7832 [15296, 12410, 12420, 12434, 12446] 5 rfl 12446 (by decide)

private theorem l0OMOd_red_pm12435 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12435 =
      denoteGraphDistributedFaithful pm_goal_1 init 7833 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 68 l0OMOdPmRef1
    7833 12435 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7833 [15298, 12411, 12421, 12435, 12447] 5 rfl 12435 (by decide)

private theorem l0OMOd_red_pm12447 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 12447 =
      denoteGraphDistributedFaithful pm_goal_1 init 7833 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 68 l0OMOdPmRef1
    7833 12447 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7833 [15298, 12411, 12421, 12435, 12447] 5 rfl 12447 (by decide)

private theorem l0OMOd_red_sm4974 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4974 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7788) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 21 l0OMOdSmReshapeA
    7788 4974 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7788 4974 [4096, 1024]

private theorem l0OMOd_red_sm4978 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4978 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 7792) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 22 l0OMOdSmReshapeB
    7792 4978 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7792 4978 [4096, 1024]

private theorem l0OMOd_red_pm7864 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7864 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12434) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 70 l0OMOdPmReshapeA0
    12434 7864 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12434 7864 [2048, 1024]

private theorem l0OMOd_red_pm7865 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7865 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12435) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 74 l0OMOdPmReshapeA1
    12435 7865 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12435 7865 [2048, 1024]

private theorem l0OMOd_red_pm7876 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7876 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12446) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 71 l0OMOdPmReshapeB0
    12446 7876 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12446 7876 [2048, 1024]

private theorem l0OMOd_red_pm7877 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7877 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 12447) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 75 l0OMOdPmReshapeB1
    12447 7877 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12447 7877 [2048, 1024]

private theorem l0OMOd_red_sm4977 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4977 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 4976) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 29 l0OMOdSmViewA
    4976 4977 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 4976 4977

private theorem l0OMOd_red_sm4981 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4981 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 4980) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 30 l0OMOdSmViewB
    4980 4981 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 4980 4981

private theorem l0OMOd_red_pm7870 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7870 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 7868) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 85 l0OMOdPmViewA0
    7868 7870 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 7868 7870

private theorem l0OMOd_red_pm7871 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7871 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 7869) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 90 l0OMOdPmViewA1
    7869 7871 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 7869 7871

private theorem l0OMOd_red_pm7882 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7882 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 7880) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 86 l0OMOdPmViewB0
    7880 7882 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 7880 7882

private theorem l0OMOd_red_pm7883 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7883 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 7881) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 91 l0OMOdPmViewB1
    7881 7883 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 7881 7883

private theorem l0OMOd_red_sm4983 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4983 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 4982) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 34 l0OMOdSmReshapeDown
    4982 4983 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 4982 4983 [4096, 512]

private theorem l0OMOd_red_pm7890 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7890 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 7888) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 98 l0OMOdPmReshapeDown0
    7888 7890 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 7888 7890 [2048, 512]

private theorem l0OMOd_red_pm7891 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7891 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 7889) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 101 l0OMOdPmReshapeDown1
    7889 7891 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 7889 7891 [2048, 512]

private theorem l0OMOd_red_sm4986 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4986 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 4985) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 36 l0OMOdSmViewDown
    4985 4986 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 4985 4986

private theorem l0OMOd_red_pm7898 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7898 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 7896) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 106 l0OMOdPmViewDown0
    7896 7898 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 7896 7898

private theorem l0OMOd_red_pm7899 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7899 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 7897) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 107 l0OMOdPmViewDown1
    7897 7899 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 7897 7899

private theorem l0OMOd_red_sm4976 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4976 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 4974)
        (denoteGraphDistributedFaithful sm_goal_1 init 4975) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 25 l0OMOdSmLinearA
    4974 4975 4976 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 4974 4975 4976

private theorem l0OMOd_red_sm4980 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4980 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 4978)
        (denoteGraphDistributedFaithful sm_goal_1 init 4979) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 26 l0OMOdSmLinearB
    4978 4979 4980 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 4978 4979 4980

private theorem l0OMOd_red_pm7868 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7868 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 7864)
        (denoteGraphDistributedFaithful pm_goal_1 init 4975) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 77 l0OMOdPmLinearA0
    7864 4975 7868 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 7864 4975 7868

private theorem l0OMOd_red_pm7869 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7869 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 7865)
        (denoteGraphDistributedFaithful pm_goal_1 init 4975) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 82 l0OMOdPmLinearA1
    7865 4975 7869 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 7865 4975 7869

private theorem l0OMOd_red_pm7880 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7880 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 7876)
        (denoteGraphDistributedFaithful pm_goal_1 init 4979) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 78 l0OMOdPmLinearB0
    7876 4979 7880 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 7876 4979 7880

private theorem l0OMOd_red_pm7881 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7881 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 7877)
        (denoteGraphDistributedFaithful pm_goal_1 init 4979) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 83 l0OMOdPmLinearB1
    7877 4979 7881 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 7877 4979 7881

private theorem l0OMOd_red_sm4982 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4982 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 4977)
        (denoteGraphDistributedFaithful sm_goal_1 init 4981) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 33 l0OMOdSmSwi
    4977 4981 4982 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 4977 4981 4982

private theorem l0OMOd_red_pm7888 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7888 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 7870)
        (denoteGraphDistributedFaithful pm_goal_1 init 7882) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 93 l0OMOdPmSwi0
    7870 7882 7888 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 7870 7882 7888

private theorem l0OMOd_red_pm7889 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7889 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 7871)
        (denoteGraphDistributedFaithful pm_goal_1 init 7883) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 97 l0OMOdPmSwi1
    7871 7883 7889 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 7871 7883 7889

private theorem l0OMOd_red_sm4985 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 4985 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 4983)
        (denoteGraphDistributedFaithful sm_goal_1 init 4984) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 35 l0OMOdSmLinearDown
    4983 4984 4985 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 4983 4984 4985

private theorem l0OMOd_red_pm7896 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7896 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 7890)
        (denoteGraphDistributedFaithful pm_goal_1 init 4984) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 102 l0OMOdPmLinearDown0
    7890 4984 7896 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 7890 4984 7896

private theorem l0OMOd_red_pm7897 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 7897 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 7891)
        (denoteGraphDistributedFaithful pm_goal_1 init 4984) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 105 l0OMOdPmLinearDown1
    7891 4984 7897 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMOdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 7891 4984 7897

private theorem l0OMOd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l0OMOd_weight_eq (initSM initPM : Store)
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
  rw [l0OMOd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l0OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l0OMOd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l0OMOd_leaf pm_goal_1 initPM W (by native_decide) hpm]
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
private theorem l0OMOd_swiglu_allGather0_commute_2 (a b c d : Tensor) (shard hidden : Nat)
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
  exact l0OMOd_swiglu_allGather0_commute_2 rankA0 rankA1 rankB0 rankB1
    lDim hidden hl hh hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape

/-- Conditional ordinary down-projection tail.  Starting from the computed
SwiGLU output relation, the theorem reduces the real reshape, down-linear, and
view nodes and derives the final `4986 ↔ 7898/7899` ordinary relation. -/
theorem l0_ordinary_moe_down_from_swiglu (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7888)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7889)
      [4096, 512] [2048, 512]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4986)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7898)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7899)
      [4096, 1024] [2048, 1024] := by
  have hSwiR : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7891)
      [4096, 512] [2048, 512] := by
    rw [l0OMOd_red_sm4983 initSM, l0OMOd_red_pm7890 initPM, l0OMOd_red_pm7891 initPM]
    exact ordinary_view hSwi
  have hwD := l0OMOd_weight_eq initSM initPM hInit initGoal_4984 (by native_decide)
    4984 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l0OMOd_weight_shape initPM hPM 4984 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4985)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7897)
      [4096, 1024] [2048, 1024] := by
    rw [l0OMOd_red_sm4985 initSM, l0OMOd_red_pm7896 initPM,
      l0OMOd_red_pm7897 initPM, hwD]
    exact ordinary_linear 2048 512 1024 hSwiR hsD (by decide) (by decide) (by decide)
  rw [l0OMOd_red_sm4986 initSM, l0OMOd_red_pm7898 initPM, l0OMOd_red_pm7899 initPM]
  exact ordinary_view hDownLinear

/-- The complete ordinary replicated MLP/down branch, starting at the normalized
attention output.  No computed SwiGLU intermediate is exposed to the caller. -/
theorem l0_ordinary_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hNorm : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4959)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7832)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7833)
      [4096, 1024] [2048, 1024]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4986)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7898)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7899)
      [4096, 1024] [2048, 1024] := by
  have hReshapeA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4974)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7864)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7865)
      [4096, 1024] [2048, 1024] := by
    rw [l0OMOd_red_sm4974 initSM, l0OMOd_red_pm7864 initPM,
      l0OMOd_red_pm7865 initPM, l0OMOd_red_sm12434 initSM,
      l0OMOd_red_pm12434 initPM, l0OMOd_red_pm12435 initPM]
    exact ordinary_view hNorm
  have hwA := l0OMOd_weight_eq initSM initPM hInit initGoal_4975 (by native_decide)
    4975 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l0OMOd_weight_shape initPM hPM 4975 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4976)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7868)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7869)
      [4096, 512] [2048, 512] := by
    rw [l0OMOd_red_sm4976 initSM, l0OMOd_red_pm7868 initPM,
      l0OMOd_red_pm7869 initPM, hwA]
    exact ordinary_linear 2048 1024 512 hReshapeA hsA
      (by decide) (by decide) (by decide)
  have hViewA : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7870)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7871)
      [4096, 512] [2048, 512] := by
    rw [l0OMOd_red_sm4977 initSM, l0OMOd_red_pm7870 initPM,
      l0OMOd_red_pm7871 initPM]
    exact ordinary_view hLinearA
  have hReshapeB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4978)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7876)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7877)
      [4096, 1024] [2048, 1024] := by
    rw [l0OMOd_red_sm4978 initSM, l0OMOd_red_pm7876 initPM,
      l0OMOd_red_pm7877 initPM, l0OMOd_red_sm12446 initSM,
      l0OMOd_red_pm12446 initPM, l0OMOd_red_pm12447 initPM]
    exact ordinary_view hNorm
  have hwB := l0OMOd_weight_eq initSM initPM hInit initGoal_4979 (by native_decide)
    4979 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsB := l0OMOd_weight_shape initPM hPM 4979 [512, 1024]
    (by native_decide) (by native_decide)
  have hLinearB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4980)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7880)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7881)
      [4096, 512] [2048, 512] := by
    rw [l0OMOd_red_sm4980 initSM, l0OMOd_red_pm7880 initPM,
      l0OMOd_red_pm7881 initPM, hwB]
    exact ordinary_linear 2048 1024 512 hReshapeB hsB
      (by decide) (by decide) (by decide)
  have hViewB : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4981)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7883)
      [4096, 512] [2048, 512] := by
    rw [l0OMOd_red_sm4981 initSM, l0OMOd_red_pm7882 initPM,
      l0OMOd_red_pm7883 initPM]
    exact ordinary_view hLinearB
  have hSwi : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7888)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7889)
      [4096, 512] [2048, 512] := by
    rw [l0OMOd_red_sm4982 initSM, l0OMOd_red_pm7888 initPM,
      l0OMOd_red_pm7889 initPM]
    exact ordinary_swiglu 2048 512 hViewA hViewB (by decide) (by decide)
  exact l0_ordinary_moe_down_from_swiglu initSM initPM hPM hInit hSwi

#print axioms l0_ordinary_moe_down_from_swiglu
#print axioms l0_ordinary_moe_down_from_norm_input

end
end TrainVerify.Denote.GeneratedPatterns
