/- Canonical Goal 1, layer 17: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L17ZigzagMoEResidualGate

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

private def l17ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6000], outs := [8792, 8796, 8800, 8804, 8808], params := [5] }

private def l17ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10896], outs := [15416, 14744, 14754, 14768, 14780], params := [5] }

private def l17ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10897], outs := [15418, 14745, 14755, 14769, 14781], params := [5] }

private def l17ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8804], outs := [6015], params := [4096, 1024] }

private def l17ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8808], outs := [6019], params := [4096, 1024] }

private def l17ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14768], outs := [10928], params := [2048, 1024] }

private def l17ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14769], outs := [10929], params := [2048, 1024] }

private def l17ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14780], outs := [10940], params := [2048, 1024] }

private def l17ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14781], outs := [10941], params := [2048, 1024] }

private def l17ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6015, 6016], outs := [6017] }

private def l17ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6019, 6020], outs := [6021] }

private def l17ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10928, 6016], outs := [10932] }

private def l17ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10929, 6016], outs := [10933] }

private def l17ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10940, 6020], outs := [10944] }

private def l17ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10941, 6020], outs := [10945] }

private def l17ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6017], outs := [6018], params := [4096, 512] }

private def l17ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6021], outs := [6022], params := [4096, 512] }

private def l17ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10932], outs := [10934], params := [2048, 512] }

private def l17ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10933], outs := [10935], params := [2048, 512] }

private def l17ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10944], outs := [10946], params := [2048, 512] }

private def l17ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10945], outs := [10947], params := [2048, 512] }

private def l17ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [6018, 6022], outs := [6023] }

private def l17ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10934, 10946], outs := [10952] }

private def l17ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10935, 10947], outs := [10953] }

private def l17ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6023], outs := [6024], params := [4096, 512] }

private def l17ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10952], outs := [10954], params := [2048, 512] }

private def l17ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10953], outs := [10955], params := [2048, 512] }

private def l17ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6024, 6025], outs := [6026] }

private def l17ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10954, 6025], outs := [10960] }

private def l17ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10955, 6025], outs := [10961] }

private def l17ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6026], outs := [6027], params := [4096, 1024] }

private def l17ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10960], outs := [10962], params := [2048, 1024] }

private def l17ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10961], outs := [10963], params := [2048, 1024] }

private theorem l17ZMd_red_sm8804 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8804 =
      denoteGraphDistributedFaithful sm_goal_1 init 6000 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 759 l17ZMdSmRef
    6000 8804 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6000 [8948, 8952, 8956, 8804, 8808] 5 rfl 8804 (by decide)

private theorem l17ZMd_red_sm8808 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8808 =
      denoteGraphDistributedFaithful sm_goal_1 init 6000 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 759 l17ZMdSmRef
    6000 8808 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6000 [8948, 8952, 8956, 8804, 8808] 5 rfl 8808 (by decide)

private theorem l17ZMd_red_pm14768 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14768 =
      denoteGraphDistributedFaithful pm_goal_1 init 10896 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1663 l17ZMdPmRef0
    10896 14768 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10896 [15416, 14744, 14754, 14768, 14780] 5 rfl 14768 (by decide)

private theorem l17ZMd_red_pm14780 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14780 =
      denoteGraphDistributedFaithful pm_goal_1 init 10896 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1663 l17ZMdPmRef0
    10896 14780 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10896 [15416, 14744, 14754, 14768, 14780] 5 rfl 14780 (by decide)

private theorem l17ZMd_red_pm14769 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14769 =
      denoteGraphDistributedFaithful pm_goal_1 init 10897 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1664 l17ZMdPmRef1
    10897 14769 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10897 [15418, 14745, 14755, 14769, 14781] 5 rfl 14769 (by decide)

private theorem l17ZMd_red_pm14781 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14781 =
      denoteGraphDistributedFaithful pm_goal_1 init 10897 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1664 l17ZMdPmRef1
    10897 14781 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10897 [15418, 14745, 14755, 14769, 14781] 5 rfl 14781 (by decide)

private theorem l17ZMd_red_sm6015 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6015 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8804) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 762 l17ZMdSmReshapeA
    8804 6015 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8804 6015 [4096, 1024]

private theorem l17ZMd_red_sm6019 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6019 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8808) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 763 l17ZMdSmReshapeB
    8808 6019 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8808 6019 [4096, 1024]

private theorem l17ZMd_red_pm10928 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10928 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14768) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1666 l17ZMdPmReshapeA0
    14768 10928 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14768 10928 [2048, 1024]

private theorem l17ZMd_red_pm10929 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10929 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14769) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1670 l17ZMdPmReshapeA1
    14769 10929 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14769 10929 [2048, 1024]

private theorem l17ZMd_red_pm10940 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10940 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14780) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1667 l17ZMdPmReshapeB0
    14780 10940 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14780 10940 [2048, 1024]

private theorem l17ZMd_red_pm10941 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10941 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14781) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1671 l17ZMdPmReshapeB1
    14781 10941 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14781 10941 [2048, 1024]

private theorem l17ZMd_red_sm6018 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6018 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6017) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 770 l17ZMdSmViewA
    6017 6018 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6017 6018

private theorem l17ZMd_red_sm6022 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6022 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6021) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 771 l17ZMdSmViewB
    6021 6022 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6021 6022

private theorem l17ZMd_red_pm10934 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10934 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10932) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1681 l17ZMdPmViewA0
    10932 10934 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10932 10934

private theorem l17ZMd_red_pm10935 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10935 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10933) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1686 l17ZMdPmViewA1
    10933 10935 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10933 10935

private theorem l17ZMd_red_pm10946 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10946 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10944) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1682 l17ZMdPmViewB0
    10944 10946 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10944 10946

private theorem l17ZMd_red_pm10947 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10947 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10945) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1687 l17ZMdPmViewB1
    10945 10947 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10945 10947

private theorem l17ZMd_red_sm6024 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6024 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6023) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 775 l17ZMdSmReshapeDown
    6023 6024 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6023 6024 [4096, 512]

private theorem l17ZMd_red_pm10954 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10954 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10952) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1694 l17ZMdPmReshapeDown0
    10952 10954 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10952 10954 [2048, 512]

private theorem l17ZMd_red_pm10955 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10955 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10953) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1697 l17ZMdPmReshapeDown1
    10953 10955 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10953 10955 [2048, 512]

private theorem l17ZMd_red_sm6027 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6027 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 6026) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 777 l17ZMdSmViewDown
    6026 6027 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6026 6027

private theorem l17ZMd_red_pm10962 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10962 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10960) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1702 l17ZMdPmViewDown0
    10960 10962 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10960 10962

private theorem l17ZMd_red_pm10963 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10963 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10961) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1703 l17ZMdPmViewDown1
    10961 10963 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10961 10963

private theorem l17ZMd_red_sm6017 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6017 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6015)
        (denoteGraphDistributedFaithful sm_goal_1 init 6016) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 766 l17ZMdSmLinearA
    6015 6016 6017 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6015 6016 6017

private theorem l17ZMd_red_sm6021 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6021 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6019)
        (denoteGraphDistributedFaithful sm_goal_1 init 6020) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 767 l17ZMdSmLinearB
    6019 6020 6021 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6019 6020 6021

private theorem l17ZMd_red_pm10932 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10932 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10928)
        (denoteGraphDistributedFaithful pm_goal_1 init 6016) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1673 l17ZMdPmLinearA0
    10928 6016 10932 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10928 6016 10932

private theorem l17ZMd_red_pm10933 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10933 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10929)
        (denoteGraphDistributedFaithful pm_goal_1 init 6016) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1678 l17ZMdPmLinearA1
    10929 6016 10933 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10929 6016 10933

private theorem l17ZMd_red_pm10944 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10944 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10940)
        (denoteGraphDistributedFaithful pm_goal_1 init 6020) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1674 l17ZMdPmLinearB0
    10940 6020 10944 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10940 6020 10944

private theorem l17ZMd_red_pm10945 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10945 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10941)
        (denoteGraphDistributedFaithful pm_goal_1 init 6020) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1679 l17ZMdPmLinearB1
    10941 6020 10945 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10941 6020 10945

private theorem l17ZMd_red_sm6023 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6023 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 6018)
        (denoteGraphDistributedFaithful sm_goal_1 init 6022) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 774 l17ZMdSmSwi
    6018 6022 6023 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 6018 6022 6023

private theorem l17ZMd_red_pm10952 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10952 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10934)
        (denoteGraphDistributedFaithful pm_goal_1 init 10946) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1689 l17ZMdPmSwi0
    10934 10946 10952 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 10934 10946 10952

private theorem l17ZMd_red_pm10953 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10953 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10935)
        (denoteGraphDistributedFaithful pm_goal_1 init 10947) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1693 l17ZMdPmSwi1
    10935 10947 10953 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 10935 10947 10953

private theorem l17ZMd_red_sm6026 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6026 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6024)
        (denoteGraphDistributedFaithful sm_goal_1 init 6025) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 776 l17ZMdSmLinearDown
    6024 6025 6026 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6024 6025 6026

private theorem l17ZMd_red_pm10960 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10960 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10954)
        (denoteGraphDistributedFaithful pm_goal_1 init 6025) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1698 l17ZMdPmLinearDown0
    10954 6025 10960 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10954 6025 10960

private theorem l17ZMd_red_pm10961 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10961 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10955)
        (denoteGraphDistributedFaithful pm_goal_1 init 6025) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1701 l17ZMdPmLinearDown1
    10955 6025 10961 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10955 6025 10961

private theorem l17ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l17ZMd_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid)
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
  rw [l17ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l17ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l17ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l17ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L17 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l17_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6027)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10962)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10963)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8804)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14768)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14769)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMd_red_sm8804 initSM, l17ZMd_red_pm14768 initPM, l17ZMd_red_pm14769 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8808)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14780)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14781)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMd_red_sm8808 initSM, l17ZMd_red_pm14780 initPM, l17ZMd_red_pm14781 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6015)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10928)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10929)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMd_red_sm6015 initSM, l17ZMd_red_pm10928 initPM, l17ZMd_red_pm10929 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6019)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10940)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10941)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMd_red_sm6019 initSM, l17ZMd_red_pm10940 initPM, l17ZMd_red_pm10941 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l17ZMd_weight_eq initSM initPM hInit initGoal_6016 (by native_decide)
    6016 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l17ZMd_weight_eq initSM initPM hInit initGoal_6020 (by native_decide)
    6020 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l17ZMd_weight_shape initPM hPM 6016 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l17ZMd_weight_shape initPM hPM 6020 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6017)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10932)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l17ZMd_red_sm6017 initSM, l17ZMd_red_pm10932 initPM,
      l17ZMd_red_pm10933 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6021)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10945)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l17ZMd_red_sm6021 initSM, l17ZMd_red_pm10944 initPM,
      l17ZMd_red_pm10945 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6018)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10934)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10935)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l17ZMd_red_sm6018 initSM, l17ZMd_red_pm10934 initPM, l17ZMd_red_pm10935 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6022)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10947)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l17ZMd_red_sm6022 initSM, l17ZMd_red_pm10946 initPM, l17ZMd_red_pm10947 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6018)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10934)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10935)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6022)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10947)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6023)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10952)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10953)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l17ZMd_red_sm6023 initSM, l17ZMd_red_pm10952 initPM, l17ZMd_red_pm10953 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6024)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10954)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10955)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l17ZMd_red_sm6024 initSM, l17ZMd_red_pm10954 initPM, l17ZMd_red_pm10955 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l17ZMd_weight_eq initSM initPM hInit initGoal_6025 (by native_decide)
    6025 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l17ZMd_weight_shape initPM hPM 6025 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6026)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10960)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10961)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l17ZMd_red_sm6026 initSM, l17ZMd_red_pm10960 initPM,
      l17ZMd_red_pm10961 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l17ZMd_red_sm6027 initSM, l17ZMd_red_pm10962 initPM, l17ZMd_red_pm10963 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
