/- Canonical Goal 1, layer 19: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L19ZigzagMoEResidualGate

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

private def l19ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6108], outs := [8870, 8874, 8878, 8882, 8886], params := [5] }

private def l19ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11204], outs := [15424, 14976, 14986, 15000, 15012], params := [5] }

private def l19ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11205], outs := [15426, 14977, 14987, 15001, 15013], params := [5] }

private def l19ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8882], outs := [6123], params := [4096, 1024] }

private def l19ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8886], outs := [6127], params := [4096, 1024] }

private def l19ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15000], outs := [11236], params := [2048, 1024] }

private def l19ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15001], outs := [11237], params := [2048, 1024] }

private def l19ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15012], outs := [11248], params := [2048, 1024] }

private def l19ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15013], outs := [11249], params := [2048, 1024] }

private def l19ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6123, 6124], outs := [6125] }

private def l19ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6127, 6128], outs := [6129] }

private def l19ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11236, 6124], outs := [11240] }

private def l19ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11237, 6124], outs := [11241] }

private def l19ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11248, 6128], outs := [11252] }

private def l19ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11249, 6128], outs := [11253] }

private def l19ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6125], outs := [6126], params := [4096, 512] }

private def l19ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6129], outs := [6130], params := [4096, 512] }

private def l19ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11240], outs := [11242], params := [2048, 512] }

private def l19ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11241], outs := [11243], params := [2048, 512] }

private def l19ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11252], outs := [11254], params := [2048, 512] }

private def l19ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11253], outs := [11255], params := [2048, 512] }

private def l19ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [6126, 6130], outs := [6131] }

private def l19ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11242, 11254], outs := [11260] }

private def l19ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11243, 11255], outs := [11261] }

private def l19ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6131], outs := [6132], params := [4096, 512] }

private def l19ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11260], outs := [11262], params := [2048, 512] }

private def l19ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11261], outs := [11263], params := [2048, 512] }

private def l19ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6132, 6133], outs := [6134] }

private def l19ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11262, 6133], outs := [11268] }

private def l19ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11263, 6133], outs := [11269] }

private def l19ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6134], outs := [6135], params := [4096, 1024] }

private def l19ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11268], outs := [11270], params := [2048, 1024] }

private def l19ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11269], outs := [11271], params := [2048, 1024] }

private theorem l19ZMd_red_sm8882 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8882 =
      denoteGraphDistributedFaithful sm_goal_1 init 6108 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 829 l19ZMdSmRef
    6108 8882 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6108 [8948, 8952, 8956, 8882, 8886] 5 rfl 8882 (by decide)

private theorem l19ZMd_red_sm8886 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8886 =
      denoteGraphDistributedFaithful sm_goal_1 init 6108 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 829 l19ZMdSmRef
    6108 8886 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6108 [8948, 8952, 8956, 8882, 8886] 5 rfl 8886 (by decide)

private theorem l19ZMd_red_pm15000 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15000 =
      denoteGraphDistributedFaithful pm_goal_1 init 11204 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1815 l19ZMdPmRef0
    11204 15000 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11204 [15424, 14976, 14986, 15000, 15012] 5 rfl 15000 (by decide)

private theorem l19ZMd_red_pm15012 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15012 =
      denoteGraphDistributedFaithful pm_goal_1 init 11204 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1815 l19ZMdPmRef0
    11204 15012 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11204 [15424, 14976, 14986, 15000, 15012] 5 rfl 15012 (by decide)

private theorem l19ZMd_red_pm15001 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15001 =
      denoteGraphDistributedFaithful pm_goal_1 init 11205 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1816 l19ZMdPmRef1
    11205 15001 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11205 [15426, 14977, 14987, 15001, 15013] 5 rfl 15001 (by decide)

private theorem l19ZMd_red_pm15013 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15013 =
      denoteGraphDistributedFaithful pm_goal_1 init 11205 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1816 l19ZMdPmRef1
    11205 15013 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11205 [15426, 14977, 14987, 15001, 15013] 5 rfl 15013 (by decide)

private theorem l19ZMd_red_sm6123 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6123 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8882) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 832 l19ZMdSmReshapeA
    8882 6123 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8882 6123 [4096, 1024]

private theorem l19ZMd_red_sm6127 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6127 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8886) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 833 l19ZMdSmReshapeB
    8886 6127 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8886 6127 [4096, 1024]

private theorem l19ZMd_red_pm11236 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11236 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15000) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1818 l19ZMdPmReshapeA0
    15000 11236 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15000 11236 [2048, 1024]

private theorem l19ZMd_red_pm11237 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11237 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15001) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1822 l19ZMdPmReshapeA1
    15001 11237 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15001 11237 [2048, 1024]

private theorem l19ZMd_red_pm11248 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11248 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15012) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1819 l19ZMdPmReshapeB0
    15012 11248 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15012 11248 [2048, 1024]

private theorem l19ZMd_red_pm11249 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11249 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15013) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1823 l19ZMdPmReshapeB1
    15013 11249 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15013 11249 [2048, 1024]

private theorem l19ZMd_red_sm6126 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6126 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6125) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 840 l19ZMdSmViewA
    6125 6126 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6125 6126

private theorem l19ZMd_red_sm6130 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6130 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6129) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 841 l19ZMdSmViewB
    6129 6130 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6129 6130

private theorem l19ZMd_red_pm11242 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11242 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11240) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1833 l19ZMdPmViewA0
    11240 11242 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11240 11242

private theorem l19ZMd_red_pm11243 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11243 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11241) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1838 l19ZMdPmViewA1
    11241 11243 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11241 11243

private theorem l19ZMd_red_pm11254 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11254 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11252) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1834 l19ZMdPmViewB0
    11252 11254 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11252 11254

private theorem l19ZMd_red_pm11255 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11255 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11253) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1839 l19ZMdPmViewB1
    11253 11255 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11253 11255

private theorem l19ZMd_red_sm6132 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6132 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6131) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 845 l19ZMdSmReshapeDown
    6131 6132 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6131 6132 [4096, 512]

private theorem l19ZMd_red_pm11262 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11262 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11260) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1846 l19ZMdPmReshapeDown0
    11260 11262 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11260 11262 [2048, 512]

private theorem l19ZMd_red_pm11263 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11263 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11261) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1849 l19ZMdPmReshapeDown1
    11261 11263 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11261 11263 [2048, 512]

private theorem l19ZMd_red_sm6135 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6135 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 6134) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 847 l19ZMdSmViewDown
    6134 6135 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6134 6135

private theorem l19ZMd_red_pm11270 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11270 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11268) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1854 l19ZMdPmViewDown0
    11268 11270 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11268 11270

private theorem l19ZMd_red_pm11271 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11271 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11269) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1855 l19ZMdPmViewDown1
    11269 11271 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11269 11271

private theorem l19ZMd_red_sm6125 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6125 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6123)
        (denoteGraphDistributedFaithful sm_goal_1 init 6124) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 836 l19ZMdSmLinearA
    6123 6124 6125 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6123 6124 6125

private theorem l19ZMd_red_sm6129 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6129 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6127)
        (denoteGraphDistributedFaithful sm_goal_1 init 6128) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 837 l19ZMdSmLinearB
    6127 6128 6129 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6127 6128 6129

private theorem l19ZMd_red_pm11240 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11240 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11236)
        (denoteGraphDistributedFaithful pm_goal_1 init 6124) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1825 l19ZMdPmLinearA0
    11236 6124 11240 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11236 6124 11240

private theorem l19ZMd_red_pm11241 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11241 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11237)
        (denoteGraphDistributedFaithful pm_goal_1 init 6124) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1830 l19ZMdPmLinearA1
    11237 6124 11241 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11237 6124 11241

private theorem l19ZMd_red_pm11252 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11252 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11248)
        (denoteGraphDistributedFaithful pm_goal_1 init 6128) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1826 l19ZMdPmLinearB0
    11248 6128 11252 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11248 6128 11252

private theorem l19ZMd_red_pm11253 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11253 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11249)
        (denoteGraphDistributedFaithful pm_goal_1 init 6128) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1831 l19ZMdPmLinearB1
    11249 6128 11253 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11249 6128 11253

private theorem l19ZMd_red_sm6131 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6131 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 6126)
        (denoteGraphDistributedFaithful sm_goal_1 init 6130) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 844 l19ZMdSmSwi
    6126 6130 6131 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 6126 6130 6131

private theorem l19ZMd_red_pm11260 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11260 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11242)
        (denoteGraphDistributedFaithful pm_goal_1 init 11254) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1841 l19ZMdPmSwi0
    11242 11254 11260 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 11242 11254 11260

private theorem l19ZMd_red_pm11261 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11261 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11243)
        (denoteGraphDistributedFaithful pm_goal_1 init 11255) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1845 l19ZMdPmSwi1
    11243 11255 11261 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 11243 11255 11261

private theorem l19ZMd_red_sm6134 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6134 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6132)
        (denoteGraphDistributedFaithful sm_goal_1 init 6133) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 846 l19ZMdSmLinearDown
    6132 6133 6134 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6132 6133 6134

private theorem l19ZMd_red_pm11268 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11268 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11262)
        (denoteGraphDistributedFaithful pm_goal_1 init 6133) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1850 l19ZMdPmLinearDown0
    11262 6133 11268 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11262 6133 11268

private theorem l19ZMd_red_pm11269 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11269 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11263)
        (denoteGraphDistributedFaithful pm_goal_1 init 6133) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1853 l19ZMdPmLinearDown1
    11263 6133 11269 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l19ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11263 6133 11269

private theorem l19ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l19ZMd_weight_eq (initSM initPM : Store)
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
  rw [l19ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l19ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l19ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l19ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L19 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l19_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11204)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11205)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6135)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11270)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11271)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8882)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15001)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMd_red_sm8882 initSM, l19ZMd_red_pm15000 initPM, l19ZMd_red_pm15001 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8886)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15012)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15013)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMd_red_sm8886 initSM, l19ZMd_red_pm15012 initPM, l19ZMd_red_pm15013 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11236)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11237)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMd_red_sm6123 initSM, l19ZMd_red_pm11236 initPM, l19ZMd_red_pm11237 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6127)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11248)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11249)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMd_red_sm6127 initSM, l19ZMd_red_pm11248 initPM, l19ZMd_red_pm11249 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l19ZMd_weight_eq initSM initPM hInit initGoal_6124 (by native_decide)
    6124 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l19ZMd_weight_eq initSM initPM hInit initGoal_6128 (by native_decide)
    6128 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l19ZMd_weight_shape initPM hPM 6124 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l19ZMd_weight_shape initPM hPM 6128 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6125)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11240)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11241)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l19ZMd_red_sm6125 initSM, l19ZMd_red_pm11240 initPM,
      l19ZMd_red_pm11241 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6129)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11252)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11253)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l19ZMd_red_sm6129 initSM, l19ZMd_red_pm11252 initPM,
      l19ZMd_red_pm11253 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6126)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11242)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11243)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l19ZMd_red_sm6126 initSM, l19ZMd_red_pm11242 initPM, l19ZMd_red_pm11243 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6130)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11254)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l19ZMd_red_sm6130 initSM, l19ZMd_red_pm11254 initPM, l19ZMd_red_pm11255 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6126)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11242)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11243)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6130)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11254)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6131)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11260)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11261)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l19ZMd_red_sm6131 initSM, l19ZMd_red_pm11260 initPM, l19ZMd_red_pm11261 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6132)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11262)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11263)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l19ZMd_red_sm6132 initSM, l19ZMd_red_pm11262 initPM, l19ZMd_red_pm11263 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l19ZMd_weight_eq initSM initPM hInit initGoal_6133 (by native_decide)
    6133 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l19ZMd_weight_shape initPM hPM 6133 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6134)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11268)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11269)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l19ZMd_red_sm6134 initSM, l19ZMd_red_pm11268 initPM,
      l19ZMd_red_pm11269 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l19ZMd_red_sm6135 initSM, l19ZMd_red_pm11270 initPM, l19ZMd_red_pm11271 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
