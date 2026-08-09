/- Canonical Goal 1, layer 18: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L18ZigzagMoEResidualGate

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

private def l18ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6054], outs := [8831, 8835, 8839, 8843, 8847], params := [5] }

private def l18ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11050], outs := [15420, 14860, 14870, 14884, 14896], params := [5] }

private def l18ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11051], outs := [15422, 14861, 14871, 14885, 14897], params := [5] }

private def l18ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8843], outs := [6069], params := [4096, 1024] }

private def l18ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8847], outs := [6073], params := [4096, 1024] }

private def l18ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14884], outs := [11082], params := [2048, 1024] }

private def l18ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14885], outs := [11083], params := [2048, 1024] }

private def l18ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14896], outs := [11094], params := [2048, 1024] }

private def l18ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14897], outs := [11095], params := [2048, 1024] }

private def l18ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6069, 6070], outs := [6071] }

private def l18ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6073, 6074], outs := [6075] }

private def l18ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11082, 6070], outs := [11086] }

private def l18ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11083, 6070], outs := [11087] }

private def l18ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11094, 6074], outs := [11098] }

private def l18ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11095, 6074], outs := [11099] }

private def l18ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6071], outs := [6072], params := [4096, 512] }

private def l18ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6075], outs := [6076], params := [4096, 512] }

private def l18ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11086], outs := [11088], params := [2048, 512] }

private def l18ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11087], outs := [11089], params := [2048, 512] }

private def l18ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11098], outs := [11100], params := [2048, 512] }

private def l18ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11099], outs := [11101], params := [2048, 512] }

private def l18ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [6072, 6076], outs := [6077] }

private def l18ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11088, 11100], outs := [11106] }

private def l18ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11089, 11101], outs := [11107] }

private def l18ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6077], outs := [6078], params := [4096, 512] }

private def l18ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11106], outs := [11108], params := [2048, 512] }

private def l18ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11107], outs := [11109], params := [2048, 512] }

private def l18ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6078, 6079], outs := [6080] }

private def l18ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11108, 6079], outs := [11114] }

private def l18ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11109, 6079], outs := [11115] }

private def l18ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6080], outs := [6081], params := [4096, 1024] }

private def l18ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11114], outs := [11116], params := [2048, 1024] }

private def l18ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11115], outs := [11117], params := [2048, 1024] }

private theorem l18ZMd_red_sm8843 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8843 =
      denoteGraphDistributedFaithful sm_goal_1 init 6054 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 794 l18ZMdSmRef
    6054 8843 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6054 [8948, 8952, 8956, 8843, 8847] 5 rfl 8843 (by decide)

private theorem l18ZMd_red_sm8847 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8847 =
      denoteGraphDistributedFaithful sm_goal_1 init 6054 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 794 l18ZMdSmRef
    6054 8847 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6054 [8948, 8952, 8956, 8843, 8847] 5 rfl 8847 (by decide)

private theorem l18ZMd_red_pm14884 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14884 =
      denoteGraphDistributedFaithful pm_goal_1 init 11050 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1739 l18ZMdPmRef0
    11050 14884 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11050 [15420, 14860, 14870, 14884, 14896] 5 rfl 14884 (by decide)

private theorem l18ZMd_red_pm14896 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14896 =
      denoteGraphDistributedFaithful pm_goal_1 init 11050 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1739 l18ZMdPmRef0
    11050 14896 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11050 [15420, 14860, 14870, 14884, 14896] 5 rfl 14896 (by decide)

private theorem l18ZMd_red_pm14885 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14885 =
      denoteGraphDistributedFaithful pm_goal_1 init 11051 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1740 l18ZMdPmRef1
    11051 14885 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11051 [15422, 14861, 14871, 14885, 14897] 5 rfl 14885 (by decide)

private theorem l18ZMd_red_pm14897 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14897 =
      denoteGraphDistributedFaithful pm_goal_1 init 11051 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1740 l18ZMdPmRef1
    11051 14897 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11051 [15422, 14861, 14871, 14885, 14897] 5 rfl 14897 (by decide)

private theorem l18ZMd_red_sm6069 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6069 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8843) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 797 l18ZMdSmReshapeA
    8843 6069 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8843 6069 [4096, 1024]

private theorem l18ZMd_red_sm6073 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6073 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8847) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 798 l18ZMdSmReshapeB
    8847 6073 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8847 6073 [4096, 1024]

private theorem l18ZMd_red_pm11082 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11082 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14884) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1742 l18ZMdPmReshapeA0
    14884 11082 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14884 11082 [2048, 1024]

private theorem l18ZMd_red_pm11083 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11083 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14885) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1746 l18ZMdPmReshapeA1
    14885 11083 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14885 11083 [2048, 1024]

private theorem l18ZMd_red_pm11094 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11094 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14896) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1743 l18ZMdPmReshapeB0
    14896 11094 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14896 11094 [2048, 1024]

private theorem l18ZMd_red_pm11095 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11095 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14897) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1747 l18ZMdPmReshapeB1
    14897 11095 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14897 11095 [2048, 1024]

private theorem l18ZMd_red_sm6072 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6072 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6071) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 805 l18ZMdSmViewA
    6071 6072 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6071 6072

private theorem l18ZMd_red_sm6076 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6076 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6075) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 806 l18ZMdSmViewB
    6075 6076 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6075 6076

private theorem l18ZMd_red_pm11088 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11088 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11086) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1757 l18ZMdPmViewA0
    11086 11088 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11086 11088

private theorem l18ZMd_red_pm11089 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11089 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11087) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1762 l18ZMdPmViewA1
    11087 11089 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11087 11089

private theorem l18ZMd_red_pm11100 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11100 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11098) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1758 l18ZMdPmViewB0
    11098 11100 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11098 11100

private theorem l18ZMd_red_pm11101 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11101 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11099) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1763 l18ZMdPmViewB1
    11099 11101 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11099 11101

private theorem l18ZMd_red_sm6078 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6078 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6077) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 810 l18ZMdSmReshapeDown
    6077 6078 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6077 6078 [4096, 512]

private theorem l18ZMd_red_pm11108 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11108 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11106) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1770 l18ZMdPmReshapeDown0
    11106 11108 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11106 11108 [2048, 512]

private theorem l18ZMd_red_pm11109 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11109 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11107) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1773 l18ZMdPmReshapeDown1
    11107 11109 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11107 11109 [2048, 512]

private theorem l18ZMd_red_sm6081 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6081 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 6080) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 812 l18ZMdSmViewDown
    6080 6081 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6080 6081

private theorem l18ZMd_red_pm11116 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11116 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11114) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1778 l18ZMdPmViewDown0
    11114 11116 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11114 11116

private theorem l18ZMd_red_pm11117 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11117 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11115) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1779 l18ZMdPmViewDown1
    11115 11117 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11115 11117

private theorem l18ZMd_red_sm6071 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6071 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6069)
        (denoteGraphDistributedFaithful sm_goal_1 init 6070) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 801 l18ZMdSmLinearA
    6069 6070 6071 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6069 6070 6071

private theorem l18ZMd_red_sm6075 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6075 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6073)
        (denoteGraphDistributedFaithful sm_goal_1 init 6074) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 802 l18ZMdSmLinearB
    6073 6074 6075 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6073 6074 6075

private theorem l18ZMd_red_pm11086 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11086 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11082)
        (denoteGraphDistributedFaithful pm_goal_1 init 6070) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1749 l18ZMdPmLinearA0
    11082 6070 11086 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11082 6070 11086

private theorem l18ZMd_red_pm11087 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11087 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11083)
        (denoteGraphDistributedFaithful pm_goal_1 init 6070) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1754 l18ZMdPmLinearA1
    11083 6070 11087 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11083 6070 11087

private theorem l18ZMd_red_pm11098 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11098 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11094)
        (denoteGraphDistributedFaithful pm_goal_1 init 6074) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1750 l18ZMdPmLinearB0
    11094 6074 11098 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11094 6074 11098

private theorem l18ZMd_red_pm11099 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11099 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11095)
        (denoteGraphDistributedFaithful pm_goal_1 init 6074) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1755 l18ZMdPmLinearB1
    11095 6074 11099 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11095 6074 11099

private theorem l18ZMd_red_sm6077 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6077 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 6072)
        (denoteGraphDistributedFaithful sm_goal_1 init 6076) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 809 l18ZMdSmSwi
    6072 6076 6077 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 6072 6076 6077

private theorem l18ZMd_red_pm11106 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11106 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11088)
        (denoteGraphDistributedFaithful pm_goal_1 init 11100) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1765 l18ZMdPmSwi0
    11088 11100 11106 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 11088 11100 11106

private theorem l18ZMd_red_pm11107 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11107 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11089)
        (denoteGraphDistributedFaithful pm_goal_1 init 11101) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1769 l18ZMdPmSwi1
    11089 11101 11107 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 11089 11101 11107

private theorem l18ZMd_red_sm6080 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6080 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6078)
        (denoteGraphDistributedFaithful sm_goal_1 init 6079) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 811 l18ZMdSmLinearDown
    6078 6079 6080 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6078 6079 6080

private theorem l18ZMd_red_pm11114 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11114 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11108)
        (denoteGraphDistributedFaithful pm_goal_1 init 6079) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1774 l18ZMdPmLinearDown0
    11108 6079 11114 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11108 6079 11114

private theorem l18ZMd_red_pm11115 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11115 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11109)
        (denoteGraphDistributedFaithful pm_goal_1 init 6079) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1777 l18ZMdPmLinearDown1
    11109 6079 11115 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11109 6079 11115

private theorem l18ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l18ZMd_weight_eq (initSM initPM : Store)
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
  rw [l18ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l18ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l18ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l18ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L18 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l18_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6081)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11116)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11117)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8843)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14884)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14885)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMd_red_sm8843 initSM, l18ZMd_red_pm14884 initPM, l18ZMd_red_pm14885 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8847)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMd_red_sm8847 initSM, l18ZMd_red_pm14896 initPM, l18ZMd_red_pm14897 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6069)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11082)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11083)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMd_red_sm6069 initSM, l18ZMd_red_pm11082 initPM, l18ZMd_red_pm11083 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6073)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11094)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11095)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMd_red_sm6073 initSM, l18ZMd_red_pm11094 initPM, l18ZMd_red_pm11095 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l18ZMd_weight_eq initSM initPM hInit initGoal_6070 (by native_decide)
    6070 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l18ZMd_weight_eq initSM initPM hInit initGoal_6074 (by native_decide)
    6074 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l18ZMd_weight_shape initPM hPM 6070 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l18ZMd_weight_shape initPM hPM 6074 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6071)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11086)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11087)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l18ZMd_red_sm6071 initSM, l18ZMd_red_pm11086 initPM,
      l18ZMd_red_pm11087 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6075)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11098)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11099)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l18ZMd_red_sm6075 initSM, l18ZMd_red_pm11098 initPM,
      l18ZMd_red_pm11099 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6072)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11088)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11089)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l18ZMd_red_sm6072 initSM, l18ZMd_red_pm11088 initPM, l18ZMd_red_pm11089 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6076)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11101)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l18ZMd_red_sm6076 initSM, l18ZMd_red_pm11100 initPM, l18ZMd_red_pm11101 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6072)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11088)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11089)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6076)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11101)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6077)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11106)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11107)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l18ZMd_red_sm6077 initSM, l18ZMd_red_pm11106 initPM, l18ZMd_red_pm11107 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6078)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11108)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11109)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l18ZMd_red_sm6078 initSM, l18ZMd_red_pm11108 initPM, l18ZMd_red_pm11109 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l18ZMd_weight_eq initSM initPM hInit initGoal_6079 (by native_decide)
    6079 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l18ZMd_weight_shape initPM hPM 6079 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6080)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11114)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11115)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l18ZMd_red_sm6080 initSM, l18ZMd_red_pm11114 initPM,
      l18ZMd_red_pm11115 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l18ZMd_red_sm6081 initSM, l18ZMd_red_pm11116 initPM, l18ZMd_red_pm11117 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
