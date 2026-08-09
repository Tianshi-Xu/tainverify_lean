/- Canonical Goal 1, layer 12: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L12Block2ZigzagMoEResidualGate

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

private def l12B2ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5676], outs := [8558, 8562, 8566, 8570, 8574], params := [5] }

private def l12B2ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9972], outs := [15392, 14048, 14058, 14072, 14084], params := [5] }

private def l12B2ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9973], outs := [15394, 14049, 14059, 14073, 14085], params := [5] }

private def l12B2ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8570], outs := [5691], params := [4096, 1024] }

private def l12B2ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8574], outs := [5695], params := [4096, 1024] }

private def l12B2ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14072], outs := [10004], params := [2048, 1024] }

private def l12B2ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14073], outs := [10005], params := [2048, 1024] }

private def l12B2ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14084], outs := [10016], params := [2048, 1024] }

private def l12B2ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14085], outs := [10017], params := [2048, 1024] }

private def l12B2ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5691, 5692], outs := [5693] }

private def l12B2ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5695, 5696], outs := [5697] }

private def l12B2ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10004, 5692], outs := [10008] }

private def l12B2ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10005, 5692], outs := [10009] }

private def l12B2ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10016, 5696], outs := [10020] }

private def l12B2ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10017, 5696], outs := [10021] }

private def l12B2ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5693], outs := [5694], params := [4096, 512] }

private def l12B2ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5697], outs := [5698], params := [4096, 512] }

private def l12B2ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10008], outs := [10010], params := [2048, 512] }

private def l12B2ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10009], outs := [10011], params := [2048, 512] }

private def l12B2ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10020], outs := [10022], params := [2048, 512] }

private def l12B2ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10021], outs := [10023], params := [2048, 512] }

private def l12B2ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5694, 5698], outs := [5699] }

private def l12B2ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10010, 10022], outs := [10028] }

private def l12B2ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10011, 10023], outs := [10029] }

private def l12B2ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5699], outs := [5700], params := [4096, 512] }

private def l12B2ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10028], outs := [10030], params := [2048, 512] }

private def l12B2ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10029], outs := [10031], params := [2048, 512] }

private def l12B2ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5700, 5701], outs := [5702] }

private def l12B2ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10030, 5701], outs := [10036] }

private def l12B2ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10031, 5701], outs := [10037] }

private def l12B2ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5702], outs := [5703], params := [4096, 1024] }

private def l12B2ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10036], outs := [10038], params := [2048, 1024] }

private def l12B2ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10037], outs := [10039], params := [2048, 1024] }

private theorem l12B2ZMd_red_sm8570 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8570 =
      denoteGraphDistributedFaithful sm_goal_1 init 5676 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 549 l12B2ZMdSmRef
    5676 8570 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5676 [8948, 8952, 8956, 8570, 8574] 5 rfl 8570 (by decide)

private theorem l12B2ZMd_red_sm8574 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8574 =
      denoteGraphDistributedFaithful sm_goal_1 init 5676 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 549 l12B2ZMdSmRef
    5676 8574 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5676 [8948, 8952, 8956, 8570, 8574] 5 rfl 8574 (by decide)

private theorem l12B2ZMd_red_pm14072 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14072 =
      denoteGraphDistributedFaithful pm_goal_1 init 9972 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1207 l12B2ZMdPmRef0
    9972 14072 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9972 [15392, 14048, 14058, 14072, 14084] 5 rfl 14072 (by decide)

private theorem l12B2ZMd_red_pm14084 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14084 =
      denoteGraphDistributedFaithful pm_goal_1 init 9972 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1207 l12B2ZMdPmRef0
    9972 14084 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9972 [15392, 14048, 14058, 14072, 14084] 5 rfl 14084 (by decide)

private theorem l12B2ZMd_red_pm14073 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14073 =
      denoteGraphDistributedFaithful pm_goal_1 init 9973 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1208 l12B2ZMdPmRef1
    9973 14073 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9973 [15394, 14049, 14059, 14073, 14085] 5 rfl 14073 (by decide)

private theorem l12B2ZMd_red_pm14085 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14085 =
      denoteGraphDistributedFaithful pm_goal_1 init 9973 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1208 l12B2ZMdPmRef1
    9973 14085 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9973 [15394, 14049, 14059, 14073, 14085] 5 rfl 14085 (by decide)

private theorem l12B2ZMd_red_sm5691 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5691 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8570) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 552 l12B2ZMdSmReshapeA
    8570 5691 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8570 5691 [4096, 1024]

private theorem l12B2ZMd_red_sm5695 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5695 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8574) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 553 l12B2ZMdSmReshapeB
    8574 5695 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8574 5695 [4096, 1024]

private theorem l12B2ZMd_red_pm10004 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10004 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14072) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1210 l12B2ZMdPmReshapeA0
    14072 10004 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14072 10004 [2048, 1024]

private theorem l12B2ZMd_red_pm10005 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10005 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14073) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1214 l12B2ZMdPmReshapeA1
    14073 10005 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14073 10005 [2048, 1024]

private theorem l12B2ZMd_red_pm10016 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10016 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14084) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1211 l12B2ZMdPmReshapeB0
    14084 10016 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14084 10016 [2048, 1024]

private theorem l12B2ZMd_red_pm10017 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10017 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14085) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1215 l12B2ZMdPmReshapeB1
    14085 10017 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14085 10017 [2048, 1024]

private theorem l12B2ZMd_red_sm5694 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5694 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5693) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 560 l12B2ZMdSmViewA
    5693 5694 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5693 5694

private theorem l12B2ZMd_red_sm5698 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5698 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5697) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 561 l12B2ZMdSmViewB
    5697 5698 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5697 5698

private theorem l12B2ZMd_red_pm10010 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10010 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10008) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1225 l12B2ZMdPmViewA0
    10008 10010 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10008 10010

private theorem l12B2ZMd_red_pm10011 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10011 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10009) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1230 l12B2ZMdPmViewA1
    10009 10011 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10009 10011

private theorem l12B2ZMd_red_pm10022 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10022 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10020) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1226 l12B2ZMdPmViewB0
    10020 10022 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10020 10022

private theorem l12B2ZMd_red_pm10023 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10023 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10021) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1231 l12B2ZMdPmViewB1
    10021 10023 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10021 10023

private theorem l12B2ZMd_red_sm5700 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5700 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5699) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 565 l12B2ZMdSmReshapeDown
    5699 5700 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5699 5700 [4096, 512]

private theorem l12B2ZMd_red_pm10030 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10030 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10028) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1238 l12B2ZMdPmReshapeDown0
    10028 10030 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10028 10030 [2048, 512]

private theorem l12B2ZMd_red_pm10031 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10031 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10029) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1241 l12B2ZMdPmReshapeDown1
    10029 10031 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10029 10031 [2048, 512]

private theorem l12B2ZMd_red_sm5703 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5703 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5702) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 567 l12B2ZMdSmViewDown
    5702 5703 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5702 5703

private theorem l12B2ZMd_red_pm10038 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10038 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10036) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1246 l12B2ZMdPmViewDown0
    10036 10038 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10036 10038

private theorem l12B2ZMd_red_pm10039 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10039 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10037) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1247 l12B2ZMdPmViewDown1
    10037 10039 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10037 10039

private theorem l12B2ZMd_red_sm5693 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5693 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5691)
        (denoteGraphDistributedFaithful sm_goal_1 init 5692) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 556 l12B2ZMdSmLinearA
    5691 5692 5693 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5691 5692 5693

private theorem l12B2ZMd_red_sm5697 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5697 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5695)
        (denoteGraphDistributedFaithful sm_goal_1 init 5696) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 557 l12B2ZMdSmLinearB
    5695 5696 5697 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5695 5696 5697

private theorem l12B2ZMd_red_pm10008 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10008 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10004)
        (denoteGraphDistributedFaithful pm_goal_1 init 5692) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1217 l12B2ZMdPmLinearA0
    10004 5692 10008 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10004 5692 10008

private theorem l12B2ZMd_red_pm10009 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10009 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10005)
        (denoteGraphDistributedFaithful pm_goal_1 init 5692) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1222 l12B2ZMdPmLinearA1
    10005 5692 10009 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10005 5692 10009

private theorem l12B2ZMd_red_pm10020 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10020 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10016)
        (denoteGraphDistributedFaithful pm_goal_1 init 5696) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1218 l12B2ZMdPmLinearB0
    10016 5696 10020 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10016 5696 10020

private theorem l12B2ZMd_red_pm10021 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10021 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10017)
        (denoteGraphDistributedFaithful pm_goal_1 init 5696) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1223 l12B2ZMdPmLinearB1
    10017 5696 10021 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10017 5696 10021

private theorem l12B2ZMd_red_sm5699 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5699 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5694)
        (denoteGraphDistributedFaithful sm_goal_1 init 5698) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 564 l12B2ZMdSmSwi
    5694 5698 5699 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5694 5698 5699

private theorem l12B2ZMd_red_pm10028 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10028 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10010)
        (denoteGraphDistributedFaithful pm_goal_1 init 10022) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1233 l12B2ZMdPmSwi0
    10010 10022 10028 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 10010 10022 10028

private theorem l12B2ZMd_red_pm10029 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10029 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10011)
        (denoteGraphDistributedFaithful pm_goal_1 init 10023) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1237 l12B2ZMdPmSwi1
    10011 10023 10029 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 10011 10023 10029

private theorem l12B2ZMd_red_sm5702 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5702 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5700)
        (denoteGraphDistributedFaithful sm_goal_1 init 5701) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 566 l12B2ZMdSmLinearDown
    5700 5701 5702 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5700 5701 5702

private theorem l12B2ZMd_red_pm10036 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10036 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10030)
        (denoteGraphDistributedFaithful pm_goal_1 init 5701) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1242 l12B2ZMdPmLinearDown0
    10030 5701 10036 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10030 5701 10036

private theorem l12B2ZMd_red_pm10037 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10037 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10031)
        (denoteGraphDistributedFaithful pm_goal_1 init 5701) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1245 l12B2ZMdPmLinearDown1
    10031 5701 10037 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10031 5701 10037

private theorem l12B2ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l12B2ZMd_weight_eq (initSM initPM : Store)
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
  rw [l12B2ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l12B2ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l12B2ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l12B2ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L21 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l12b2_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5703)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10038)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10039)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8570)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14072)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14073)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMd_red_sm8570 initSM, l12B2ZMd_red_pm14072 initPM, l12B2ZMd_red_pm14073 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8574)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14084)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14085)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMd_red_sm8574 initSM, l12B2ZMd_red_pm14084 initPM, l12B2ZMd_red_pm14085 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5691)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10004)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10005)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMd_red_sm5691 initSM, l12B2ZMd_red_pm10004 initPM, l12B2ZMd_red_pm10005 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5695)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10017)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMd_red_sm5695 initSM, l12B2ZMd_red_pm10016 initPM, l12B2ZMd_red_pm10017 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l12B2ZMd_weight_eq initSM initPM hInit initGoal_5692 (by native_decide)
    5692 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l12B2ZMd_weight_eq initSM initPM hInit initGoal_5696 (by native_decide)
    5696 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l12B2ZMd_weight_shape initPM hPM 5692 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l12B2ZMd_weight_shape initPM hPM 5696 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5693)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10008)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10009)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12B2ZMd_red_sm5693 initSM, l12B2ZMd_red_pm10008 initPM,
      l12B2ZMd_red_pm10009 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5697)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10020)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10021)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12B2ZMd_red_sm5697 initSM, l12B2ZMd_red_pm10020 initPM,
      l12B2ZMd_red_pm10021 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5694)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10010)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10011)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12B2ZMd_red_sm5694 initSM, l12B2ZMd_red_pm10010 initPM, l12B2ZMd_red_pm10011 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5698)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10022)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10023)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12B2ZMd_red_sm5698 initSM, l12B2ZMd_red_pm10022 initPM, l12B2ZMd_red_pm10023 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5694)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10010)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10011)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5698)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10022)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10023)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5699)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10028)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10029)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12B2ZMd_red_sm5699 initSM, l12B2ZMd_red_pm10028 initPM, l12B2ZMd_red_pm10029 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5700)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10030)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12B2ZMd_red_sm5700 initSM, l12B2ZMd_red_pm10030 initPM, l12B2ZMd_red_pm10031 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l12B2ZMd_weight_eq initSM initPM hInit initGoal_5701 (by native_decide)
    5701 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l12B2ZMd_weight_shape initPM hPM 5701 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10036)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10037)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12B2ZMd_red_sm5702 initSM, l12B2ZMd_red_pm10036 initPM,
      l12B2ZMd_red_pm10037 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l12B2ZMd_red_sm5703 initSM, l12B2ZMd_red_pm10038 initPM, l12B2ZMd_red_pm10039 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
