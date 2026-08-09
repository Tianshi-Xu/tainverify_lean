/- Canonical Goal 1, layer 15: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L15ZigzagMoEResidualGate

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

private def l15ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5892], outs := [8714, 8718, 8722, 8726, 8730], params := [5] }

private def l15ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10588], outs := [15408, 14512, 14522, 14536, 14548], params := [5] }

private def l15ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10589], outs := [15410, 14513, 14523, 14537, 14549], params := [5] }

private def l15ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8726], outs := [5907], params := [4096, 1024] }

private def l15ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8730], outs := [5911], params := [4096, 1024] }

private def l15ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14536], outs := [10620], params := [2048, 1024] }

private def l15ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14537], outs := [10621], params := [2048, 1024] }

private def l15ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14548], outs := [10632], params := [2048, 1024] }

private def l15ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14549], outs := [10633], params := [2048, 1024] }

private def l15ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5907, 5908], outs := [5909] }

private def l15ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5911, 5912], outs := [5913] }

private def l15ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10620, 5908], outs := [10624] }

private def l15ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10621, 5908], outs := [10625] }

private def l15ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10632, 5912], outs := [10636] }

private def l15ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10633, 5912], outs := [10637] }

private def l15ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5909], outs := [5910], params := [4096, 512] }

private def l15ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5913], outs := [5914], params := [4096, 512] }

private def l15ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10624], outs := [10626], params := [2048, 512] }

private def l15ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10625], outs := [10627], params := [2048, 512] }

private def l15ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10636], outs := [10638], params := [2048, 512] }

private def l15ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10637], outs := [10639], params := [2048, 512] }

private def l15ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5910, 5914], outs := [5915] }

private def l15ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10626, 10638], outs := [10644] }

private def l15ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10627, 10639], outs := [10645] }

private def l15ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5915], outs := [5916], params := [4096, 512] }

private def l15ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10644], outs := [10646], params := [2048, 512] }

private def l15ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10645], outs := [10647], params := [2048, 512] }

private def l15ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5916, 5917], outs := [5918] }

private def l15ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10646, 5917], outs := [10652] }

private def l15ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10647, 5917], outs := [10653] }

private def l15ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5918], outs := [5919], params := [4096, 1024] }

private def l15ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10652], outs := [10654], params := [2048, 1024] }

private def l15ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10653], outs := [10655], params := [2048, 1024] }

private theorem l15ZMd_red_sm8726 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8726 =
      denoteGraphDistributedFaithful sm_goal_1 init 5892 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 689 l15ZMdSmRef
    5892 8726 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5892 [8948, 8952, 8956, 8726, 8730] 5 rfl 8726 (by decide)

private theorem l15ZMd_red_sm8730 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8730 =
      denoteGraphDistributedFaithful sm_goal_1 init 5892 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 689 l15ZMdSmRef
    5892 8730 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5892 [8948, 8952, 8956, 8726, 8730] 5 rfl 8730 (by decide)

private theorem l15ZMd_red_pm14536 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14536 =
      denoteGraphDistributedFaithful pm_goal_1 init 10588 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1511 l15ZMdPmRef0
    10588 14536 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10588 [15408, 14512, 14522, 14536, 14548] 5 rfl 14536 (by decide)

private theorem l15ZMd_red_pm14548 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14548 =
      denoteGraphDistributedFaithful pm_goal_1 init 10588 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1511 l15ZMdPmRef0
    10588 14548 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10588 [15408, 14512, 14522, 14536, 14548] 5 rfl 14548 (by decide)

private theorem l15ZMd_red_pm14537 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14537 =
      denoteGraphDistributedFaithful pm_goal_1 init 10589 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1512 l15ZMdPmRef1
    10589 14537 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10589 [15410, 14513, 14523, 14537, 14549] 5 rfl 14537 (by decide)

private theorem l15ZMd_red_pm14549 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14549 =
      denoteGraphDistributedFaithful pm_goal_1 init 10589 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1512 l15ZMdPmRef1
    10589 14549 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10589 [15410, 14513, 14523, 14537, 14549] 5 rfl 14549 (by decide)

private theorem l15ZMd_red_sm5907 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5907 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8726) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 692 l15ZMdSmReshapeA
    8726 5907 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8726 5907 [4096, 1024]

private theorem l15ZMd_red_sm5911 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5911 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8730) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 693 l15ZMdSmReshapeB
    8730 5911 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8730 5911 [4096, 1024]

private theorem l15ZMd_red_pm10620 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10620 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14536) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1514 l15ZMdPmReshapeA0
    14536 10620 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14536 10620 [2048, 1024]

private theorem l15ZMd_red_pm10621 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10621 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14537) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1518 l15ZMdPmReshapeA1
    14537 10621 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14537 10621 [2048, 1024]

private theorem l15ZMd_red_pm10632 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10632 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14548) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1515 l15ZMdPmReshapeB0
    14548 10632 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14548 10632 [2048, 1024]

private theorem l15ZMd_red_pm10633 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10633 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14549) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1519 l15ZMdPmReshapeB1
    14549 10633 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14549 10633 [2048, 1024]

private theorem l15ZMd_red_sm5910 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5910 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5909) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 700 l15ZMdSmViewA
    5909 5910 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5909 5910

private theorem l15ZMd_red_sm5914 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5914 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5913) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 701 l15ZMdSmViewB
    5913 5914 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5913 5914

private theorem l15ZMd_red_pm10626 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10626 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10624) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1529 l15ZMdPmViewA0
    10624 10626 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10624 10626

private theorem l15ZMd_red_pm10627 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10627 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10625) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1534 l15ZMdPmViewA1
    10625 10627 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10625 10627

private theorem l15ZMd_red_pm10638 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10638 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10636) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1530 l15ZMdPmViewB0
    10636 10638 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10636 10638

private theorem l15ZMd_red_pm10639 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10639 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10637) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1535 l15ZMdPmViewB1
    10637 10639 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10637 10639

private theorem l15ZMd_red_sm5916 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5916 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5915) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 705 l15ZMdSmReshapeDown
    5915 5916 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5915 5916 [4096, 512]

private theorem l15ZMd_red_pm10646 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10646 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10644) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1542 l15ZMdPmReshapeDown0
    10644 10646 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10644 10646 [2048, 512]

private theorem l15ZMd_red_pm10647 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10647 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10645) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1545 l15ZMdPmReshapeDown1
    10645 10647 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10645 10647 [2048, 512]

private theorem l15ZMd_red_sm5919 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5919 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5918) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 707 l15ZMdSmViewDown
    5918 5919 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5918 5919

private theorem l15ZMd_red_pm10654 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10654 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10652) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1550 l15ZMdPmViewDown0
    10652 10654 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10652 10654

private theorem l15ZMd_red_pm10655 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10655 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10653) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1551 l15ZMdPmViewDown1
    10653 10655 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10653 10655

private theorem l15ZMd_red_sm5909 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5909 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5907)
        (denoteGraphDistributedFaithful sm_goal_1 init 5908) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 696 l15ZMdSmLinearA
    5907 5908 5909 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5907 5908 5909

private theorem l15ZMd_red_sm5913 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5913 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5911)
        (denoteGraphDistributedFaithful sm_goal_1 init 5912) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 697 l15ZMdSmLinearB
    5911 5912 5913 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5911 5912 5913

private theorem l15ZMd_red_pm10624 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10624 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10620)
        (denoteGraphDistributedFaithful pm_goal_1 init 5908) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1521 l15ZMdPmLinearA0
    10620 5908 10624 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10620 5908 10624

private theorem l15ZMd_red_pm10625 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10625 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10621)
        (denoteGraphDistributedFaithful pm_goal_1 init 5908) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1526 l15ZMdPmLinearA1
    10621 5908 10625 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10621 5908 10625

private theorem l15ZMd_red_pm10636 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10636 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10632)
        (denoteGraphDistributedFaithful pm_goal_1 init 5912) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1522 l15ZMdPmLinearB0
    10632 5912 10636 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10632 5912 10636

private theorem l15ZMd_red_pm10637 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10637 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10633)
        (denoteGraphDistributedFaithful pm_goal_1 init 5912) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1527 l15ZMdPmLinearB1
    10633 5912 10637 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10633 5912 10637

private theorem l15ZMd_red_sm5915 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5915 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5910)
        (denoteGraphDistributedFaithful sm_goal_1 init 5914) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 704 l15ZMdSmSwi
    5910 5914 5915 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5910 5914 5915

private theorem l15ZMd_red_pm10644 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10644 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10626)
        (denoteGraphDistributedFaithful pm_goal_1 init 10638) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1537 l15ZMdPmSwi0
    10626 10638 10644 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 10626 10638 10644

private theorem l15ZMd_red_pm10645 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10645 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10627)
        (denoteGraphDistributedFaithful pm_goal_1 init 10639) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1541 l15ZMdPmSwi1
    10627 10639 10645 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 10627 10639 10645

private theorem l15ZMd_red_sm5918 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5918 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5916)
        (denoteGraphDistributedFaithful sm_goal_1 init 5917) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 706 l15ZMdSmLinearDown
    5916 5917 5918 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5916 5917 5918

private theorem l15ZMd_red_pm10652 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10652 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10646)
        (denoteGraphDistributedFaithful pm_goal_1 init 5917) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1546 l15ZMdPmLinearDown0
    10646 5917 10652 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10646 5917 10652

private theorem l15ZMd_red_pm10653 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10653 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10647)
        (denoteGraphDistributedFaithful pm_goal_1 init 5917) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1549 l15ZMdPmLinearDown1
    10647 5917 10653 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l15ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10647 5917 10653

private theorem l15ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l15ZMd_weight_eq (initSM initPM : Store)
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
  rw [l15ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l15ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l15ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l15ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L15 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l15_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5919)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10654)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10655)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8726)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14536)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14537)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMd_red_sm8726 initSM, l15ZMd_red_pm14536 initPM, l15ZMd_red_pm14537 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8730)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14548)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14549)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMd_red_sm8730 initSM, l15ZMd_red_pm14548 initPM, l15ZMd_red_pm14549 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5907)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10621)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMd_red_sm5907 initSM, l15ZMd_red_pm10620 initPM, l15ZMd_red_pm10621 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5911)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10632)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10633)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMd_red_sm5911 initSM, l15ZMd_red_pm10632 initPM, l15ZMd_red_pm10633 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l15ZMd_weight_eq initSM initPM hInit initGoal_5908 (by native_decide)
    5908 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l15ZMd_weight_eq initSM initPM hInit initGoal_5912 (by native_decide)
    5912 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l15ZMd_weight_shape initPM hPM 5908 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l15ZMd_weight_shape initPM hPM 5912 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5909)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10624)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10625)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l15ZMd_red_sm5909 initSM, l15ZMd_red_pm10624 initPM,
      l15ZMd_red_pm10625 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5913)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10636)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10637)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l15ZMd_red_sm5913 initSM, l15ZMd_red_pm10636 initPM,
      l15ZMd_red_pm10637 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5910)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10626)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10627)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l15ZMd_red_sm5910 initSM, l15ZMd_red_pm10626 initPM, l15ZMd_red_pm10627 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5914)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10638)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10639)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l15ZMd_red_sm5914 initSM, l15ZMd_red_pm10638 initPM, l15ZMd_red_pm10639 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5910)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10626)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10627)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5914)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10638)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10639)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5915)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10644)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10645)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l15ZMd_red_sm5915 initSM, l15ZMd_red_pm10644 initPM, l15ZMd_red_pm10645 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5916)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10646)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10647)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l15ZMd_red_sm5916 initSM, l15ZMd_red_pm10646 initPM, l15ZMd_red_pm10647 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l15ZMd_weight_eq initSM initPM hInit initGoal_5917 (by native_decide)
    5917 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l15ZMd_weight_shape initPM hPM 5917 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5918)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l15ZMd_red_sm5918 initSM, l15ZMd_red_pm10652 initPM,
      l15ZMd_red_pm10653 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l15ZMd_red_sm5919 initSM, l15ZMd_red_pm10654 initPM, l15ZMd_red_pm10655 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
