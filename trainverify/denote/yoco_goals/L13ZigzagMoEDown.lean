/- Canonical Goal 1, layer 13: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L13ZigzagMoEResidualGate

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

private def l13ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5784], outs := [8636, 8640, 8644, 8648, 8652], params := [5] }

private def l13ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10280], outs := [15400, 14280, 14290, 14304, 14316], params := [5] }

private def l13ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10281], outs := [15402, 14281, 14291, 14305, 14317], params := [5] }

private def l13ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8648], outs := [5799], params := [4096, 1024] }

private def l13ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8652], outs := [5803], params := [4096, 1024] }

private def l13ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14304], outs := [10312], params := [2048, 1024] }

private def l13ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14305], outs := [10313], params := [2048, 1024] }

private def l13ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14316], outs := [10324], params := [2048, 1024] }

private def l13ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14317], outs := [10325], params := [2048, 1024] }

private def l13ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5799, 5800], outs := [5801] }

private def l13ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5803, 5804], outs := [5805] }

private def l13ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10312, 5800], outs := [10316] }

private def l13ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10313, 5800], outs := [10317] }

private def l13ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10324, 5804], outs := [10328] }

private def l13ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10325, 5804], outs := [10329] }

private def l13ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5801], outs := [5802], params := [4096, 512] }

private def l13ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5805], outs := [5806], params := [4096, 512] }

private def l13ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10316], outs := [10318], params := [2048, 512] }

private def l13ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10317], outs := [10319], params := [2048, 512] }

private def l13ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10328], outs := [10330], params := [2048, 512] }

private def l13ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10329], outs := [10331], params := [2048, 512] }

private def l13ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5802, 5806], outs := [5807] }

private def l13ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10318, 10330], outs := [10336] }

private def l13ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10319, 10331], outs := [10337] }

private def l13ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5807], outs := [5808], params := [4096, 512] }

private def l13ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10336], outs := [10338], params := [2048, 512] }

private def l13ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10337], outs := [10339], params := [2048, 512] }

private def l13ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5808, 5809], outs := [5810] }

private def l13ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10338, 5809], outs := [10344] }

private def l13ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10339, 5809], outs := [10345] }

private def l13ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5810], outs := [5811], params := [4096, 1024] }

private def l13ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10344], outs := [10346], params := [2048, 1024] }

private def l13ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10345], outs := [10347], params := [2048, 1024] }

private theorem l13ZMd_red_sm8648 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8648 =
      denoteGraphDistributedFaithful sm_goal_1 init 5784 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 619 l13ZMdSmRef
    5784 8648 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5784 [8948, 8952, 8956, 8648, 8652] 5 rfl 8648 (by decide)

private theorem l13ZMd_red_sm8652 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8652 =
      denoteGraphDistributedFaithful sm_goal_1 init 5784 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 619 l13ZMdSmRef
    5784 8652 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5784 [8948, 8952, 8956, 8648, 8652] 5 rfl 8652 (by decide)

private theorem l13ZMd_red_pm14304 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14304 =
      denoteGraphDistributedFaithful pm_goal_1 init 10280 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1359 l13ZMdPmRef0
    10280 14304 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10280 [15400, 14280, 14290, 14304, 14316] 5 rfl 14304 (by decide)

private theorem l13ZMd_red_pm14316 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14316 =
      denoteGraphDistributedFaithful pm_goal_1 init 10280 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1359 l13ZMdPmRef0
    10280 14316 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10280 [15400, 14280, 14290, 14304, 14316] 5 rfl 14316 (by decide)

private theorem l13ZMd_red_pm14305 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14305 =
      denoteGraphDistributedFaithful pm_goal_1 init 10281 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1360 l13ZMdPmRef1
    10281 14305 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10281 [15402, 14281, 14291, 14305, 14317] 5 rfl 14305 (by decide)

private theorem l13ZMd_red_pm14317 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14317 =
      denoteGraphDistributedFaithful pm_goal_1 init 10281 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1360 l13ZMdPmRef1
    10281 14317 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10281 [15402, 14281, 14291, 14305, 14317] 5 rfl 14317 (by decide)

private theorem l13ZMd_red_sm5799 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5799 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8648) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 622 l13ZMdSmReshapeA
    8648 5799 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8648 5799 [4096, 1024]

private theorem l13ZMd_red_sm5803 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5803 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8652) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 623 l13ZMdSmReshapeB
    8652 5803 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8652 5803 [4096, 1024]

private theorem l13ZMd_red_pm10312 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10312 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14304) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1362 l13ZMdPmReshapeA0
    14304 10312 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14304 10312 [2048, 1024]

private theorem l13ZMd_red_pm10313 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10313 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14305) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1366 l13ZMdPmReshapeA1
    14305 10313 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14305 10313 [2048, 1024]

private theorem l13ZMd_red_pm10324 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10324 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14316) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1363 l13ZMdPmReshapeB0
    14316 10324 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14316 10324 [2048, 1024]

private theorem l13ZMd_red_pm10325 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10325 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14317) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1367 l13ZMdPmReshapeB1
    14317 10325 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14317 10325 [2048, 1024]

private theorem l13ZMd_red_sm5802 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5802 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5801) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 630 l13ZMdSmViewA
    5801 5802 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5801 5802

private theorem l13ZMd_red_sm5806 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5806 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5805) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 631 l13ZMdSmViewB
    5805 5806 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5805 5806

private theorem l13ZMd_red_pm10318 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10318 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10316) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1377 l13ZMdPmViewA0
    10316 10318 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10316 10318

private theorem l13ZMd_red_pm10319 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10319 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10317) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1382 l13ZMdPmViewA1
    10317 10319 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10317 10319

private theorem l13ZMd_red_pm10330 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10330 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10328) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1378 l13ZMdPmViewB0
    10328 10330 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10328 10330

private theorem l13ZMd_red_pm10331 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10331 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10329) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1383 l13ZMdPmViewB1
    10329 10331 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10329 10331

private theorem l13ZMd_red_sm5808 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5808 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5807) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 635 l13ZMdSmReshapeDown
    5807 5808 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5807 5808 [4096, 512]

private theorem l13ZMd_red_pm10338 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10338 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10336) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1390 l13ZMdPmReshapeDown0
    10336 10338 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10336 10338 [2048, 512]

private theorem l13ZMd_red_pm10339 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10339 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10337) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1393 l13ZMdPmReshapeDown1
    10337 10339 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10337 10339 [2048, 512]

private theorem l13ZMd_red_sm5811 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5811 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5810) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 637 l13ZMdSmViewDown
    5810 5811 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5810 5811

private theorem l13ZMd_red_pm10346 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10346 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10344) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1398 l13ZMdPmViewDown0
    10344 10346 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10344 10346

private theorem l13ZMd_red_pm10347 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10347 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10345) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1399 l13ZMdPmViewDown1
    10345 10347 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10345 10347

private theorem l13ZMd_red_sm5801 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5801 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5799)
        (denoteGraphDistributedFaithful sm_goal_1 init 5800) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 626 l13ZMdSmLinearA
    5799 5800 5801 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5799 5800 5801

private theorem l13ZMd_red_sm5805 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5805 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5803)
        (denoteGraphDistributedFaithful sm_goal_1 init 5804) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 627 l13ZMdSmLinearB
    5803 5804 5805 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5803 5804 5805

private theorem l13ZMd_red_pm10316 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10316 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10312)
        (denoteGraphDistributedFaithful pm_goal_1 init 5800) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1369 l13ZMdPmLinearA0
    10312 5800 10316 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10312 5800 10316

private theorem l13ZMd_red_pm10317 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10317 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10313)
        (denoteGraphDistributedFaithful pm_goal_1 init 5800) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1374 l13ZMdPmLinearA1
    10313 5800 10317 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10313 5800 10317

private theorem l13ZMd_red_pm10328 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10328 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10324)
        (denoteGraphDistributedFaithful pm_goal_1 init 5804) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1370 l13ZMdPmLinearB0
    10324 5804 10328 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10324 5804 10328

private theorem l13ZMd_red_pm10329 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10329 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10325)
        (denoteGraphDistributedFaithful pm_goal_1 init 5804) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1375 l13ZMdPmLinearB1
    10325 5804 10329 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10325 5804 10329

private theorem l13ZMd_red_sm5807 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5807 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5802)
        (denoteGraphDistributedFaithful sm_goal_1 init 5806) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 634 l13ZMdSmSwi
    5802 5806 5807 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5802 5806 5807

private theorem l13ZMd_red_pm10336 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10336 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10318)
        (denoteGraphDistributedFaithful pm_goal_1 init 10330) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1385 l13ZMdPmSwi0
    10318 10330 10336 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 10318 10330 10336

private theorem l13ZMd_red_pm10337 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10337 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10319)
        (denoteGraphDistributedFaithful pm_goal_1 init 10331) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1389 l13ZMdPmSwi1
    10319 10331 10337 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 10319 10331 10337

private theorem l13ZMd_red_sm5810 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5810 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5808)
        (denoteGraphDistributedFaithful sm_goal_1 init 5809) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 636 l13ZMdSmLinearDown
    5808 5809 5810 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5808 5809 5810

private theorem l13ZMd_red_pm10344 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10344 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10338)
        (denoteGraphDistributedFaithful pm_goal_1 init 5809) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1394 l13ZMdPmLinearDown0
    10338 5809 10344 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10338 5809 10344

private theorem l13ZMd_red_pm10345 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10345 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10339)
        (denoteGraphDistributedFaithful pm_goal_1 init 5809) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1397 l13ZMdPmLinearDown1
    10339 5809 10345 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l13ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10339 5809 10345

private theorem l13ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l13ZMd_weight_eq (initSM initPM : Store)
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
  rw [l13ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l13ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l13ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l13ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L13 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l13_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5784)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10280)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10281)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5811)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10346)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10347)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8648)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14304)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14305)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMd_red_sm8648 initSM, l13ZMd_red_pm14304 initPM, l13ZMd_red_pm14305 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8652)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14316)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14317)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMd_red_sm8652 initSM, l13ZMd_red_pm14316 initPM, l13ZMd_red_pm14317 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5799)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10312)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10313)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMd_red_sm5799 initSM, l13ZMd_red_pm10312 initPM, l13ZMd_red_pm10313 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5803)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10325)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMd_red_sm5803 initSM, l13ZMd_red_pm10324 initPM, l13ZMd_red_pm10325 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l13ZMd_weight_eq initSM initPM hInit initGoal_5800 (by native_decide)
    5800 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l13ZMd_weight_eq initSM initPM hInit initGoal_5804 (by native_decide)
    5804 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l13ZMd_weight_shape initPM hPM 5800 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l13ZMd_weight_shape initPM hPM 5804 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5801)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10316)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10317)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l13ZMd_red_sm5801 initSM, l13ZMd_red_pm10316 initPM,
      l13ZMd_red_pm10317 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5805)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10328)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10329)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l13ZMd_red_sm5805 initSM, l13ZMd_red_pm10328 initPM,
      l13ZMd_red_pm10329 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5802)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10318)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10319)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l13ZMd_red_sm5802 initSM, l13ZMd_red_pm10318 initPM, l13ZMd_red_pm10319 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10330)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10331)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l13ZMd_red_sm5806 initSM, l13ZMd_red_pm10330 initPM, l13ZMd_red_pm10331 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5802)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10318)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10319)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5806)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10330)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10331)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5807)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10336)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10337)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l13ZMd_red_sm5807 initSM, l13ZMd_red_pm10336 initPM, l13ZMd_red_pm10337 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5808)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10338)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10339)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l13ZMd_red_sm5808 initSM, l13ZMd_red_pm10338 initPM, l13ZMd_red_pm10339 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l13ZMd_weight_eq initSM initPM hInit initGoal_5809 (by native_decide)
    5809 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l13ZMd_weight_shape initPM hPM 5809 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5810)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10344)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10345)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l13ZMd_red_sm5810 initSM, l13ZMd_red_pm10344 initPM,
      l13ZMd_red_pm10345 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l13ZMd_red_sm5811 initSM, l13ZMd_red_pm10346 initPM, l13ZMd_red_pm10347 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
