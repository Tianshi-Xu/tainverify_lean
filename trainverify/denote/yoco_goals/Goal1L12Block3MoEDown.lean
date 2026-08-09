/- Canonical Goal 1, layer 12: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.Goal1L12Block3MoEResidualGate

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

private def l12ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5730], outs := [8597, 8601, 8605, 8609, 8613], params := [5] }

private def l12ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10126], outs := [15396, 14164, 14174, 14188, 14200], params := [5] }

private def l12ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10127], outs := [15398, 14165, 14175, 14189, 14201], params := [5] }

private def l12ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8609], outs := [5745], params := [4096, 1024] }

private def l12ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8613], outs := [5749], params := [4096, 1024] }

private def l12ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14188], outs := [10158], params := [2048, 1024] }

private def l12ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14189], outs := [10159], params := [2048, 1024] }

private def l12ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14200], outs := [10170], params := [2048, 1024] }

private def l12ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14201], outs := [10171], params := [2048, 1024] }

private def l12ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5745, 5746], outs := [5747] }

private def l12ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5749, 5750], outs := [5751] }

private def l12ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10158, 5746], outs := [10162] }

private def l12ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10159, 5746], outs := [10163] }

private def l12ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10170, 5750], outs := [10174] }

private def l12ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10171, 5750], outs := [10175] }

private def l12ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5747], outs := [5748], params := [4096, 512] }

private def l12ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5751], outs := [5752], params := [4096, 512] }

private def l12ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10162], outs := [10164], params := [2048, 512] }

private def l12ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10163], outs := [10165], params := [2048, 512] }

private def l12ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10174], outs := [10176], params := [2048, 512] }

private def l12ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10175], outs := [10177], params := [2048, 512] }

private def l12ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5748, 5752], outs := [5753] }

private def l12ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10164, 10176], outs := [10182] }

private def l12ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10165, 10177], outs := [10183] }

private def l12ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5753], outs := [5754], params := [4096, 512] }

private def l12ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10182], outs := [10184], params := [2048, 512] }

private def l12ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10183], outs := [10185], params := [2048, 512] }

private def l12ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5754, 5755], outs := [5756] }

private def l12ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10184, 5755], outs := [10190] }

private def l12ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10185, 5755], outs := [10191] }

private def l12ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5756], outs := [5757], params := [4096, 1024] }

private def l12ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10190], outs := [10192], params := [2048, 1024] }

private def l12ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10191], outs := [10193], params := [2048, 1024] }

private theorem l12ZMd_red_sm8609 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8609 =
      denoteGraphDistributedFaithful sm_goal_1 init 5730 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 584 l12ZMdSmRef
    5730 8609 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5730 [8948, 8952, 8956, 8609, 8613] 5 rfl 8609 (by decide)

private theorem l12ZMd_red_sm8613 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8613 =
      denoteGraphDistributedFaithful sm_goal_1 init 5730 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 584 l12ZMdSmRef
    5730 8613 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5730 [8948, 8952, 8956, 8609, 8613] 5 rfl 8613 (by decide)

private theorem l12ZMd_red_pm14188 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14188 =
      denoteGraphDistributedFaithful pm_goal_1 init 10126 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1283 l12ZMdPmRef0
    10126 14188 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10126 [15396, 14164, 14174, 14188, 14200] 5 rfl 14188 (by decide)

private theorem l12ZMd_red_pm14200 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14200 =
      denoteGraphDistributedFaithful pm_goal_1 init 10126 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1283 l12ZMdPmRef0
    10126 14200 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10126 [15396, 14164, 14174, 14188, 14200] 5 rfl 14200 (by decide)

private theorem l12ZMd_red_pm14189 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14189 =
      denoteGraphDistributedFaithful pm_goal_1 init 10127 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1284 l12ZMdPmRef1
    10127 14189 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10127 [15398, 14165, 14175, 14189, 14201] 5 rfl 14189 (by decide)

private theorem l12ZMd_red_pm14201 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14201 =
      denoteGraphDistributedFaithful pm_goal_1 init 10127 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1284 l12ZMdPmRef1
    10127 14201 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10127 [15398, 14165, 14175, 14189, 14201] 5 rfl 14201 (by decide)

private theorem l12ZMd_red_sm5745 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5745 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8609) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 587 l12ZMdSmReshapeA
    8609 5745 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8609 5745 [4096, 1024]

private theorem l12ZMd_red_sm5749 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5749 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8613) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 588 l12ZMdSmReshapeB
    8613 5749 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8613 5749 [4096, 1024]

private theorem l12ZMd_red_pm10158 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10158 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14188) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1286 l12ZMdPmReshapeA0
    14188 10158 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14188 10158 [2048, 1024]

private theorem l12ZMd_red_pm10159 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10159 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14189) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1290 l12ZMdPmReshapeA1
    14189 10159 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14189 10159 [2048, 1024]

private theorem l12ZMd_red_pm10170 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10170 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14200) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1287 l12ZMdPmReshapeB0
    14200 10170 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14200 10170 [2048, 1024]

private theorem l12ZMd_red_pm10171 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10171 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14201) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1291 l12ZMdPmReshapeB1
    14201 10171 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14201 10171 [2048, 1024]

private theorem l12ZMd_red_sm5748 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5748 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5747) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 595 l12ZMdSmViewA
    5747 5748 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5747 5748

private theorem l12ZMd_red_sm5752 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5752 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5751) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 596 l12ZMdSmViewB
    5751 5752 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5751 5752

private theorem l12ZMd_red_pm10164 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10164 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10162) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1301 l12ZMdPmViewA0
    10162 10164 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10162 10164

private theorem l12ZMd_red_pm10165 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10165 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10163) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1306 l12ZMdPmViewA1
    10163 10165 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10163 10165

private theorem l12ZMd_red_pm10176 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10176 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10174) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1302 l12ZMdPmViewB0
    10174 10176 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10174 10176

private theorem l12ZMd_red_pm10177 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10177 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10175) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1307 l12ZMdPmViewB1
    10175 10177 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10175 10177

private theorem l12ZMd_red_sm5754 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5754 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5753) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 600 l12ZMdSmReshapeDown
    5753 5754 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5753 5754 [4096, 512]

private theorem l12ZMd_red_pm10184 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10184 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10182) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1314 l12ZMdPmReshapeDown0
    10182 10184 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10182 10184 [2048, 512]

private theorem l12ZMd_red_pm10185 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10185 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10183) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1317 l12ZMdPmReshapeDown1
    10183 10185 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10183 10185 [2048, 512]

private theorem l12ZMd_red_sm5757 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5757 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5756) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 602 l12ZMdSmViewDown
    5756 5757 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5756 5757

private theorem l12ZMd_red_pm10192 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10192 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10190) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1322 l12ZMdPmViewDown0
    10190 10192 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10190 10192

private theorem l12ZMd_red_pm10193 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10193 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10191) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1323 l12ZMdPmViewDown1
    10191 10193 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10191 10193

private theorem l12ZMd_red_sm5747 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5747 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5745)
        (denoteGraphDistributedFaithful sm_goal_1 init 5746) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 591 l12ZMdSmLinearA
    5745 5746 5747 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5745 5746 5747

private theorem l12ZMd_red_sm5751 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5751 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5749)
        (denoteGraphDistributedFaithful sm_goal_1 init 5750) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 592 l12ZMdSmLinearB
    5749 5750 5751 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5749 5750 5751

private theorem l12ZMd_red_pm10162 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10162 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10158)
        (denoteGraphDistributedFaithful pm_goal_1 init 5746) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1293 l12ZMdPmLinearA0
    10158 5746 10162 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10158 5746 10162

private theorem l12ZMd_red_pm10163 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10163 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10159)
        (denoteGraphDistributedFaithful pm_goal_1 init 5746) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1298 l12ZMdPmLinearA1
    10159 5746 10163 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10159 5746 10163

private theorem l12ZMd_red_pm10174 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10174 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10170)
        (denoteGraphDistributedFaithful pm_goal_1 init 5750) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1294 l12ZMdPmLinearB0
    10170 5750 10174 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10170 5750 10174

private theorem l12ZMd_red_pm10175 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10175 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10171)
        (denoteGraphDistributedFaithful pm_goal_1 init 5750) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1299 l12ZMdPmLinearB1
    10171 5750 10175 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10171 5750 10175

private theorem l12ZMd_red_sm5753 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5753 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5748)
        (denoteGraphDistributedFaithful sm_goal_1 init 5752) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 599 l12ZMdSmSwi
    5748 5752 5753 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5748 5752 5753

private theorem l12ZMd_red_pm10182 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10182 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10164)
        (denoteGraphDistributedFaithful pm_goal_1 init 10176) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1309 l12ZMdPmSwi0
    10164 10176 10182 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 10164 10176 10182

private theorem l12ZMd_red_pm10183 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10183 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10165)
        (denoteGraphDistributedFaithful pm_goal_1 init 10177) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1313 l12ZMdPmSwi1
    10165 10177 10183 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 10165 10177 10183

private theorem l12ZMd_red_sm5756 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5756 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5754)
        (denoteGraphDistributedFaithful sm_goal_1 init 5755) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 601 l12ZMdSmLinearDown
    5754 5755 5756 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5754 5755 5756

private theorem l12ZMd_red_pm10190 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10190 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10184)
        (denoteGraphDistributedFaithful pm_goal_1 init 5755) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1318 l12ZMdPmLinearDown0
    10184 5755 10190 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10184 5755 10190

private theorem l12ZMd_red_pm10191 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10191 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10185)
        (denoteGraphDistributedFaithful pm_goal_1 init 5755) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1321 l12ZMdPmLinearDown1
    10185 5755 10191 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10185 5755 10191

private theorem l12ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l12ZMd_weight_eq (initSM initPM : Store)
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
  rw [l12ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l12ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l12ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l12ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L21 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem goal1_l12_block3_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5730)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10126)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10127)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5757)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10192)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8609)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14188)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14189)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm8609 initSM, l12ZMd_red_pm14188 initPM, l12ZMd_red_pm14189 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8613)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14200)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm8613 initSM, l12ZMd_red_pm14200 initPM, l12ZMd_red_pm14201 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5745)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10158)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10159)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm5745 initSM, l12ZMd_red_pm10158 initPM, l12ZMd_red_pm10159 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5749)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10170)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10171)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm5749 initSM, l12ZMd_red_pm10170 initPM, l12ZMd_red_pm10171 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l12ZMd_weight_eq initSM initPM hInit initGoal_5746 (by native_decide)
    5746 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l12ZMd_weight_eq initSM initPM hInit initGoal_5750 (by native_decide)
    5750 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l12ZMd_weight_shape initPM hPM 5746 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l12ZMd_weight_shape initPM hPM 5750 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5747)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10163)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5747 initSM, l12ZMd_red_pm10162 initPM,
      l12ZMd_red_pm10163 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5751)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10174)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10175)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5751 initSM, l12ZMd_red_pm10174 initPM,
      l12ZMd_red_pm10175 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5748)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10164)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10165)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5748 initSM, l12ZMd_red_pm10164 initPM, l12ZMd_red_pm10165 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5752)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10176)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10177)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5752 initSM, l12ZMd_red_pm10176 initPM, l12ZMd_red_pm10177 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5748)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10164)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10165)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5752)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10176)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10177)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5753)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10182)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10183)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5753 initSM, l12ZMd_red_pm10182 initPM, l12ZMd_red_pm10183 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10184)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10185)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l12ZMd_red_sm5754 initSM, l12ZMd_red_pm10184 initPM, l12ZMd_red_pm10185 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l12ZMd_weight_eq initSM initPM hInit initGoal_5755 (by native_decide)
    5755 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l12ZMd_weight_shape initPM hPM 5755 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5756)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10190)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10191)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l12ZMd_red_sm5756 initSM, l12ZMd_red_pm10190 initPM,
      l12ZMd_red_pm10191 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l12ZMd_red_sm5757 initSM, l12ZMd_red_pm10192 initPM, l12ZMd_red_pm10193 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
