/- Canonical Goal 1, layer 14: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.L14ZigzagMoEResidualGate

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

private def l14ZMdSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5838], outs := [8675, 8679, 8683, 8687, 8691], params := [5] }

private def l14ZMdPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10434], outs := [15404, 14396, 14406, 14420, 14432], params := [5] }

private def l14ZMdPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10435], outs := [15406, 14397, 14407, 14421, 14433], params := [5] }

private def l14ZMdSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8687], outs := [5853], params := [4096, 1024] }

private def l14ZMdSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8691], outs := [5857], params := [4096, 1024] }

private def l14ZMdPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14420], outs := [10466], params := [2048, 1024] }

private def l14ZMdPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14421], outs := [10467], params := [2048, 1024] }

private def l14ZMdPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [14432], outs := [10478], params := [2048, 1024] }

private def l14ZMdPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [14433], outs := [10479], params := [2048, 1024] }

private def l14ZMdSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5853, 5854], outs := [5855] }

private def l14ZMdSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5857, 5858], outs := [5859] }

private def l14ZMdPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10466, 5854], outs := [10470] }

private def l14ZMdPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10467, 5854], outs := [10471] }

private def l14ZMdPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10478, 5858], outs := [10482] }

private def l14ZMdPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10479, 5858], outs := [10483] }

private def l14ZMdSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5855], outs := [5856], params := [4096, 512] }

private def l14ZMdSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5859], outs := [5860], params := [4096, 512] }

private def l14ZMdPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10470], outs := [10472], params := [2048, 512] }

private def l14ZMdPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10471], outs := [10473], params := [2048, 512] }

private def l14ZMdPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10482], outs := [10484], params := [2048, 512] }

private def l14ZMdPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10483], outs := [10485], params := [2048, 512] }

private def l14ZMdSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [5856, 5860], outs := [5861] }

private def l14ZMdPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [10472, 10484], outs := [10490] }

private def l14ZMdPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [10473, 10485], outs := [10491] }

private def l14ZMdSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5861], outs := [5862], params := [4096, 512] }

private def l14ZMdPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [10490], outs := [10492], params := [2048, 512] }

private def l14ZMdPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [10491], outs := [10493], params := [2048, 512] }

private def l14ZMdSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5862, 5863], outs := [5864] }

private def l14ZMdPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10492, 5863], outs := [10498] }

private def l14ZMdPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10493, 5863], outs := [10499] }

private def l14ZMdSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5864], outs := [5865], params := [4096, 1024] }

private def l14ZMdPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [10498], outs := [10500], params := [2048, 1024] }

private def l14ZMdPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [10499], outs := [10501], params := [2048, 1024] }

private theorem l14ZMd_red_sm8687 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8687 =
      denoteGraphDistributedFaithful sm_goal_1 init 5838 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 654 l14ZMdSmRef
    5838 8687 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5838 [8948, 8952, 8956, 8687, 8691] 5 rfl 8687 (by decide)

private theorem l14ZMd_red_sm8691 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8691 =
      denoteGraphDistributedFaithful sm_goal_1 init 5838 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 654 l14ZMdSmRef
    5838 8691 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5838 [8948, 8952, 8956, 8687, 8691] 5 rfl 8691 (by decide)

private theorem l14ZMd_red_pm14420 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14420 =
      denoteGraphDistributedFaithful pm_goal_1 init 10434 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1435 l14ZMdPmRef0
    10434 14420 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10434 [15404, 14396, 14406, 14420, 14432] 5 rfl 14420 (by decide)

private theorem l14ZMd_red_pm14432 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14432 =
      denoteGraphDistributedFaithful pm_goal_1 init 10434 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1435 l14ZMdPmRef0
    10434 14432 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10434 [15404, 14396, 14406, 14420, 14432] 5 rfl 14432 (by decide)

private theorem l14ZMd_red_pm14421 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14421 =
      denoteGraphDistributedFaithful pm_goal_1 init 10435 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1436 l14ZMdPmRef1
    10435 14421 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10435 [15406, 14397, 14407, 14421, 14433] 5 rfl 14421 (by decide)

private theorem l14ZMd_red_pm14433 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 14433 =
      denoteGraphDistributedFaithful pm_goal_1 init 10435 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1436 l14ZMdPmRef1
    10435 14433 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10435 [15406, 14397, 14407, 14421, 14433] 5 rfl 14433 (by decide)

private theorem l14ZMd_red_sm5853 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5853 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8687) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 657 l14ZMdSmReshapeA
    8687 5853 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8687 5853 [4096, 1024]

private theorem l14ZMd_red_sm5857 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5857 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8691) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 658 l14ZMdSmReshapeB
    8691 5857 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8691 5857 [4096, 1024]

private theorem l14ZMd_red_pm10466 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10466 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14420) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1438 l14ZMdPmReshapeA0
    14420 10466 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14420 10466 [2048, 1024]

private theorem l14ZMd_red_pm10467 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10467 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14421) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1442 l14ZMdPmReshapeA1
    14421 10467 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14421 10467 [2048, 1024]

private theorem l14ZMd_red_pm10478 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10478 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14432) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1439 l14ZMdPmReshapeB0
    14432 10478 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 14432 10478 [2048, 1024]

private theorem l14ZMd_red_pm10479 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10479 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 14433) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1443 l14ZMdPmReshapeB1
    14433 10479 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 14433 10479 [2048, 1024]

private theorem l14ZMd_red_sm5856 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5856 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5855) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 665 l14ZMdSmViewA
    5855 5856 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5855 5856

private theorem l14ZMd_red_sm5860 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5860 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5859) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 666 l14ZMdSmViewB
    5859 5860 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 5859 5860

private theorem l14ZMd_red_pm10472 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10472 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10470) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1453 l14ZMdPmViewA0
    10470 10472 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10470 10472

private theorem l14ZMd_red_pm10473 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10473 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10471) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1458 l14ZMdPmViewA1
    10471 10473 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10471 10473

private theorem l14ZMd_red_pm10484 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10484 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10482) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1454 l14ZMdPmViewB0
    10482 10484 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 10482 10484

private theorem l14ZMd_red_pm10485 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10485 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10483) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1459 l14ZMdPmViewB1
    10483 10485 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 10483 10485

private theorem l14ZMd_red_sm5862 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5862 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 5861) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 670 l14ZMdSmReshapeDown
    5861 5862 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 5861 5862 [4096, 512]

private theorem l14ZMd_red_pm10492 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10492 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10490) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1466 l14ZMdPmReshapeDown0
    10490 10492 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 10490 10492 [2048, 512]

private theorem l14ZMd_red_pm10493 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10493 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 10491) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1469 l14ZMdPmReshapeDown1
    10491 10493 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 10491 10493 [2048, 512]

private theorem l14ZMd_red_sm5865 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5865 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 5864) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 672 l14ZMdSmViewDown
    5864 5865 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 5864 5865

private theorem l14ZMd_red_pm10500 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10500 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10498) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1474 l14ZMdPmViewDown0
    10498 10500 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 10498 10500

private theorem l14ZMd_red_pm10501 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10501 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 10499) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1475 l14ZMdPmViewDown1
    10499 10501 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 10499 10501

private theorem l14ZMd_red_sm5855 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5855 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5853)
        (denoteGraphDistributedFaithful sm_goal_1 init 5854) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 661 l14ZMdSmLinearA
    5853 5854 5855 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5853 5854 5855

private theorem l14ZMd_red_sm5859 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5859 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5857)
        (denoteGraphDistributedFaithful sm_goal_1 init 5858) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 662 l14ZMdSmLinearB
    5857 5858 5859 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5857 5858 5859

private theorem l14ZMd_red_pm10470 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10470 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10466)
        (denoteGraphDistributedFaithful pm_goal_1 init 5854) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1445 l14ZMdPmLinearA0
    10466 5854 10470 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10466 5854 10470

private theorem l14ZMd_red_pm10471 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10471 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10467)
        (denoteGraphDistributedFaithful pm_goal_1 init 5854) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1450 l14ZMdPmLinearA1
    10467 5854 10471 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10467 5854 10471

private theorem l14ZMd_red_pm10482 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10482 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10478)
        (denoteGraphDistributedFaithful pm_goal_1 init 5858) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1446 l14ZMdPmLinearB0
    10478 5858 10482 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10478 5858 10482

private theorem l14ZMd_red_pm10483 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10483 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10479)
        (denoteGraphDistributedFaithful pm_goal_1 init 5858) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1451 l14ZMdPmLinearB1
    10479 5858 10483 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10479 5858 10483

private theorem l14ZMd_red_sm5861 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5861 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 5856)
        (denoteGraphDistributedFaithful sm_goal_1 init 5860) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 669 l14ZMdSmSwi
    5856 5860 5861 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 5856 5860 5861

private theorem l14ZMd_red_pm10490 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10490 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10472)
        (denoteGraphDistributedFaithful pm_goal_1 init 10484) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1461 l14ZMdPmSwi0
    10472 10484 10490 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 10472 10484 10490

private theorem l14ZMd_red_pm10491 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10491 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 10473)
        (denoteGraphDistributedFaithful pm_goal_1 init 10485) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1465 l14ZMdPmSwi1
    10473 10485 10491 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 10473 10485 10491

private theorem l14ZMd_red_sm5864 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 5864 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 5862)
        (denoteGraphDistributedFaithful sm_goal_1 init 5863) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 671 l14ZMdSmLinearDown
    5862 5863 5864 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5862 5863 5864

private theorem l14ZMd_red_pm10498 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10498 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10492)
        (denoteGraphDistributedFaithful pm_goal_1 init 5863) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1470 l14ZMdPmLinearDown0
    10492 5863 10498 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 10492 5863 10498

private theorem l14ZMd_red_pm10499 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 10499 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 10493)
        (denoteGraphDistributedFaithful pm_goal_1 init 5863) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1473 l14ZMdPmLinearDown1
    10493 5863 10499 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l14ZMdPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 10493 5863 10499

private theorem l14ZMd_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem l14ZMd_weight_eq (initSM initPM : Store)
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
  rw [l14ZMd_leaf sm_goal_1 initSM W (by native_decide) hsm,
    l14ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem l14ZMd_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [l14ZMd_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L14 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem l14_zigzag_moe_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10434)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10435)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5865)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10500)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10501)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8687)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14420)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14421)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMd_red_sm8687 initSM, l14ZMd_red_pm14420 initPM, l14ZMd_red_pm14421 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8691)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14432)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 14433)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMd_red_sm8691 initSM, l14ZMd_red_pm14432 initPM, l14ZMd_red_pm14433 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5853)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10466)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10467)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMd_red_sm5853 initSM, l14ZMd_red_pm10466 initPM, l14ZMd_red_pm10467 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5857)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMd_red_sm5857 initSM, l14ZMd_red_pm10478 initPM, l14ZMd_red_pm10479 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := l14ZMd_weight_eq initSM initPM hInit initGoal_5854 (by native_decide)
    5854 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := l14ZMd_weight_eq initSM initPM hInit initGoal_5858 (by native_decide)
    5858 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := l14ZMd_weight_shape initPM hPM 5854 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := l14ZMd_weight_shape initPM hPM 5858 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5855)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10470)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10471)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l14ZMd_red_sm5855 initSM, l14ZMd_red_pm10470 initPM,
      l14ZMd_red_pm10471 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5859)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10482)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10483)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l14ZMd_red_sm5859 initSM, l14ZMd_red_pm10482 initPM,
      l14ZMd_red_pm10483 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5856)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10472)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10473)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l14ZMd_red_sm5856 initSM, l14ZMd_red_pm10472 initPM, l14ZMd_red_pm10473 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5860)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10484)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10485)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l14ZMd_red_sm5860 initSM, l14ZMd_red_pm10484 initPM, l14ZMd_red_pm10485 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5856)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10472)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10473)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5860)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10484)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10485)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5861)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10490)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10491)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l14ZMd_red_sm5861 initSM, l14ZMd_red_pm10490 initPM, l14ZMd_red_pm10491 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10492)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10493)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [l14ZMd_red_sm5862 initSM, l14ZMd_red_pm10492 initPM, l14ZMd_red_pm10493 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := l14ZMd_weight_eq initSM initPM hInit initGoal_5863 (by native_decide)
    5863 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := l14ZMd_weight_shape initPM hPM 5863 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5864)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10498)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10499)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [l14ZMd_red_sm5864 initSM, l14ZMd_red_pm10498 initPM,
      l14ZMd_red_pm10499 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [l14ZMd_red_sm5865 initSM, l14ZMd_red_pm10500 initPM, l14ZMd_red_pm10501 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
