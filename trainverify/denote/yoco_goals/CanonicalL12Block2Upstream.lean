/- Canonical Goal 1, layer 12 block 2: upstream residual boundary. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagPointwiseRel

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

private def cL12B2UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5653], outs := [8539, 8543],
    params := [2] }
private def cL12B2UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9904], outs := [16118, 16122],
    params := [2] }
private def cL12B2UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9905], outs := [16126, 16130],
    params := [2] }

private theorem cL12B2Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL12B2Up_red_sm8543 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8543 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5653 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 537 cL12B2UpSmMulti
    5653 8543 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12B2Up_apply_multiref_second sm_goal_1 s 0 5653 8539 8543 (by native_decide)

private theorem cL12B2Up_red_pm16122 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16122 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9904 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1180 cL12B2UpPmMulti0
    9904 16122 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12B2Up_apply_multiref_second pm_goal_1 s 0 9904 16118 16122 (by native_decide)

private theorem cL12B2Up_red_pm16130 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16130 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9905 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1181 cL12B2UpPmMulti1
    9905 16130 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL12B2UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12B2Up_apply_multiref_second pm_goal_1 s 1 9905 16126 16130 (by native_decide)

/-- The L12 block 2 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem canonical_l12b2_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8543)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16130)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL12B2Up_red_sm8543 initSM, cL12B2Up_red_pm16122 initPM,
    cL12B2Up_red_pm16130 initPM]
  exact hIncoming

#print axioms canonical_l12b2_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns

