/- Canonical Goal 1, layer 14: upstream residual boundary. -/
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

private def cL15UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5869], outs := [8695, 8699],
    params := [2] }
private def cL15UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10520], outs := [16246, 16250],
    params := [2] }
private def cL15UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10521], outs := [16254, 16258],
    params := [2] }

private theorem cL15Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL15Up_red_sm8621 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8699 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5869 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 677 cL15UpSmMulti
    5869 8699 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL15Up_apply_multiref_second sm_goal_1 s 0 5869 8695 8699 (by native_decide)

private theorem cL15Up_red_pm16186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16250 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10520 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1484 cL15UpPmMulti0
    10520 16250 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL15Up_apply_multiref_second pm_goal_1 s 0 10520 16246 16250 (by native_decide)

private theorem cL15Up_red_pm16194 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16258 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10521 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1485 cL15UpPmMulti1
    10521 16258 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL15UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL15Up_apply_multiref_second pm_goal_1 s 1 10521 16254 16258 (by native_decide)

/-- The L15 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem canonical_l15_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10520)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10521)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8699)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16250)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16258)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL15Up_red_sm8621 initSM, cL15Up_red_pm16186 initPM,
    cL15Up_red_pm16194 initPM]
  exact hIncoming

#print axioms canonical_l15_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
