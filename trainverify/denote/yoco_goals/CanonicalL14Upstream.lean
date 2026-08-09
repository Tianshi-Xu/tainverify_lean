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

private def cL14UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5815], outs := [8656, 8660],
    params := [2] }
private def cL14UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10366], outs := [16214, 16218],
    params := [2] }
private def cL14UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10367], outs := [16222, 16226],
    params := [2] }

private theorem cL14Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL14Up_red_sm8621 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8660 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5815 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 642 cL14UpSmMulti
    5815 8660 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL14Up_apply_multiref_second sm_goal_1 s 0 5815 8656 8660 (by native_decide)

private theorem cL14Up_red_pm16186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16218 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10366 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1408 cL14UpPmMulti0
    10366 16218 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL14Up_apply_multiref_second pm_goal_1 s 0 10366 16214 16218 (by native_decide)

private theorem cL14Up_red_pm16194 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16226 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10367 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1409 cL14UpPmMulti1
    10367 16226 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL14UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL14Up_apply_multiref_second pm_goal_1 s 1 10367 16222 16226 (by native_decide)

/-- The L14 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem canonical_l14_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5815)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10366)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10367)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8660)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16226)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL14Up_red_sm8621 initSM, cL14Up_red_pm16186 initPM,
    cL14Up_red_pm16194 initPM]
  exact hIncoming

#print axioms canonical_l14_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
