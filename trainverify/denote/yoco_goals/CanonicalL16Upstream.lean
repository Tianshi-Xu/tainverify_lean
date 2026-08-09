/- Canonical Goal 1, layer 15: upstream residual boundary. -/
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

private def cL16UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5923], outs := [8734, 8738],
    params := [2] }
private def cL16UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10674], outs := [16278, 16282],
    params := [2] }
private def cL16UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10675], outs := [16286, 16290],
    params := [2] }

private theorem cL16Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL16Up_red_sm8621 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8738 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5923 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 712 cL16UpSmMulti
    5923 8738 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL16Up_apply_multiref_second sm_goal_1 s 0 5923 8734 8738 (by native_decide)

private theorem cL16Up_red_pm16186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16282 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10674 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1560 cL16UpPmMulti0
    10674 16282 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL16Up_apply_multiref_second pm_goal_1 s 0 10674 16278 16282 (by native_decide)

private theorem cL16Up_red_pm16194 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16290 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10675 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1561 cL16UpPmMulti1
    10675 16290 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL16UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL16Up_apply_multiref_second pm_goal_1 s 1 10675 16286 16290 (by native_decide)

/-- The L16 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem canonical_l16_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5923)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10675)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16282)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL16Up_red_sm8621 initSM, cL16Up_red_pm16186 initPM,
    cL16Up_red_pm16194 initPM]
  exact hIncoming

#print axioms canonical_l16_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
