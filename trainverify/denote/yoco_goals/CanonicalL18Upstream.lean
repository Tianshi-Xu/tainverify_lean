/- Canonical Goal 1, layer 18: upstream residual boundary. -/
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

private def cL18UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6031], outs := [8812, 8816],
    params := [2] }
private def cL18UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10982], outs := [16342, 16346],
    params := [2] }
private def cL18UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10983], outs := [16350, 16354],
    params := [2] }

private theorem cL18Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL18Up_red_sm8621 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8816 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6031 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 782 cL18UpSmMulti
    6031 8816 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL18Up_apply_multiref_second sm_goal_1 s 0 6031 8812 8816 (by native_decide)

private theorem cL18Up_red_pm16186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16346 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10982 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1712 cL18UpPmMulti0
    10982 16346 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL18Up_apply_multiref_second pm_goal_1 s 0 10982 16342 16346 (by native_decide)

private theorem cL18Up_red_pm16194 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16354 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10983 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1713 cL18UpPmMulti1
    10983 16354 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL18UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL18Up_apply_multiref_second pm_goal_1 s 1 10983 16350 16354 (by native_decide)

/-- The L18 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem canonical_l18_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8816)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16346)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL18Up_red_sm8621 initSM, cL18Up_red_pm16186 initPM,
    cL18Up_red_pm16194 initPM]
  exact hIncoming

#print axioms canonical_l18_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
