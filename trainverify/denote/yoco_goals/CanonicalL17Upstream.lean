/- Canonical Goal 1, layer 17: upstream residual boundary. -/
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

private def cL17UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5977], outs := [8773, 8777],
    params := [2] }
private def cL17UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10828], outs := [16310, 16314],
    params := [2] }
private def cL17UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10829], outs := [16318, 16322],
    params := [2] }

private theorem cL17Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL17Up_red_sm8621 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8777 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5977 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 747 cL17UpSmMulti
    5977 8777 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL17Up_apply_multiref_second sm_goal_1 s 0 5977 8773 8777 (by native_decide)

private theorem cL17Up_red_pm16186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16314 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10828 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1636 cL17UpPmMulti0
    10828 16314 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL17Up_apply_multiref_second pm_goal_1 s 0 10828 16310 16314 (by native_decide)

private theorem cL17Up_red_pm16194 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16322 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10829 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1637 cL17UpPmMulti1
    10829 16322 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL17UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL17Up_apply_multiref_second pm_goal_1 s 1 10829 16318 16322 (by native_decide)

/-- The L17 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem canonical_l17_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8777)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16314)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16322)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL17Up_red_sm8621 initSM, cL17Up_red_pm16186 initPM,
    cL17Up_red_pm16194 initPM]
  exact hIncoming

#print axioms canonical_l17_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
