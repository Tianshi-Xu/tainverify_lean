/- Canonical Goal 1, layer 20: upstream residual boundary. -/
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

private def cL20UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6139], outs := [8890, 8894],
    params := [2] }
private def cL20UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11290], outs := [16406, 16410],
    params := [2] }
private def cL20UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11291], outs := [16414, 16418],
    params := [2] }

private theorem cL20Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL20Up_red_sm8894 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8894 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6139 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 852 cL20UpSmMulti
    6139 8894 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL20Up_apply_multiref_second sm_goal_1 s 0 6139 8890 8894 (by native_decide)

private theorem cL20Up_red_pm16410 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16410 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11290 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1864 cL20UpPmMulti0
    11290 16410 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL20Up_apply_multiref_second pm_goal_1 s 0 11290 16406 16410 (by native_decide)

private theorem cL20Up_red_pm16418 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16418 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11291 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1865 cL20UpPmMulti1
    11291 16418 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL20UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL20Up_apply_multiref_second pm_goal_1 s 1 11291 16414 16418 (by native_decide)

/-- The L20 residual premise is not an independent boundary assumption: it is
exactly the second output of the real L19 two-way multiref on every rank. -/
theorem canonical_l20_residual_from_l19_output (initSM initPM : Store)
    (hL19Output : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6139)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11291)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8894)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16410)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16418)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL20Up_red_sm8894 initSM, cL20Up_red_pm16410 initPM,
    cL20Up_red_pm16418 initPM]
  exact hL19Output

#print axioms canonical_l20_residual_from_l19_output

end
end TrainVerify.Denote.GeneratedPatterns
