/- Canonical Goal 1, layer 19: upstream residual boundary. -/
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

private def cL19UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6085], outs := [8851, 8855],
    params := [2] }
private def cL19UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11136], outs := [16374, 16378],
    params := [2] }
private def cL19UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11137], outs := [16382, 16386],
    params := [2] }

private theorem cL19Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL19Up_red_sm8621 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8855 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6085 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 817 cL19UpSmMulti
    6085 8855 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL19Up_apply_multiref_second sm_goal_1 s 0 6085 8851 8855 (by native_decide)

private theorem cL19Up_red_pm16186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16378 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11136 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1788 cL19UpPmMulti0
    11136 16378 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL19Up_apply_multiref_second pm_goal_1 s 0 11136 16374 16378 (by native_decide)

private theorem cL19Up_red_pm16194 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16386 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11137 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1789 cL19UpPmMulti1
    11137 16386 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL19UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL19Up_apply_multiref_second pm_goal_1 s 1 11137 16382 16386 (by native_decide)

/-- The L19 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem canonical_l19_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6085)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11136)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11137)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8855)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16378)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16386)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL19Up_red_sm8621 initSM, cL19Up_red_pm16186 initPM,
    cL19Up_red_pm16194 initPM]
  exact hIncoming

#print axioms canonical_l19_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
