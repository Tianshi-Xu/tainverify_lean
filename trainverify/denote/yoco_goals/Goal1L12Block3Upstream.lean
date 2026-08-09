/- Canonical Goal 1, L12 block 3: upstream residual boundary. -/
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

private def b3UpSmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5707], outs := [8578, 8582],
    params := [2] }
private def b3UpPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10058], outs := [16150, 16154],
    params := [2] }
private def b3UpPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10059], outs := [16158, 16162],
    params := [2] }

private theorem b3Up_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem b3Up_red_sm8621 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8582 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5707 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 572 b3UpSmMulti
    5707 8582 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3UpSmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact b3Up_apply_multiref_second sm_goal_1 s 0 5707 8578 8582 (by native_decide)

private theorem b3Up_red_pm16186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16154 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10058 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1256 b3UpPmMulti0
    10058 16154 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3UpPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact b3Up_apply_multiref_second pm_goal_1 s 0 10058 16150 16154 (by native_decide)

private theorem b3Up_red_pm16194 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16162 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10059 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1257 b3UpPmMulti1
    10059 16162 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold b3UpPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact b3Up_apply_multiref_second pm_goal_1 s 1 10059 16158 16162 (by native_decide)

/-- The L12 block 3 residual branch is derived from the sole computed incoming Zigzag2Rel
interface through the real two-way multiref on every rank. -/
theorem goal1_l12_block3_residual_from_incoming (initSM initPM : Store)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8582)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16154)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [b3Up_red_sm8621 initSM, b3Up_red_pm16186 initPM,
    b3Up_red_pm16194 initPM]
  exact hIncoming

#print axioms goal1_l12_block3_residual_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
