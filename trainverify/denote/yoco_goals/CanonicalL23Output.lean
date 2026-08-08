/- Canonical Goal 1, layer 23: the final float and residual-add segment. -/
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

private def cL23SmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [6245], outs := [6246] }
private def cL23SmAdd : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [8941, 6246], outs := [6247] }
private def cL23PmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [11588], outs := [11594] }
private def cL23PmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11589], outs := [11595] }
private def cL23PmAdd0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_add", ins := [16458, 11594], outs := [11598] }
private def cL23PmAdd1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_add", ins := [16466, 11595], outs := [11599] }

private theorem cL23_red_sm6246 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6246 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6245 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 920 cL23SmFloat
    6245 6246 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23SmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 6245 6246 []

private theorem cL23_red_pm11594 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11594 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11588 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 2012 cL23PmFloat0
    11588 11594 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23PmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 11588 11594 []

private theorem cL23_red_pm11595 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11595 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11589 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 2013 cL23PmFloat1
    11589 11595 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23PmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11589 11595 []

private theorem cL23_red_sm6247 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6247 =
      elemwiseAdd (denoteGraphDistributedFaithful sm_goal_1 initSM 8941)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6246) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 921 cL23SmAdd
    8941 6246 6247 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23SmAdd
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out sm_goal_1 s 0 8941 6246 6247

private theorem cL23_red_pm11598 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11598 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16458)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11594) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 2014 cL23PmAdd0
    16458 11594 11598 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23PmAdd0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 0 16458 11594 11598

private theorem cL23_red_pm11599 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11599 =
      elemwiseAdd (denoteGraphDistributedFaithful pm_goal_1 initPM 16466)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11595) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 2015 cL23PmAdd1
    16466 11595 11599 elemwiseAdd
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23PmAdd1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_add2_out pm_goal_1 s 1 16466 11595 11599

/-- The concrete last two L23 operators preserve the canonical CP2 zigzag
layout.  This is a composable graph theorem: its two premises are precisely the
upstream MoE-join and residual-bypass relations, while its conclusion is the
`hpre` relation consumed by `canonical_loss_backbone_tail`. -/
theorem canonical_l23_output_from_join_inputs (initSM initPM : Store)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8941)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16458)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16466)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hJoin : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6245)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11588)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11589)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hFloat : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11594)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL23_red_sm6246 initSM, cL23_red_pm11594 initPM, cL23_red_pm11595 initPM]
    exact hJoin
  rw [cL23_red_sm6247 initSM, cL23_red_pm11598 initPM, cL23_red_pm11599 initPM]
  exact Zigzag2Rel.add 2048 1024 hResidual hFloat (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
