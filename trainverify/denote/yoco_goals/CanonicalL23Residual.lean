/- Canonical Goal 1, layer 23: residual bypass through the generated multiref nodes. -/
import denote.yoco_goals.CanonicalL23Output

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def cL23ResidualSm : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6214],
    outs := [8937, 8941], params := [2] }

private def cL23ResidualPm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11508],
    outs := [16454, 16458], params := [2] }

private def cL23ResidualPm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11509],
    outs := [16462, 16466], params := [2] }

private theorem cL23Residual_red_sm8941 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8941 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6214 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 897 cL23ResidualSm
    6214 8941 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23ResidualSm
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 6214 8937 8941
    (by decide)

private theorem cL23Residual_red_pm16458 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16458 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11508 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1963 cL23ResidualPm0
    11508 16458 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23ResidualPm0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 11508 16454 16458
    (by decide)

private theorem cL23Residual_red_pm16466 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16466 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11509 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1964 cL23ResidualPm1
    11509 16466 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23ResidualPm1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 11509 16462 16466
    (by decide)

/-- The three generated residual-bypass outputs are exactly the preceding
layer output values.  This is the graph-derived, assumption-free part of the
canonical L23 residual branch. -/
theorem canonical_l23_residual_bypass_values (initSM initPM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8941 =
        denoteGraphDistributedFaithful sm_goal_1 initSM 6214 ∧
      denoteGraphDistributedFaithful pm_goal_1 initPM 16458 =
        denoteGraphDistributedFaithful pm_goal_1 initPM 11508 ∧
      denoteGraphDistributedFaithful pm_goal_1 initPM 16466 =
        denoteGraphDistributedFaithful pm_goal_1 initPM 11509 := by
  exact ⟨cL23Residual_red_sm8941 initSM, cL23Residual_red_pm16458 initPM,
    cL23Residual_red_pm16466 initPM⟩

/-- Composable residual segment: a zigzag relation at the preceding layer
output transports through the real canonical `FW_multiref` nodes to exactly
the `hResidual` relation consumed by `canonical_l23_output_from_join_inputs`.
No relation over the computed bypass is added to an external caller contract. -/
theorem canonical_l23_residual_from_layer22_output (initSM initPM : Store)
    (hLayer22 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6214)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11508)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11509)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8941)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16458)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16466)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL23Residual_red_sm8941 initSM, cL23Residual_red_pm16458 initPM,
    cL23Residual_red_pm16466 initPM]
  exact hLayer22

end
end TrainVerify.Denote.GeneratedPatterns
