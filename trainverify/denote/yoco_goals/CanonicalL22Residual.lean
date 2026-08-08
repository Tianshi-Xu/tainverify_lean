/- Canonical Goal 1, layer 22: residual bypass through the generated multiref nodes. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLayoutRel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def cL22ResidualSm : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6193],
    outs := [8929, 8933], params := [2] }

private def cL22ResidualPm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11444],
    outs := [16438, 16442], params := [2] }

private def cL22ResidualPm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11445],
    outs := [16446, 16450], params := [2] }

private theorem cL22Residual_red_sm8933 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8933 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6193 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 887 cL22ResidualSm
    6193 8933 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22ResidualSm
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 sm_goal_1 s 0 6193 8929 8933
    (by decide)

private theorem cL22Residual_red_pm16442 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16442 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11444 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1940 cL22ResidualPm0
    11444 16442 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22ResidualPm0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 0 11444 16438 16442
    (by decide)

private theorem cL22Residual_red_pm16450 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16450 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11445 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1941 cL22ResidualPm1
    11445 16450 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL22ResidualPm1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref2_second_out_g259 pm_goal_1 s 1 11445 16446 16450
    (by decide)

/-- The three generated L22 residual-bypass outputs are exactly the preceding
layer output values. This is the graph-derived, assumption-free segment. -/
theorem canonical_l22_residual_bypass_values (initSM initPM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8933 =
        denoteGraphDistributedFaithful sm_goal_1 initSM 6193 ∧
      denoteGraphDistributedFaithful pm_goal_1 initPM 16442 =
        denoteGraphDistributedFaithful pm_goal_1 initPM 11444 ∧
      denoteGraphDistributedFaithful pm_goal_1 initPM 16450 =
        denoteGraphDistributedFaithful pm_goal_1 initPM 11445 := by
  exact ⟨cL22Residual_red_sm8933 initSM, cL22Residual_red_pm16442 initPM,
    cL22Residual_red_pm16450 initPM⟩

/-- A zigzag relation at the canonical L21 output transports through the real
L22 `FW_multiref` nodes to exactly the residual relation consumed by
`canonical_l22_output_from_inputs`. The computed residual relation remains a
conclusion rather than an external caller premise. -/
theorem canonical_l22_residual_from_layer21_output (initSM initPM : Store)
    (hLayer21 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16442)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL22Residual_red_sm8933 initSM, cL22Residual_red_pm16442 initPM,
    cL22Residual_red_pm16450 initPM]
  exact hLayer21

end
end TrainVerify.Denote.GeneratedPatterns
