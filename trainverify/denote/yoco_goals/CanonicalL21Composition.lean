/- Canonical Goal 1, layer 21: complete faithful composition from the L20 output. -/
import denote.yoco_goals.CanonicalL21Down
import denote.yoco_goals.CanonicalL21ExpertDown
import denote.yoco_goals.CanonicalL21Output

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

/-- The complete canonical L21 faithful relation.  Its sole computed-lineage
premise is the exact L20 output relation; normalization, activation, routing,
remote expert execution, scalar gating, dense down projection, residual bypass,
and the final MoE/residual join are all closed internally. -/
theorem canonical_l21_output_from_layer20_output (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hLayer20 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm :=
    canonical_l21_norm_from_layer20_output initSM initPM hInit hLayer20
  have hActivation :=
    canonical_l21_activation_from_layer20_output initSM initPM hInit hLayer20
  have hRouter :=
    canonical_l21_router_from_norm_input initSM initPM hPM hInit hNorm
  have hExpert :=
    canonical_l21_expert_from_branch_inputs initSM initPM hSM hPM hInit
      hActivation hRouter.1 hRouter.2
  have hGate :=
    canonical_l21_gate_from_norm_input initSM initPM hPM hInit hNorm
  have hDown :=
    canonical_l21_down_from_norm_input initSM initPM hPM hInit hNorm
  have hResidual :=
    canonical_l21_residual_from_layer20_output initSM initPM hLayer20
  exact canonical_l21_output_from_branch_inputs initSM initPM
    hResidual hExpert hGate hDown

#print axioms canonical_l21_output_from_layer20_output

end
end TrainVerify.Denote.GeneratedPatterns
