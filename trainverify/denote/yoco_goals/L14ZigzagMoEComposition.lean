/- Canonical Goal 1, layer 14: complete faithful composition from the L14 attention residual. -/
import denote.yoco_goals.L14ZigzagMoEDown
import denote.yoco_goals.L14ZigzagMoEExpertDown
import denote.yoco_goals.L14ZigzagMoEOutput

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

/-- The complete canonical L14 faithful relation.  Its sole computed-lineage
premise is the exact L14 attention residual relation; normalization, activation, routing,
remote expert execution, scalar gating, dense down projection, residual bypass,
and the final MoE/residual join are all closed internally. -/
theorem l14_zigzag_moe_output_from_attention_output (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10431)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10520)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10521)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm :=
    l14_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  have hActivation :=
    l14_zigzag_moe_activation_from_attention_output initSM initPM hInit hAttention
  have hRouter :=
    l14_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm
  have hExpert :=
    l14_zigzag_moe_expert_from_branch_inputs initSM initPM hSM hPM hInit
      hActivation hRouter.1 hRouter.2
  have hGate :=
    l14_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm
  have hDown :=
    l14_zigzag_moe_down_from_norm_input initSM initPM hPM hInit hNorm
  have hResidual :=
    l14_zigzag_moe_residual_from_attention_output initSM initPM hAttention
  exact l14_zigzag_moe_output_from_branch_inputs initSM initPM
    hResidual hExpert hGate hDown

#print axioms l14_zigzag_moe_output_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
