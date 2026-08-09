/- Canonical Goal 1, layer 16: complete faithful composition from the L16 attention residual. -/
import denote.yoco_goals.L16ZigzagMoEDown
import denote.yoco_goals.L16ZigzagMoEExpertDown
import denote.yoco_goals.L16ZigzagMoEOutput

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

/-- The complete canonical L16 faithful relation.  Its sole computed-lineage
premise is the exact L16 attention residual relation; normalization, activation, routing,
remote expert execution, scalar gating, dense down projection, residual bypass,
and the final MoE/residual join are all closed internally. -/
theorem l16_zigzag_moe_output_from_attention_output (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm :=
    l16_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  have hActivation :=
    l16_zigzag_moe_activation_from_attention_output initSM initPM hInit hAttention
  have hRouter :=
    l16_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm
  have hExpert :=
    l16_zigzag_moe_expert_from_branch_inputs initSM initPM hSM hPM hInit
      hActivation hRouter.1 hRouter.2
  have hGate :=
    l16_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm
  have hDown :=
    l16_zigzag_moe_down_from_norm_input initSM initPM hPM hInit hNorm
  have hResidual :=
    l16_zigzag_moe_residual_from_attention_output initSM initPM hAttention
  exact l16_zigzag_moe_output_from_branch_inputs initSM initPM
    hResidual hExpert hGate hDown

#print axioms l16_zigzag_moe_output_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
