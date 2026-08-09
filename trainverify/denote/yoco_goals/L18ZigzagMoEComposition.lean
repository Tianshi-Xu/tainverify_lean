/- Canonical Goal 1, layer 18: complete faithful composition from the L18 attention residual. -/
import denote.yoco_goals.L18ZigzagMoEDown
import denote.yoco_goals.L18ZigzagMoEExpertDown
import denote.yoco_goals.L18ZigzagMoEOutput

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

/-- The complete canonical L18 faithful relation.  Its sole computed-lineage
premise is the exact L18 attention residual relation; normalization, activation, routing,
remote expert execution, scalar gating, dense down projection, residual bypass,
and the final MoE/residual join are all closed internally. -/
theorem l18_zigzag_moe_output_from_attention_output (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6085)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11136)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11137)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hNorm :=
    l18_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  have hActivation :=
    l18_zigzag_moe_activation_from_attention_output initSM initPM hInit hAttention
  have hRouter :=
    l18_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm
  have hExpert :=
    l18_zigzag_moe_expert_from_branch_inputs initSM initPM hSM hPM hInit
      hActivation hRouter.1 hRouter.2
  have hGate :=
    l18_zigzag_moe_gate_from_norm_input initSM initPM hPM hInit hNorm
  have hDown :=
    l18_zigzag_moe_down_from_norm_input initSM initPM hPM hInit hNorm
  have hResidual :=
    l18_zigzag_moe_residual_from_attention_output initSM initPM hAttention
  exact l18_zigzag_moe_output_from_branch_inputs initSM initPM
    hResidual hExpert hGate hDown

#print axioms l18_zigzag_moe_output_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
