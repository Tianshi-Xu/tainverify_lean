/- L8 ordinary MoE composition from attention residual to block output. -/
import denote.yoco_goals.L8OrdinaryMoEBoundary
import denote.yoco_goals.L8OrdinaryMoEExpert
import denote.yoco_goals.L8OrdinaryMoENorm

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

/-- Forget the extra nonscalar certificate carried by `Gather2Rel`, while
preserving every value and shape field explicitly. -/
private theorem ordinary2Rel_of_gather2Rel
    {full rank0 rank1 : Tensor} {fullShape shardShape : Shape}
    (h : Gather2Rel full rank0 rank1 fullShape shardShape) :
    Ordinary2Rel full rank0 rank1 fullShape shardShape := by
  exact {
    full_value := h.value
    full_shape := h.full_shape
    rank0_shape := h.shard0_shape
    rank1_shape := h.shard1_shape
  }

/-- Restore the `Gather2Rel` package from an ordinary relation plus the one
shape-side fact not present in `Ordinary2Rel`. -/
private theorem gather2Rel_of_ordinary2Rel
    {full rank0 rank1 : Tensor} {fullShape shardShape : Shape}
    (h : Ordinary2Rel full rank0 rank1 fullShape shardShape)
    (hnonscalar : shardShape ≠ [1]) :
    Gather2Rel full rank0 rank1 fullShape shardShape := by
  exact {
    value := h.full_value
    full_shape := h.full_shape
    shard0_shape := h.rank0_shape
    shard1_shape := h.rank1_shape
    nonscalar := hnonscalar
  }

/-- Complete ordinary cache-source composition.  The sole computed branch input
is the attention-output relation; normalization, activation, routing, expert,
gate, replicated MLP/down, residual, and the faithful boundary tail are all
assembled internally. -/
theorem l8_ordinary_moe_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9140)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9141)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5430)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9230)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9231)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l8_ordinary_moe_norm_from_attention_output
    initSM initPM hInit hAttention
  have hNormOrd := ordinary2Rel_of_gather2Rel hNorm
  have hActivation := l8_ordinary_moe_activation_from_attention_output
    initSM initPM hInit hAttention
  have hRouter := l8_ordinary_moe_router_from_norm_input
    initSM initPM hPM hInit hNorm
  have hRouterProbs := hRouter.1
  have hRouterMap := hRouter.2
  have hExpert := l8_ordinary_moe_expert_from_branch_inputs
    initSM initPM hSM hPM hInit hActivation hRouterProbs hRouterMap
  have hExpertOrd := ordinary2Rel_of_gather2Rel hExpert
  have hGate := l8_ordinary_moe_gate_from_norm_input
    initSM initPM hPM hInit hNorm
  have hGateOrd := ordinary2Rel_of_gather2Rel hGate
  have hDown := l8_ordinary_moe_down_from_norm_input
    initSM initPM hPM hInit hNormOrd
  have hResidual := l8_ordinary_moe_residual_from_attention_output
    initSM initPM hAttention
  have hResidualOrd := ordinary2Rel_of_gather2Rel hResidual
  have hBoundary := l8_ordinary_moe_boundary_from_branch_inputs
    initSM initPM hResidualOrd hExpertOrd hGateOrd hDown
  exact gather2Rel_of_ordinary2Rel hBoundary (by decide)

#print axioms l8_ordinary_moe_composition

end
end TrainVerify.Denote.GeneratedPatterns
