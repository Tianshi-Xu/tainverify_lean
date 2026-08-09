/- L12 ordinary MoE composition from the exact attention residual to block output. -/
import denote.yoco_goals.L12OrdinaryMoEBoundary
import denote.yoco_goals.L12OrdinaryMoEExpert
import denote.yoco_goals.L12OrdinaryMoENorm

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

/-- Exact-scope faithful L12 MoE/output tail.  The sole computed input is the
true attention residual at `5620 ↔ 9812/9813`; all subsequent normalization,
routing, expert, gate/down, bypass, and output nodes are discharged internally. -/
theorem l12_ordinary_moe_composition (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      [4096, 1024] [2048, 1024] := by
  have hNorm := l12_ordinary_moe_norm_from_attention_output
    initSM initPM hInit hAttention
  have hNormOrd := ordinary2Rel_of_gather2Rel hNorm
  have hActivation := l12_ordinary_moe_activation_from_attention_output
    initSM initPM hInit hAttention
  have hRouter := l12_ordinary_moe_router_from_norm_input
    initSM initPM hPM hInit hNorm
  have hExpert := l12_ordinary_moe_expert_from_branch_inputs
    initSM initPM hSM hPM hInit hActivation hRouter.1 hRouter.2
  have hGate := l12_ordinary_moe_gate_from_norm_input
    initSM initPM hPM hInit hNorm
  have hDown := l12_ordinary_moe_down_from_norm_input
    initSM initPM hPM hInit hNormOrd
  have hResidual := l12_ordinary_moe_residual_from_attention_output
    initSM initPM hAttention
  have hBoundary := l12_ordinary_moe_boundary_from_branch_inputs initSM initPM
    (ordinary2Rel_of_gather2Rel hResidual)
    (ordinary2Rel_of_gather2Rel hExpert)
    (ordinary2Rel_of_gather2Rel hGate) hDown
  exact gather2Rel_of_ordinary2Rel hBoundary (by decide)

#print axioms l12_ordinary_moe_composition

end
end TrainVerify.Denote.GeneratedPatterns
