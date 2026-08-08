/- Canonical Goal 1, layer 23: complete faithful composition through the loss backbone. -/
import denote.yoco_goals.CanonicalL23Norm
import denote.yoco_goals.CanonicalL23Router
import denote.yoco_goals.CanonicalL23GateDown
import denote.yoco_goals.CanonicalL23Down
import denote.yoco_goals.CanonicalL23Expert
import denote.yoco_goals.CanonicalL23Join
import denote.yoco_goals.CanonicalL23Residual
import denote.yoco_goals.CanonicalL23Output
import denote.yoco_goals.CanonicalLossBackboneTail
import denote.yoco_goals.Goal_1_FaithfulHead

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private theorem cL23c_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

/-- The L22 projection weight is an external initialized tensor.  Its denotation
identity is derived here from `hInit`, rather than exposed as a caller premise. -/
private theorem cL23c_weight6210_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210 := by
  have hi := (hInit initGoal_6210 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6210 pm_goal_1.numRanks _ rfl,
    show initGoal_6210.tps = [{rank := 0, tid := 6210}] from rfl,
    show initGoal_6210.ts = 6210 from rfl,
    show initGoal_6210.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  rw [cL23c_leaf sm_goal_1 initSM 6210 (by native_decide) (by native_decide),
    cL23c_leaf pm_goal_1 initPM 6210 (by native_decide) (by native_decide)]
  exact hi

private theorem cL23c_weight6210_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape = [1024, 1024] := by
  rw [cL23c_leaf pm_goal_1 initPM 6210 (by native_decide) (by native_decide)]
  exact hPM 6210 [1024, 1024] (by native_decide)

/-- Complete canonical Goal-1 L23 faithful chain.  The only lineage premises are
the two internal L22 boundary relations.  All L22/L23 computed intermediates,
including the projection-weight denotation facts, are derived inside the module. -/
theorem canonical_l23_composition_to_gather (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hPMCanonical : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16442)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11713)
      [4096, 1024] [2048, 1024] := by
  have hwEq := cL23c_weight6210_eq initSM initPM hInit
  have hwShape := cL23c_weight6210_shape initPM hPM
  have hLayer22 := canonical_l22_output_from_inputs initSM initPM
    hResidual hAttention hwEq hwShape
  have hNorm := canonical_l23_norm_from_l22_inputs initSM initPM hInit
    hResidual hAttention hwEq hwShape
  have hActivation := canonical_l23_activation_from_l22_inputs initSM initPM hInit
    hResidual hAttention hwEq hwShape
  have hRouter := canonical_l23_router_from_norm_input initSM initPM
    hPMCanonical hInit hNorm
  have hGate := canonical_l23_gate_from_norm_input initSM initPM hPMCanonical hInit hNorm
  have hDown := canonical_l23_down_from_norm_input initSM initPM hPMCanonical hInit hNorm
  have hExpert := canonical_l23_expert_from_branch_inputs initSM initPM
    hSM hPM hInit hActivation hRouter.1 hRouter.2
  have hJoin := canonical_l23_join_from_branch_inputs initSM initPM hExpert hGate hDown
  have hResidual23 := canonical_l23_residual_from_layer22_output initSM initPM hLayer22
  have hOutput := canonical_l23_output_from_join_inputs initSM initPM hResidual23 hJoin
  exact canonical_loss_backbone_tail initSM initPM hInit hOutput hPacked

/-- Goal 1 head layered over the complete L23 composition.  The label bound is
the head's genuine external well-formed-input condition. -/
theorem canonical_goal_1_from_l22_boundaries (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hPMCanonical : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hResidual : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16442)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hlabels : ∀ l < 4096, scalarToNat (valAt (initPM 4931) l) < 154880) :
    InitGoalHolds pm_goal_1.numRanks goal_1
      (denoteGraphDistributedFaithful sm_goal_1 initSM)
      (denoteGraphDistributedFaithful pm_goal_1 initPM) := by
  have hGather := canonical_l23_composition_to_gather initSM initPM hSM hPM
    hPMCanonical hInit hPacked hResidual hAttention
  exact canonical_goal_1_from_norm initSM initPM hPM hInit hGather hlabels

end
end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.canonical_l23_composition_to_gather
#print axioms TrainVerify.Denote.GeneratedPatterns.canonical_goal_1_from_l22_boundaries
