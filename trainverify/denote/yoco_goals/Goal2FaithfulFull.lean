/- Goal 2: full faithful external-input ancestry. -/
import denote.yoco_goals.Goal1ExternalToL18Composition
import denote.yoco_goals.CanonicalL19ShardedKVAttention
import denote.yoco_goals.L19ZigzagMoEComposition
import denote.yoco_goals.CanonicalL20ShardedKVAttention
import denote.yoco_goals.CanonicalL21Composition
import denote.yoco_goals.CanonicalL22AttentionComposition
import denote.yoco_goals.CanonicalL22KAlignment
import denote.yoco_goals.CanonicalL22VAlignment
import denote.yoco_goals.CanonicalL22Residual
import denote.yoco_goals.CanonicalL23Norm
import denote.yoco_goals.CanonicalL23Router
import denote.yoco_goals.CanonicalL23GateDown
import denote.yoco_goals.CanonicalL23Down
import denote.yoco_goals.CanonicalL23Expert
import denote.yoco_goals.CanonicalL23Join
import denote.yoco_goals.CanonicalL23Residual
import denote.yoco_goals.CanonicalL23Output
import denote.yoco_goals.CanonicalLossBackboneTailGoal2

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

private def goal2BridgeTids : List Tid := [11598, 11599, 6252]

private theorem goal2_pm_prefix_facts :
    pm_goal_1.numRanks = pm_goal_2.numRanks ∧
    pm_goal_1.nodes.take 2016 = pm_goal_2.nodes.take 2016 ∧
    (∀ n ∈ pm_goal_1.nodes.take 2016,
      pm_goal_1.replicaBuddies n = pm_goal_2.replicaBuddies n) ∧
    (∀ tid ∈ goal2BridgeTids,
      (∀ n ∈ pm_goal_1.nodes.drop 2016, n.outs ≠ []) ∧
      (∀ n ∈ pm_goal_1.nodes.drop 2016, tid ∉ n.outs) ∧
      (∀ n ∈ pm_goal_2.nodes.drop 2016, n.outs ≠ []) ∧
      (∀ n ∈ pm_goal_2.nodes.drop 2016, tid ∉ n.outs)) := by
  native_decide

private theorem goal2_pm_step_eq (s : Store) (n : NodeDecl)
    (hn : n ∈ pm_goal_1.nodes.take 2016) :
    applyNodeDistributedFaithful pm_goal_1 s n =
      applyNodeDistributedFaithful pm_goal_2 s n := by
  have hranks := goal2_pm_prefix_facts.1
  have hbuddies := goal2_pm_prefix_facts.2.2.1 n hn
  unfold applyNodeDistributedFaithful
  by_cases hshuffle : n.op = "OpName.FW_maybe_shuffle"
  · rw [if_pos hshuffle, if_pos hshuffle]
    unfold applyNodeFaithfulShuffleValue
    rw [hbuddies]
  · rw [if_neg hshuffle, if_neg hshuffle]
    by_cases hunshuffle : n.op = "OpName.FW_maybe_unshuffle"
    · rw [if_pos hunshuffle, if_pos hunshuffle]
      unfold applyNodeFaithfulUnshuffleValue
      rw [hbuddies]
    · rw [if_neg hunshuffle, if_neg hunshuffle]
      by_cases hattn : n.op = "OpName.FW_attn_zigzag"
      · rw [if_pos hattn, if_pos hattn]
        unfold applyNodeFaithfulZigzagAttnValue zigzagAttnUsesReplicatedKV
        rw [hbuddies, hranks]
      · rw [if_neg hattn, if_neg hattn]
        unfold applyNodeDistributed
        by_cases hmoe : n.op = "OpName.FW_all2all_moe_gmm"
        · rw [if_pos hmoe, if_pos hmoe]
          unfold applyNodeFullExpertMoE_value
          rw [hbuddies]
        · rw [if_neg hmoe, if_neg hmoe]
          unfold applyNodeRingAttn
          rw [if_neg hattn, if_neg hattn]
          by_cases hwindow : n.op = "OpName.FW_attn_sliding_window"
          · rw [if_pos hwindow, if_pos hwindow]
            unfold applyNodeRingAttn_sliding_window ringAttnBuddies
            rw [hbuddies]
          · rw [if_neg hwindow, if_neg hwindow]
            rw [applyNode_congr_numRanks pm_goal_1 pm_goal_2 hranks]

private theorem goal2_foldl_eq_of_steps
    (f g : Store → NodeDecl → Store) (nodes : List NodeDecl) (init : Store)
    (hstep : ∀ n ∈ nodes, ∀ s, f s n = g s n) :
    nodes.foldl f init = nodes.foldl g init := by
  induction nodes generalizing init with
  | nil => rfl
  | cons n rest ih =>
      rw [List.foldl_cons, List.foldl_cons, hstep n List.mem_cons_self init]
      apply ih
      intro m hm s
      exact hstep m (List.mem_cons_of_mem n hm) s

private theorem goal2_pm_prefix_fold_eq (init : Store) :
    (pm_goal_1.nodes.take 2016).foldl
        (applyNodeDistributedFaithful pm_goal_1) init =
      (pm_goal_2.nodes.take 2016).foldl
        (applyNodeDistributedFaithful pm_goal_2) init := by
  have hnodes := goal2_pm_prefix_facts.2.1
  rw [← hnodes]
  let pre := pm_goal_1.nodes.take 2016
  apply goal2_foldl_eq_of_steps
  intro n hn s
  exact goal2_pm_step_eq s n hn

/-- Goal-1 and Goal-2 full faithful PM graphs agree at the complete L23 zigzag
boundary.  This is an audited prefix transport: the graphs share all 2016
producing nodes and all graph-sensitive buddy metadata; only the later CE gather
differs. -/
theorem goal1_goal2_pm_l23_boundary (init : Store) (tid : Tid)
    (htid : tid ∈ goal2BridgeTids) :
    denoteGraphDistributedFaithful pm_goal_1 init tid =
      denoteGraphDistributedFaithful pm_goal_2 init tid := by
  rcases goal2_pm_prefix_facts.2.2.2 tid htid with
    ⟨g1nil, g1write, g2nil, g2write⟩
  rw [denoteGraphDistributedFaithful_eq_prefix pm_goal_1 init tid 2016 g1nil g1write,
    denoteGraphDistributedFaithful_eq_prefix pm_goal_2 init tid 2016 g2nil g2write,
    goal2_pm_prefix_fold_eq init]

private theorem goal2_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem goal2_weight6210_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210 := by
  have hi := (hInit initGoal_6210 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6210 pm_goal_1.numRanks _ rfl,
    show initGoal_6210.tps = [{rank := 0, tid := 6210}] from rfl,
    show initGoal_6210.ts = 6210 from rfl,
    show initGoal_6210.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  rw [goal2_leaf sm_goal_1 initSM 6210 (by native_decide) (by native_decide),
    goal2_leaf pm_goal_1 initPM 6210 (by native_decide) (by native_decide)]
  exact hi

private theorem goal2_weight6210_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape = [1024, 1024] := by
  rw [goal2_leaf pm_goal_1 initPM 6210 (by native_decide) (by native_decide)]
  exact hPM 6210 [1024, 1024] (by native_decide)

/-- The complete external-input ancestry to the computed Goal-1 L23 zigzag
boundary.  It is used only through the exact Goal-1/Goal-2 graph-prefix bridge. -/
private theorem goal1_external_to_l23_zigzag
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1ExternalInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hL18 := goal1_external_to_l18_output initSM initPM hSM hPM hInit hContract
  have hCache := goal1_external_to_cache_faithful_composition initSM initPM hSM hPM hInit
  have hpm6096 : denoteGraphDistributedFaithful pm_goal_1 initPM 6096 = initPM 6096 := by
    exact goal2_leaf pm_goal_1 initPM 6096 (by native_decide) (by native_decide)
  have hpm6150 : denoteGraphDistributedFaithful pm_goal_1 initPM 6150 = initPM 6150 := by
    exact goal2_leaf pm_goal_1 initPM 6150 (by native_decide) (by native_decide)
  have hpm6252 : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    exact goal2_leaf pm_goal_1 initPM 6252 (by native_decide) (by native_decide)
  have h6096Init : initPM 6096 = initPM 6252 :=
    hContract.2.1.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have h6150Init : initPM 6150 = initPM 6252 :=
    hContract.2.1.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias19 : denoteGraphDistributedFaithful pm_goal_1 initPM 6096 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm6096, hpm6252, h6096Init]
  have hCuAlias20 : denoteGraphDistributedFaithful pm_goal_1 initPM 6150 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm6150, hpm6252, h6150Init]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hpm6252]
    exact hContract.2.2.1.decoded_single
  have hL19Attention := canonical_l19_attention_residual_from_incoming_and_cache
    initSM initPM hPM hInit hL18 hCache hCuAlias19 hDecoded
  have hL19 := l19_zigzag_moe_output_from_attention_output
    initSM initPM hSM hPM hInit hL19Attention
  have hL20 := canonical_l20_output_from_l19_and_cache
    initSM initPM hPM hInit hL19 hCache hCuAlias20 hDecoded
  have hL21 := canonical_l21_output_from_layer20_output
    initSM initPM hSM hPM hInit hL20
  have hQ := canonical_l22_q_relation_from_l21 initSM initPM hPM hInit hL21
  have hK := canonical_l22_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l22_v_ordinary_relation initSM initPM hPM hInit hCache
  have hAttention := canonical_l22_attention_from_qkv initSM initPM hInit
    hContract.2.1 hContract.2.2.1 hQ hK hV
  have hResidual := canonical_l22_residual_from_layer21_output initSM initPM hL21
  have hwEq := goal2_weight6210_eq initSM initPM hInit
  have hwShape := goal2_weight6210_shape initPM hPM
  have hLayer22 := canonical_l22_output_from_inputs initSM initPM hResidual hAttention hwEq hwShape
  have hNorm := canonical_l23_norm_from_l22_inputs initSM initPM hInit
    hResidual hAttention hwEq hwShape
  have hActivation := canonical_l23_activation_from_l22_inputs initSM initPM hInit
    hResidual hAttention hwEq hwShape
  have hRouter := canonical_l23_router_from_norm_input initSM initPM hPM hInit hNorm
  have hGate := canonical_l23_gate_from_norm_input initSM initPM hPM hInit hNorm
  have hDown := canonical_l23_down_from_norm_input initSM initPM hPM hInit hNorm
  have hExpert := canonical_l23_expert_from_branch_inputs initSM initPM
    hSM hPM hInit hActivation hRouter.1 hRouter.2
  have hJoin := canonical_l23_join_from_branch_inputs initSM initPM hExpert hGate hDown
  have hResidual23 := canonical_l23_residual_from_layer22_output initSM initPM hLayer22
  exact canonical_l23_output_from_join_inputs initSM initPM hResidual23 hJoin

/-- Goal 2's computed L23 zigzag relation, derived solely from external shape/init
facts and `Goal2ExternalInputContract`.  No computed relation is a caller premise. -/
theorem goal2_external_to_l23_zigzag
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_2InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_2InitEnv)
    (hInit : InitGoalsHold pm_goal_2.numRanks goal_2_full_initGoals initSM initPM)
    (hContract : Goal2ExternalInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hpre := goal1_external_to_l23_zigzag initSM initPM hSM hPM hInit hContract
  rw [← goal1_goal2_pm_l23_boundary initPM 11598 (by decide),
    ← goal1_goal2_pm_l23_boundary initPM 11599 (by decide),
    ← goal1_goal2_pm_l23_boundary initPM 6252 (by decide)]
  exact hpre

/-- The generated Goal-2 full faithful statement, with the computed L23 boundary
reconstructed internally from the independent external contract. -/
theorem canonical_goal_2_external : goal_2_stmt_full := by
  unfold goal_2_stmt_full
  unfold CoarseLineageHoldsWithInitDistributedFaithfulWithContract
  intro initSM initPM hSM hPM hInit hContract
  have hpre := goal2_external_to_l23_zigzag initSM initPM hSM hPM hInit hContract
  exact canonical_goal_2_from_zigzag initSM initPM hPM hInit hpre hContract.2.2.1

#print axioms goal1_goal2_pm_l23_boundary
#print axioms goal2_external_to_l23_zigzag
#print axioms canonical_goal_2_external

end
end TrainVerify.Denote.GeneratedPatterns
