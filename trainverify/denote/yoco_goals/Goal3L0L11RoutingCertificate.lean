/- Goal 3: L0--L11 ordinary routing-map membership certificate. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.CanonicalGoal1ExternalL0Composition
import denote.yoco_goals.Goal1L1L11CacheComposition

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

/-- Public spelling used by Goal 3 stack assembly. -/
abbrev Goal3ExternalInputContract := Goal3FullExternalInputs

private def goal3EarlySmRoutingTids : List Tid :=
  [4964, 5019, 5074, 5129, 5184, 5239, 5294, 5349, 5404, 5459, 5514, 5569]

private def goal3EarlyPmRouting0Tids : List Tid :=
  [7844, 8008, 8172, 8336, 8500, 8664, 8828, 8992, 9156, 9320, 9484, 9648]

private def goal3EarlyPmRouting1Tids : List Tid :=
  [7845, 8009, 8173, 8337, 8501, 8665, 8829, 8993, 9157, 9321, 9485, 9649]

/-- The twelve ordinary pre-shuffle routing-map members consumed by Goal 3's
24-layer stack.  Each field is stated on the ancestry-closed generated graph. -/
structure Goal3L0L11RoutingCertificate (initSM initPM : Store) : Prop where
  l0 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 4964)
    (denoteGraphDistributedFaithful pm initPM 7844)
    (denoteGraphDistributedFaithful pm initPM 7845) [4096, 64] [2048, 64]
  l1 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5019)
    (denoteGraphDistributedFaithful pm initPM 8008)
    (denoteGraphDistributedFaithful pm initPM 8009) [4096, 64] [2048, 64]
  l2 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5074)
    (denoteGraphDistributedFaithful pm initPM 8172)
    (denoteGraphDistributedFaithful pm initPM 8173) [4096, 64] [2048, 64]
  l3 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5129)
    (denoteGraphDistributedFaithful pm initPM 8336)
    (denoteGraphDistributedFaithful pm initPM 8337) [4096, 64] [2048, 64]
  l4 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5184)
    (denoteGraphDistributedFaithful pm initPM 8500)
    (denoteGraphDistributedFaithful pm initPM 8501) [4096, 64] [2048, 64]
  l5 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5239)
    (denoteGraphDistributedFaithful pm initPM 8664)
    (denoteGraphDistributedFaithful pm initPM 8665) [4096, 64] [2048, 64]
  l6 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5294)
    (denoteGraphDistributedFaithful pm initPM 8828)
    (denoteGraphDistributedFaithful pm initPM 8829) [4096, 64] [2048, 64]
  l7 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5349)
    (denoteGraphDistributedFaithful pm initPM 8992)
    (denoteGraphDistributedFaithful pm initPM 8993) [4096, 64] [2048, 64]
  l8 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5404)
    (denoteGraphDistributedFaithful pm initPM 9156)
    (denoteGraphDistributedFaithful pm initPM 9157) [4096, 64] [2048, 64]
  l9 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5459)
    (denoteGraphDistributedFaithful pm initPM 9320)
    (denoteGraphDistributedFaithful pm initPM 9321) [4096, 64] [2048, 64]
  l10 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5514)
    (denoteGraphDistributedFaithful pm initPM 9484)
    (denoteGraphDistributedFaithful pm initPM 9485) [4096, 64] [2048, 64]
  l11 : Ordinary2Rel (denoteGraphDistributedFaithful sm initSM 5569)
    (denoteGraphDistributedFaithful pm initPM 9648)
    (denoteGraphDistributedFaithful pm initPM 9649) [4096, 64] [2048, 64]

private theorem goal3_early_prefix_facts :
    sm.numRanks = sm_goal_1.numRanks ∧
    sm.nodes.take 457 = sm_goal_1.nodes.take 457 ∧
    (∀ n ∈ sm.nodes.take 457, sm.replicaBuddies n = sm_goal_1.replicaBuddies n) ∧
    pm.numRanks = pm_goal_1.numRanks ∧
    pm.nodes.take 1025 = pm_goal_1.nodes.take 1025 ∧
    (∀ n ∈ pm.nodes.take 1025, pm.replicaBuddies n = pm_goal_1.replicaBuddies n) ∧
    (∀ tid ∈ goal3EarlySmRoutingTids,
      (∀ n ∈ sm.nodes.drop 457, n.outs ≠ []) ∧
      (∀ n ∈ sm.nodes.drop 457, tid ∉ n.outs) ∧
      (∀ n ∈ sm_goal_1.nodes.drop 457, n.outs ≠ []) ∧
      (∀ n ∈ sm_goal_1.nodes.drop 457, tid ∉ n.outs)) ∧
    (∀ tid ∈ goal3EarlyPmRouting0Tids ++ goal3EarlyPmRouting1Tids,
      (∀ n ∈ pm.nodes.drop 1025, n.outs ≠ []) ∧
      (∀ n ∈ pm.nodes.drop 1025, tid ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes.drop 1025, n.outs ≠ []) ∧
      (∀ n ∈ pm_goal_1.nodes.drop 1025, tid ∉ n.outs)) := by
  native_decide

private theorem goal3_faithful_step_eq (g h : GraphDecl) (s : Store) (n : NodeDecl)
    (hranks : g.numRanks = h.numRanks)
    (hbuddies : g.replicaBuddies n = h.replicaBuddies n) :
    applyNodeDistributedFaithful g s n = applyNodeDistributedFaithful h s n := by
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
            rw [applyNode_congr_numRanks g h hranks]

private theorem goal3_foldl_eq_of_steps
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

private theorem goal3_sm_prefix_fold_eq (init : Store) :
    (sm.nodes.take 457).foldl (applyNodeDistributedFaithful sm) init =
      (sm_goal_1.nodes.take 457).foldl
        (applyNodeDistributedFaithful sm_goal_1) init := by
  have hnodes := goal3_early_prefix_facts.2.1
  rw [← hnodes]
  apply goal3_foldl_eq_of_steps
  intro n hn s
  exact goal3_faithful_step_eq sm sm_goal_1 s n goal3_early_prefix_facts.1
    (goal3_early_prefix_facts.2.2.1 n hn)

private theorem goal3_pm_prefix_fold_eq (init : Store) :
    (pm.nodes.take 1025).foldl (applyNodeDistributedFaithful pm) init =
      (pm_goal_1.nodes.take 1025).foldl
        (applyNodeDistributedFaithful pm_goal_1) init := by
  have hnodes := goal3_early_prefix_facts.2.2.2.2.1
  rw [← hnodes]
  apply goal3_foldl_eq_of_steps
  intro n hn s
  exact goal3_faithful_step_eq pm pm_goal_1 s n goal3_early_prefix_facts.2.2.2.1
    (goal3_early_prefix_facts.2.2.2.2.2.1 n hn)

/-- Exact generated-full to Goal-1 transport for the twelve early SM routing
maps.  Only the audited common prefix and graph-sensitive metadata are used. -/
theorem goal3_early_sm_to_goal1 (init : Store) (tid : Tid)
    (htid : tid ∈ goal3EarlySmRoutingTids) :
    denoteGraphDistributedFaithful sm init tid =
      denoteGraphDistributedFaithful sm_goal_1 init tid := by
  rcases goal3_early_prefix_facts.2.2.2.2.2.2.1 tid htid with
    ⟨fnil, fwrite, gnil, gwrite⟩
  rw [denoteGraphDistributedFaithful_eq_prefix sm init tid 457 fnil fwrite,
    denoteGraphDistributedFaithful_eq_prefix sm_goal_1 init tid 457 gnil gwrite,
    goal3_sm_prefix_fold_eq init]

/-- Exact generated-full to Goal-1 transport for the twenty-four early PM
routing shards. -/
theorem goal3_early_pm_to_goal1 (init : Store) (tid : Tid)
    (htid : tid ∈ goal3EarlyPmRouting0Tids ++ goal3EarlyPmRouting1Tids) :
    denoteGraphDistributedFaithful pm init tid =
      denoteGraphDistributedFaithful pm_goal_1 init tid := by
  rcases goal3_early_prefix_facts.2.2.2.2.2.2.2 tid htid with
    ⟨fnil, fwrite, gnil, gwrite⟩
  rw [denoteGraphDistributedFaithful_eq_prefix pm init tid 1025 fnil fwrite,
    denoteGraphDistributedFaithful_eq_prefix pm_goal_1 init tid 1025 gnil gwrite,
    goal3_pm_prefix_fold_eq init]

private theorem ordinary_of_gather_transport
    {full full' rank0 rank0' rank1 rank1' : Tensor}
    {fullShape shardShape : Shape}
    (h : Gather2Rel full' rank0' rank1' fullShape shardShape)
    (hf : full = full') (h0 : rank0 = rank0') (h1 : rank1 = rank1') :
    Ordinary2Rel full rank0 rank1 fullShape shardShape := by
  rw [hf, h0, h1]
  exact {
    full_value := h.value
    full_shape := h.full_shape
    rank0_shape := h.shard0_shape
    rank1_shape := h.shard1_shape
  }

/-- Closed L0--L11 routing certificate for full Goal 3.  The hypotheses are
only independent external shape/init facts and the Goal-3 input contract; no
computed relation is supplied by the caller. -/
theorem goal3_l0_l11_routing_certificate
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (_hContract : Goal3ExternalInputContract initSM initPM) :
    Goal3L0L11RoutingCertificate initSM initPM := by
  have hSM1 : StoreShapesHold initSM sm_goal_1InitEnv := by
    apply storeShapesHold_weaken (small := sm_goal_1InitShapes) (big := smInitShapes)
    · native_decide
    · exact hSM
  have hPM1 : StoreShapesHold initPM pm_goal_1InitEnv := by
    apply storeShapesHold_weaken (small := pm_goal_1InitShapes) (big := pmInitShapes)
    · native_decide
    · exact hPM
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := by
    exact hInit
  have hA0 := canonical_l0_residual4957_rel initSM initPM hSM1 hPM1 hInit1
  have hR0 := l0_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA0
  have hL0 := goal1_external_l0_faithful_composition initSM initPM hSM1 hPM1 hInit1
  have hA1 := l1o_residual5012_rel_from_boundary4990 initSM initPM hInit1 hL0
  have hR1 := l1_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA1
  have hL1 := l1_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL0
  have hA2 := l2o_residual5067_rel_from_boundary5045 initSM initPM hInit1 hL1
  have hR2 := l2_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA2
  have hL2 := l2_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL1
  have hA3 := l3o_residual5122_rel_from_boundary5100 initSM initPM hInit1 hL2
  have hR3 := l3_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA3
  have hL3 := l3_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL2
  have hA4 := l4o_residual5177_rel_from_boundary5155 initSM initPM hInit1 hL3
  have hR4 := l4_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA4
  have hL4 := l4_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL3
  have hA5 := l5o_residual5232_rel_from_boundary5210 initSM initPM hInit1 hL4
  have hR5 := l5_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA5
  have hL5 := l5_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL4
  have hA6 := l6o_residual5287_rel_from_boundary5265 initSM initPM hInit1 hL5
  have hR6 := l6_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA6
  have hL6 := l6_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL5
  have hA7 := l7o_residual5342_rel_from_boundary5320 initSM initPM hInit1 hL6
  have hR7 := l7_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA7
  have hL7 := l7_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL6
  have hA8 := l8o_residual5397_rel_from_boundary5375 initSM initPM hInit1 hL7
  have hR8 := l8_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA8
  have hL8 := l8_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL7
  have hA9 := l9o_residual5452_rel_from_boundary5430 initSM initPM hInit1 hL8
  have hR9 := l9_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA9
  have hL9 := l9_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL8
  have hV10 := l10o_v5493_rel_from_boundary initSM initPM hInit1 hL9
  have hQK10 := l10o_q5495_k5496_rels_from_boundary initSM initPM hInit1 hL9
  have hA10 := l10o_residual5507_rel_from_boundary5485_of_qkv
    initSM initPM hInit1 hL9 hQK10.1 hQK10.2 hV10
  have hR10 := l10_ordinary_moe_router_from_attention_output initSM initPM hPM1 hInit1 hA10
  have hL10 := l10_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL9
  have hA11 := l11o_residual5562_rel_from_boundary5540 initSM initPM hInit1 hL10
  have hR11 := canonical_kv_cache_ordinary_router_from_attention_output
    initSM initPM hPM1 hInit1 hA11
  refine {
    l0 := ordinary_of_gather_transport hR0.2
      (goal3_early_sm_to_goal1 initSM 4964 (by decide))
      (goal3_early_pm_to_goal1 initPM 7844 (by decide))
      (goal3_early_pm_to_goal1 initPM 7845 (by decide))
    l1 := ordinary_of_gather_transport hR1.2
      (goal3_early_sm_to_goal1 initSM 5019 (by decide))
      (goal3_early_pm_to_goal1 initPM 8008 (by decide))
      (goal3_early_pm_to_goal1 initPM 8009 (by decide))
    l2 := ordinary_of_gather_transport hR2.2
      (goal3_early_sm_to_goal1 initSM 5074 (by decide))
      (goal3_early_pm_to_goal1 initPM 8172 (by decide))
      (goal3_early_pm_to_goal1 initPM 8173 (by decide))
    l3 := ordinary_of_gather_transport hR3.2
      (goal3_early_sm_to_goal1 initSM 5129 (by decide))
      (goal3_early_pm_to_goal1 initPM 8336 (by decide))
      (goal3_early_pm_to_goal1 initPM 8337 (by decide))
    l4 := ordinary_of_gather_transport hR4.2
      (goal3_early_sm_to_goal1 initSM 5184 (by decide))
      (goal3_early_pm_to_goal1 initPM 8500 (by decide))
      (goal3_early_pm_to_goal1 initPM 8501 (by decide))
    l5 := ordinary_of_gather_transport hR5.2
      (goal3_early_sm_to_goal1 initSM 5239 (by decide))
      (goal3_early_pm_to_goal1 initPM 8664 (by decide))
      (goal3_early_pm_to_goal1 initPM 8665 (by decide))
    l6 := ordinary_of_gather_transport hR6.2
      (goal3_early_sm_to_goal1 initSM 5294 (by decide))
      (goal3_early_pm_to_goal1 initPM 8828 (by decide))
      (goal3_early_pm_to_goal1 initPM 8829 (by decide))
    l7 := ordinary_of_gather_transport hR7.2
      (goal3_early_sm_to_goal1 initSM 5349 (by decide))
      (goal3_early_pm_to_goal1 initPM 8992 (by decide))
      (goal3_early_pm_to_goal1 initPM 8993 (by decide))
    l8 := ordinary_of_gather_transport hR8.2
      (goal3_early_sm_to_goal1 initSM 5404 (by decide))
      (goal3_early_pm_to_goal1 initPM 9156 (by decide))
      (goal3_early_pm_to_goal1 initPM 9157 (by decide))
    l9 := ordinary_of_gather_transport hR9.2
      (goal3_early_sm_to_goal1 initSM 5459 (by decide))
      (goal3_early_pm_to_goal1 initPM 9320 (by decide))
      (goal3_early_pm_to_goal1 initPM 9321 (by decide))
    l10 := ordinary_of_gather_transport hR10.2
      (goal3_early_sm_to_goal1 initSM 5514 (by decide))
      (goal3_early_pm_to_goal1 initPM 9484 (by decide))
      (goal3_early_pm_to_goal1 initPM 9485 (by decide))
    l11 := ordinary_of_gather_transport hR11.2
      (goal3_early_sm_to_goal1 initSM 5569 (by decide))
      (goal3_early_pm_to_goal1 initPM 9648 (by decide))
      (goal3_early_pm_to_goal1 initPM 9649 (by decide))
  }

end
end TrainVerify.Denote.GeneratedPatterns
