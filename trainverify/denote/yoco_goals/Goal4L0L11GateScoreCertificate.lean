/- Goal 4 L0--L11: external gate-score certificate via scoped Goal-1 transport. -/
import denote.yoco_goals.Goal4EarlyScopedBridge
import denote.yoco_goals.Goal4FaithfulRoutingStack
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

/-- The twelve early ordinary gate-score relations on the exact Goal-4 graphs. -/
structure Goal4L0L11GateScoreCertificate (initSM initPM : Store) : Prop where
  l0 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 4965)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 7846)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 7847) [4096, 64] [2048, 64]
  l1 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5020)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8010)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8011) [4096, 64] [2048, 64]
  l2 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5075)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8174)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8175) [4096, 64] [2048, 64]
  l3 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5130)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8338)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8339) [4096, 64] [2048, 64]
  l4 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5185)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8502)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8503) [4096, 64] [2048, 64]
  l5 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5240)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8666)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8667) [4096, 64] [2048, 64]
  l6 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5295)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8830)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8831) [4096, 64] [2048, 64]
  l7 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5350)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8994)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8995) [4096, 64] [2048, 64]
  l8 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5405)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9158)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9159) [4096, 64] [2048, 64]
  l9 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5460)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9322)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9323) [4096, 64] [2048, 64]
  l10 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5515)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9486)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9487) [4096, 64] [2048, 64]
  l11 : Ordinary2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5570)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9650)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9651) [4096, 64] [2048, 64]

/-- Every Goal-1 SM init shape is certified by a generated init goal. -/
private theorem goal4_goal1_sm_shape_coverage : ∀ p ∈ sm_goal_1InitShapes,
    ∃ g ∈ goal_4_full_initGoals, g.ts = p.1 ∧ g.tsShape = p.2 := by
  native_decide

/-- Every Goal-1 PM init shape occurs at its matching finite index in a generated init goal. -/
private theorem goal4_goal1_pm_shape_coverage : ∀ p ∈ pm_goal_1InitShapes,
    ∃ g ∈ goal_4_full_initGoals, ∃ i,
      ∃ hi : i < g.tps.length, ∃ hj : i < g.tpShapes.length,
      (g.tps[i]'hi).tid = p.1 ∧ g.tpShapes[i]'hj = p.2 := by
  native_decide

private theorem goal4_goal1_sm_shapes_of_init (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM) :
    StoreShapesHold initSM sm_goal_1InitEnv := by
  intro tid sh hlookup
  unfold sm_goal_1InitEnv at hlookup
  have hmem : (tid, sh) ∈ sm_goal_1InitShapes :=
    shapeEnvOfList_mem_of_eq_some hlookup
  rcases goal4_goal1_sm_shape_coverage (tid, sh) hmem with ⟨g, hg, htid, hsh⟩
  have hh := hInit g hg
  unfold InitGoalHolds at hh
  simpa only [htid, hsh] using hh.1

private theorem goal4_goal1_pm_shapes_of_init (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM) :
    StoreShapesHold initPM pm_goal_1InitEnv := by
  intro tid sh hlookup
  unfold pm_goal_1InitEnv at hlookup
  have hmem : (tid, sh) ∈ pm_goal_1InitShapes :=
    shapeEnvOfList_mem_of_eq_some hlookup
  rcases goal4_goal1_pm_shape_coverage (tid, sh) hmem with
    ⟨g, hg, i, hi, hj, htid, hsh⟩
  have hh := hInit g hg
  unfold InitGoalHolds at hh
  have halign := congrArg (fun xs : List Shape => xs.getD i []) hh.2.1
  simp only [List.map_map, List.getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.map, Option.getD, Function.comp_apply, htid, hsh] at halign
  exact halign

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

/-- Closed L0--L11 gate-score certificate.  Computed relations are derived from
Goal 4 shape/init premises and transported only at the audited early TIDs. -/
theorem goal4_l0_l11_gate_score_certificate
    (initSM initPM : Store)
    (_hSM : StoreShapesHold initSM sm_goal_4InitEnv)
    (_hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (_hContract : Goal4ExternalInputContract initSM initPM) :
    Goal4L0L11GateScoreCertificate initSM initPM := by
  have hSM1 : StoreShapesHold initSM sm_goal_1InitEnv :=
    goal4_goal1_sm_shapes_of_init initSM initPM hInit
  have hPM1 : StoreShapesHold initPM pm_goal_1InitEnv :=
    goal4_goal1_pm_shapes_of_init initSM initPM hInit
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := by
    exact hInit
  have hA0 := canonical_l0_residual4957_rel initSM initPM hSM1 hPM1 hInit1
  have hN0 := l0_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA0
  have hX0 := l0_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN0
  have hL0 := goal1_external_l0_faithful_composition initSM initPM hSM1 hPM1 hInit1
  have hA1 := l1o_residual5012_rel_from_boundary4990 initSM initPM hInit1 hL0
  have hN1 := l1_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA1
  have hX1 := l1_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN1
  have hL1 := l1_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL0
  have hA2 := l2o_residual5067_rel_from_boundary5045 initSM initPM hInit1 hL1
  have hN2 := l2_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA2
  have hX2 := l2_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN2
  have hL2 := l2_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL1
  have hA3 := l3o_residual5122_rel_from_boundary5100 initSM initPM hInit1 hL2
  have hN3 := l3_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA3
  have hX3 := l3_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN3
  have hL3 := l3_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL2
  have hA4 := l4o_residual5177_rel_from_boundary5155 initSM initPM hInit1 hL3
  have hN4 := l4_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA4
  have hX4 := l4_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN4
  have hL4 := l4_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL3
  have hA5 := l5o_residual5232_rel_from_boundary5210 initSM initPM hInit1 hL4
  have hN5 := l5_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA5
  have hX5 := l5_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN5
  have hL5 := l5_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL4
  have hA6 := l6o_residual5287_rel_from_boundary5265 initSM initPM hInit1 hL5
  have hN6 := l6_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA6
  have hX6 := l6_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN6
  have hL6 := l6_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL5
  have hA7 := l7o_residual5342_rel_from_boundary5320 initSM initPM hInit1 hL6
  have hN7 := l7_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA7
  have hX7 := l7_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN7
  have hL7 := l7_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL6
  have hA8 := l8o_residual5397_rel_from_boundary5375 initSM initPM hInit1 hL7
  have hN8 := l8_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA8
  have hX8 := l8_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN8
  have hL8 := l8_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL7
  have hA9 := l9o_residual5452_rel_from_boundary5430 initSM initPM hInit1 hL8
  have hN9 := l9_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA9
  have hX9 := l9_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN9
  have hL9 := l9_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL8
  have hV10 := l10o_v5493_rel_from_boundary initSM initPM hInit1 hL9
  have hQK10 := l10o_q5495_k5496_rels_from_boundary initSM initPM hInit1 hL9
  have hA10 := l10o_residual5507_rel_from_boundary5485_of_qkv
    initSM initPM hInit1 hL9 hQK10.1 hQK10.2 hV10
  have hN10 := l10_ordinary_moe_norm_from_attention_output initSM initPM hInit1 hA10
  have hX10 := l10_ordinary_moe_logits_from_norm_input initSM initPM hPM1 hInit1 hN10
  have hL10 := l10_ordinary_faithful_composition initSM initPM hSM1 hPM1 hInit1 hL9
  have hA11 := l11o_residual5562_rel_from_boundary5540 initSM initPM hInit1 hL10
  have hN11 := canonical_kv_cache_ordinary_norm_from_attention_output
    initSM initPM hInit1 hA11
  have hX11 := canonical_kv_cache_ordinary_logits_from_norm_input
    initSM initPM hPM1 hInit1 hN11
  have hG0 := ordinary_of_gather_transport hX0
    (goal4_early_sm_to_goal1 initSM 4962 (by decide))
    (goal4_early_pm_to_goal1 initPM 7840 (by decide))
    (goal4_early_pm_to_goal1 initPM 7841 (by decide))
  have hG1 := ordinary_of_gather_transport hX1
    (goal4_early_sm_to_goal1 initSM 5017 (by decide))
    (goal4_early_pm_to_goal1 initPM 8004 (by decide))
    (goal4_early_pm_to_goal1 initPM 8005 (by decide))
  have hG2 := ordinary_of_gather_transport hX2
    (goal4_early_sm_to_goal1 initSM 5072 (by decide))
    (goal4_early_pm_to_goal1 initPM 8168 (by decide))
    (goal4_early_pm_to_goal1 initPM 8169 (by decide))
  have hG3 := ordinary_of_gather_transport hX3
    (goal4_early_sm_to_goal1 initSM 5127 (by decide))
    (goal4_early_pm_to_goal1 initPM 8332 (by decide))
    (goal4_early_pm_to_goal1 initPM 8333 (by decide))
  have hG4 := ordinary_of_gather_transport hX4
    (goal4_early_sm_to_goal1 initSM 5182 (by decide))
    (goal4_early_pm_to_goal1 initPM 8496 (by decide))
    (goal4_early_pm_to_goal1 initPM 8497 (by decide))
  have hG5 := ordinary_of_gather_transport hX5
    (goal4_early_sm_to_goal1 initSM 5237 (by decide))
    (goal4_early_pm_to_goal1 initPM 8660 (by decide))
    (goal4_early_pm_to_goal1 initPM 8661 (by decide))
  have hG6 := ordinary_of_gather_transport hX6
    (goal4_early_sm_to_goal1 initSM 5292 (by decide))
    (goal4_early_pm_to_goal1 initPM 8824 (by decide))
    (goal4_early_pm_to_goal1 initPM 8825 (by decide))
  have hG7 := ordinary_of_gather_transport hX7
    (goal4_early_sm_to_goal1 initSM 5347 (by decide))
    (goal4_early_pm_to_goal1 initPM 8988 (by decide))
    (goal4_early_pm_to_goal1 initPM 8989 (by decide))
  have hG8 := ordinary_of_gather_transport hX8
    (goal4_early_sm_to_goal1 initSM 5402 (by decide))
    (goal4_early_pm_to_goal1 initPM 9152 (by decide))
    (goal4_early_pm_to_goal1 initPM 9153 (by decide))
  have hG9 := ordinary_of_gather_transport hX9
    (goal4_early_sm_to_goal1 initSM 5457 (by decide))
    (goal4_early_pm_to_goal1 initPM 9316 (by decide))
    (goal4_early_pm_to_goal1 initPM 9317 (by decide))
  have hG10 := ordinary_of_gather_transport hX10
    (goal4_early_sm_to_goal1 initSM 5512 (by decide))
    (goal4_early_pm_to_goal1 initPM 9480 (by decide))
    (goal4_early_pm_to_goal1 initPM 9481 (by decide))
  have hG11 := ordinary_of_gather_transport hX11
    (goal4_early_sm_to_goal1 initSM 5567 (by decide))
    (goal4_early_pm_to_goal1 initPM 9644 (by decide))
    (goal4_early_pm_to_goal1 initPM 9645 (by decide))
  exact {
    l0 := canonical_goal4_l0_gate_scores initSM initPM hG0
    l1 := canonical_goal4_l1_gate_scores initSM initPM hG1
    l2 := canonical_goal4_l2_gate_scores initSM initPM hG2
    l3 := canonical_goal4_l3_gate_scores initSM initPM hG3
    l4 := canonical_goal4_l4_gate_scores initSM initPM hG4
    l5 := canonical_goal4_l5_gate_scores initSM initPM hG5
    l6 := canonical_goal4_l6_gate_scores initSM initPM hG6
    l7 := canonical_goal4_l7_gate_scores initSM initPM hG7
    l8 := canonical_goal4_l8_gate_scores initSM initPM hG8
    l9 := canonical_goal4_l9_gate_scores initSM initPM hG9
    l10 := canonical_goal4_l10_gate_scores initSM initPM hG10
    l11 := canonical_goal4_l11_gate_scores initSM initPM hG11
  }

#print axioms goal4_l0_l11_gate_score_certificate

end
end TrainVerify.Denote.GeneratedPatterns
