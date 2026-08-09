/- Goal 4 L0--L11: scoped transport across Goal 1's two label chunks. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.Goal_4
import denote.GraphGears

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

/-- Goal 1 alone chunks label TID 4931 into these two dead-for-L0--L11 TIDs. -/
def goal4EarlyExcludedTids : List Tid := [11714, 11715]

/-- Equality on the observable early scope, deliberately ignoring Goal 1's two
label-chunk temporaries. -/
def Goal4EarlyScopedEq (s t : Store) : Prop :=
  ∀ tid, tid ∉ goal4EarlyExcludedTids → s tid = t tid

private theorem storeSet_scoped_congr (s t : Store) (pairs : List (Tid × Tensor))
    (h : Goal4EarlyScopedEq s t) :
    Goal4EarlyScopedEq (storeSet s pairs) (storeSet t pairs) := by
  intro tid htid
  unfold storeSet
  cases hp : pairs.find? (fun p => decide (p.1 = tid)) with
  | none => exact h tid htid
  | some p => rfl

private theorem map_store_eq {xs : List Tid} {s t : Store}
    (h : Goal4EarlyScopedEq s t)
    (hxs : ∀ tid ∈ xs, tid ∉ goal4EarlyExcludedTids) : xs.map s = xs.map t := by
  apply List.map_congr_left
  intro tid htid
  exact h tid (hxs tid htid)

private theorem buddy_map_store_eq (g : GraphDecl) (n : NodeDecl) (s t : Store)
    (h : Goal4EarlyScopedEq s t)
    (idx : Nat)
    (hread : ∀ m ∈ g.replicaBuddies n,
      m.ins.getD idx 0 ∉ goal4EarlyExcludedTids) :
    (g.replicaBuddies n).map (fun m => s (m.ins.getD idx 0)) =
      (g.replicaBuddies n).map (fun m => t (m.ins.getD idx 0)) := by
  apply List.map_congr_left
  intro m hm
  exact h _ (hread m hm)

private theorem applyNode_scoped_congr (g : GraphDecl) (s t : Store) (n : NodeDecl)
    (h : Goal4EarlyScopedEq s t)
    (hins : ∀ tid ∈ n.ins, tid ∉ goal4EarlyExcludedTids) :
    Goal4EarlyScopedEq (applyNode g s n) (applyNode g t n) := by
  have hargs := map_store_eq h hins
  intro tid htid
  unfold applyNode
  rw [hargs]
  exact storeSet_scoped_congr s t _ h tid htid

private theorem faithful_step_scoped_congr (g : GraphDecl) (s t : Store) (n : NodeDecl)
    (h : Goal4EarlyScopedEq s t)
    (hops : n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧ n.op ≠ "OpName.FW_attn_zigzag")
    (hins : ∀ tid ∈ n.ins, tid ∉ goal4EarlyExcludedTids)
    (hget : ∀ i < 5, n.ins.getD i 0 ∉ goal4EarlyExcludedTids)
    (hbuddy : ∀ m ∈ g.replicaBuddies n, ∀ i < 5,
      m.ins.getD i 0 ∉ goal4EarlyExcludedTids) :
    Goal4EarlyScopedEq (applyNodeDistributedFaithful g s n)
      (applyNodeDistributedFaithful g t n) := by
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      g s n hops.1 hops.2.1 hops.2.2,
    applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      g t n hops.1 hops.2.1 hops.2.2]
  unfold applyNodeDistributed
  by_cases hmoe : n.op = "OpName.FW_all2all_moe_gmm"
  · rw [if_pos hmoe, if_pos hmoe]
    have hv : applyNodeFullExpertMoE_value g s n =
        applyNodeFullExpertMoE_value g t n := by
      unfold applyNodeFullExpertMoE_value
      dsimp only
      rw [h _ (hget 0 (by decide)), h _ (hget 1 (by decide)),
        h _ (hget 2 (by decide)),
        buddy_map_store_eq g n s t h 3 (fun m hm => hbuddy m hm 3 (by decide)),
        buddy_map_store_eq g n s t h 4 (fun m hm => hbuddy m hm 4 (by decide))]
    rw [hv]
    exact storeSet_scoped_congr s t _ h
  · rw [if_neg hmoe, if_neg hmoe]
    unfold applyNodeRingAttn
    rw [if_neg hops.2.2, if_neg hops.2.2]
    by_cases hwindow : n.op = "OpName.FW_attn_sliding_window"
    · rw [if_pos hwindow, if_pos hwindow]
      have hv : applyNodeRingAttn_sliding_window g s n =
          applyNodeRingAttn_sliding_window g t n := by
        unfold applyNodeRingAttn_sliding_window ringAttnBuddies
        dsimp only
        rw [buddy_map_store_eq g n s t h 0
              (fun m hm => hbuddy m hm 0 (by decide)),
          buddy_map_store_eq g n s t h 1
              (fun m hm => hbuddy m hm 1 (by decide)),
          buddy_map_store_eq g n s t h 2
              (fun m hm => hbuddy m hm 2 (by decide)),
          h _ (hget 3 (by decide)), h _ (hget 4 (by decide))]
      rw [hv]
      exact storeSet_scoped_congr s t _ h
    · rw [if_neg hwindow, if_neg hwindow]
      exact applyNode_scoped_congr g s t n h hins

private theorem faithful_step_graph_eq (g₁ g₂ : GraphDecl) (s : Store) (n : NodeDecl)
    (hranks : g₁.numRanks = g₂.numRanks)
    (hbuddies : g₁.replicaBuddies n = g₂.replicaBuddies n) :
    applyNodeDistributedFaithful g₁ s n = applyNodeDistributedFaithful g₂ s n := by
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
            rw [applyNode_congr_numRanks g₁ g₂ hranks]

private def goal4EarlyCommonPmNodes : List NodeDecl :=
  pm_goal_4.nodes.take 1023

private theorem goal4_early_pm_facts :
    pm_goal_4.numRanks = pm_goal_1.numRanks ∧
    pm_goal_4.nodes.take 1023 =
      pm_goal_1.nodes.take 13 ++
      (pm_goal_1.nodes.drop 14).take 13 ++
      (pm_goal_1.nodes.drop 28).take 997 ∧
    pm_goal_1.nodes.take 1025 =
      pm_goal_1.nodes.take 13 ++ [pm_goal_1.nodes[13]'(by native_decide)] ++
      (pm_goal_1.nodes.drop 14).take 13 ++ [pm_goal_1.nodes[27]'(by native_decide)] ++
      (pm_goal_1.nodes.drop 28).take 997 ∧
    (pm_goal_1.nodes[13]'(by native_decide)).outs = [11714] ∧
    (pm_goal_1.nodes[27]'(by native_decide)).outs = [11715] ∧
    (∀ n ∈ goal4EarlyCommonPmNodes,
      pm_goal_4.replicaBuddies n = pm_goal_1.replicaBuddies n ∧
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag" ∧
      (∀ tid ∈ n.ins, tid ∉ goal4EarlyExcludedTids) ∧
      (∀ i < 5, n.ins.getD i 0 ∉ goal4EarlyExcludedTids) ∧
      (∀ m ∈ pm_goal_1.replicaBuddies n, ∀ i < 5,
        m.ins.getD i 0 ∉ goal4EarlyExcludedTids)) := by
  native_decide

private theorem foldl_common_scoped (nodes : List NodeDecl)
    (hsub : ∀ n ∈ nodes, n ∈ goal4EarlyCommonPmNodes)
    (s t : Store) (hst : Goal4EarlyScopedEq s t) :
    Goal4EarlyScopedEq
      (nodes.foldl (applyNodeDistributedFaithful pm_goal_4) s)
      (nodes.foldl (applyNodeDistributedFaithful pm_goal_1) t) := by
  induction nodes generalizing s t with
  | nil => exact hst
  | cons n rest ih =>
      simp only [List.foldl]
      have hn := goal4_early_pm_facts.2.2.2.2.2 n
        (hsub n List.mem_cons_self)
      have hgraph := faithful_step_graph_eq pm_goal_4 pm_goal_1 s n
        goal4_early_pm_facts.1 hn.1
      have hscope := faithful_step_scoped_congr pm_goal_1 s t n hst
        ⟨hn.2.1, hn.2.2.1, hn.2.2.2.1⟩ hn.2.2.2.2.1
        hn.2.2.2.2.2.1 hn.2.2.2.2.2.2
      apply ih
      · intro m hm
        exact hsub m (List.mem_cons_of_mem n hm)
      · intro tid htid
        rw [hgraph]
        exact hscope tid htid

private theorem goal4_early_pm_prefix_scoped (init : Store) :
    Goal4EarlyScopedEq
      ((pm_goal_4.nodes.take 1023).foldl
        (applyNodeDistributedFaithful pm_goal_4) init)
      ((pm_goal_1.nodes.take 1025).foldl
        (applyNodeDistributedFaithful pm_goal_1) init) := by
  let a := pm_goal_1.nodes.take 13
  let b := (pm_goal_1.nodes.drop 14).take 13
  let c := (pm_goal_1.nodes.drop 28).take 997
  let e0 := pm_goal_1.nodes[13]'(by native_decide)
  let e1 := pm_goal_1.nodes[27]'(by native_decide)
  have h4 : pm_goal_4.nodes.take 1023 = a ++ b ++ c := goal4_early_pm_facts.2.1
  have h1 : pm_goal_1.nodes.take 1025 = a ++ [e0] ++ b ++ [e1] ++ c :=
    goal4_early_pm_facts.2.2.1
  rw [h4, h1]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hinit : Goal4EarlyScopedEq init init := fun _ _ => rfl
  have ha := foldl_common_scoped a (by
    intro n hn; unfold goal4EarlyCommonPmNodes
    rw [h4]; exact List.mem_append_left _ (List.mem_append_left _ hn)) init init hinit
  let s4a := a.foldl (applyNodeDistributedFaithful pm_goal_4) init
  let s1a := a.foldl (applyNodeDistributedFaithful pm_goal_1) init
  have he0 : Goal4EarlyScopedEq s4a
      (applyNodeDistributedFaithful pm_goal_1 s1a e0) := by
    intro tid htid
    rw [applyNodeDistributedFaithful_eq_of_not_mem_outs pm_goal_1 s1a e0 tid
      (by unfold e0; native_decide) (by
        rw [show e0.outs = [11714] from goal4_early_pm_facts.2.2.2.1]
        intro hmem
        simp only [List.mem_singleton] at hmem
        subst tid
        exact htid (by native_decide))]
    exact ha tid htid
  have hb := foldl_common_scoped b (by
    intro n hn; unfold goal4EarlyCommonPmNodes
    rw [h4]; exact List.mem_append_left _ (List.mem_append_right _ hn))
    s4a (applyNodeDistributedFaithful pm_goal_1 s1a e0) he0
  let s4b := b.foldl (applyNodeDistributedFaithful pm_goal_4) s4a
  let s1b := b.foldl (applyNodeDistributedFaithful pm_goal_1)
    (applyNodeDistributedFaithful pm_goal_1 s1a e0)
  have he1 : Goal4EarlyScopedEq s4b
      (applyNodeDistributedFaithful pm_goal_1 s1b e1) := by
    intro tid htid
    rw [applyNodeDistributedFaithful_eq_of_not_mem_outs pm_goal_1 s1b e1 tid
      (by unfold e1; native_decide) (by
        rw [show e1.outs = [11715] from goal4_early_pm_facts.2.2.2.2.1]
        intro hmem
        simp only [List.mem_singleton] at hmem
        subst tid
        exact htid (by native_decide))]
    exact hb tid htid
  exact foldl_common_scoped c (by
    intro n hn; unfold goal4EarlyCommonPmNodes
    rw [h4]; exact List.mem_append_right _ hn)
    s4b (applyNodeDistributedFaithful pm_goal_1 s1b e1) he1

private def goal4EarlyPmRoutingTids : List Tid :=
  [7846, 7847, 8010, 8011, 8174, 8175, 8338, 8339, 8502, 8503, 8666, 8667,
   8830, 8831, 8994, 8995, 9158, 9159, 9322, 9323, 9486, 9487, 9650, 9651]

private theorem goal4_early_pm_suffix_facts : ∀ tid ∈ goal4EarlyPmRoutingTids,
    (∀ n ∈ pm_goal_4.nodes.drop 1023, n.outs ≠ []) ∧
    (∀ n ∈ pm_goal_4.nodes.drop 1023, tid ∉ n.outs) ∧
    (∀ n ∈ pm_goal_1.nodes.drop 1025, n.outs ≠ []) ∧
    (∀ n ∈ pm_goal_1.nodes.drop 1025, tid ∉ n.outs) := by
  native_decide

/-- Scoped PM equality needed by the Goal-4 L0--L11 routing/logit reuse.  The
only graph mismatch is Goal 1's dead label chunks at nodes 13 and 27. -/
theorem goal4_early_pm_to_goal1 (init : Store) (tid : Tid)
    (htid : tid ∈ goal4EarlyPmRoutingTids) :
    denoteGraphDistributedFaithful pm_goal_4 init tid =
      denoteGraphDistributedFaithful pm_goal_1 init tid := by
  rcases goal4_early_pm_suffix_facts tid htid with ⟨g4nil, g4write, g1nil, g1write⟩
  rw [denoteGraphDistributedFaithful_eq_prefix pm_goal_4 init tid 1023 g4nil g4write,
    denoteGraphDistributedFaithful_eq_prefix pm_goal_1 init tid 1025 g1nil g1write]
  apply goal4_early_pm_prefix_scoped init tid
  unfold goal4EarlyPmRoutingTids at htid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
  rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private def goal4EarlySmRoutingTids : List Tid :=
  [4965, 5020, 5075, 5130, 5185, 5240, 5295, 5350, 5405, 5460, 5515, 5570]

private theorem goal4_early_sm_facts :
    sm_goal_4.numRanks = sm_goal_1.numRanks ∧
    sm_goal_4.nodes.take 457 = sm_goal_1.nodes.take 457 ∧
    (∀ n ∈ sm_goal_4.nodes.take 457,
      sm_goal_4.replicaBuddies n = sm_goal_1.replicaBuddies n) ∧
    (∀ tid ∈ goal4EarlySmRoutingTids,
      (∀ n ∈ sm_goal_4.nodes.drop 457, n.outs ≠ []) ∧
      (∀ n ∈ sm_goal_4.nodes.drop 457, tid ∉ n.outs) ∧
      (∀ n ∈ sm_goal_1.nodes.drop 457, n.outs ≠ []) ∧
      (∀ n ∈ sm_goal_1.nodes.drop 457, tid ∉ n.outs)) := by
  native_decide

private theorem foldl_sm_graph_eq (nodes : List NodeDecl) (init : Store)
    (hstep : ∀ n ∈ nodes, ∀ s,
      applyNodeDistributedFaithful sm_goal_4 s n =
        applyNodeDistributedFaithful sm_goal_1 s n) :
    nodes.foldl (applyNodeDistributedFaithful sm_goal_4) init =
      nodes.foldl (applyNodeDistributedFaithful sm_goal_1) init := by
  induction nodes generalizing init with
  | nil => rfl
  | cons n rest ih =>
      simp only [List.foldl, hstep n List.mem_cons_self init]
      apply ih
      intro m hm s
      exact hstep m (List.mem_cons_of_mem n hm) s

/-- SM has no label-chunk mismatch: its audited L0--L11 prefix is exactly Goal 1. -/
theorem goal4_early_sm_to_goal1 (init : Store) (tid : Tid)
    (htid : tid ∈ goal4EarlySmRoutingTids) :
    denoteGraphDistributedFaithful sm_goal_4 init tid =
      denoteGraphDistributedFaithful sm_goal_1 init tid := by
  rcases goal4_early_sm_facts.2.2.2 tid htid with ⟨g4nil, g4write, g1nil, g1write⟩
  rw [denoteGraphDistributedFaithful_eq_prefix sm_goal_4 init tid 457 g4nil g4write,
    denoteGraphDistributedFaithful_eq_prefix sm_goal_1 init tid 457 g1nil g1write]
  have hnodes := goal4_early_sm_facts.2.1
  rw [← hnodes]
  apply congrFun (foldl_sm_graph_eq (sm_goal_4.nodes.take 457) init (by
    intro n hn s
    exact faithful_step_graph_eq sm_goal_4 sm_goal_1 s n
      goal4_early_sm_facts.1 (goal4_early_sm_facts.2.2.1 n hn))) tid

/-- Goal 4's actual init environments contain every Goal-1 early shape except
label TID 4931; this is the shape bridge early routing proofs should request. -/
private theorem goal4_early_sm_shape_lookup_facts : ∀ tid,
    tid ∈ (sm_goal_4.nodes.take 457).flatMap (fun n => n.ins) →
    shapeEnvOfList sm_goal_1InitShapes tid ≠ none →
    shapeEnvOfList sm_goal_4InitShapes tid = shapeEnvOfList sm_goal_1InitShapes tid := by
  native_decide

theorem goal4_early_sm_shape_of_goal1_lookup (initSM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv) (tid : Tid) (sh : Shape)
    (hneeded : tid ∈ (sm_goal_4.nodes.take 457).flatMap (fun n => n.ins))
    (hlookup : sm_goal_1InitEnv tid = some sh) : (initSM tid).shape = sh := by
  apply hSM tid sh
  unfold sm_goal_4InitEnv
  unfold sm_goal_1InitEnv at hlookup
  have hnon : shapeEnvOfList sm_goal_1InitShapes tid ≠ none := by
    rw [hlookup]
    exact Option.some_ne_none sh
  have hbridge := goal4_early_sm_shape_lookup_facts tid hneeded hnon
  rw [hbridge]
  exact hlookup

/-- PM counterpart: Goal 4 supplies every Goal-1 init shape actually read by
the common 1023-node early prefix; the excluded 4931 chunk is not requested. -/
private theorem goal4_early_pm_shape_lookup_facts : ∀ tid,
    tid ∈ (pm_goal_4.nodes.take 1023).flatMap (fun n => n.ins) →
    shapeEnvOfList pm_goal_1InitShapes tid ≠ none →
    shapeEnvOfList pm_goal_4InitShapes tid = shapeEnvOfList pm_goal_1InitShapes tid := by
  native_decide

theorem goal4_early_pm_shape_of_goal1_lookup (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_4InitEnv) (tid : Tid) (sh : Shape)
    (hneeded : tid ∈ (pm_goal_4.nodes.take 1023).flatMap (fun n => n.ins))
    (hlookup : pm_goal_1InitEnv tid = some sh) : (initPM tid).shape = sh := by
  apply hPM tid sh
  unfold pm_goal_4InitEnv
  unfold pm_goal_1InitEnv at hlookup
  have hnon : shapeEnvOfList pm_goal_1InitShapes tid ≠ none := by
    rw [hlookup]
    exact Option.some_ne_none sh
  have hbridge := goal4_early_pm_shape_lookup_facts tid hneeded hnon
  rw [hbridge]
  exact hlookup

end
end TrainVerify.Denote.GeneratedPatterns
