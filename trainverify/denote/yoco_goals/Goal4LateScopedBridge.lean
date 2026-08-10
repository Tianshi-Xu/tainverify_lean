/- Goal 4 L12--L23: per-prefix scoped transport to Goal 1. -/
import denote.yoco_goals.Goal4EarlyScopedBridge

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def Goal4LateScopeEq (scope : List Tid) (s t : Store) : Prop :=
  ∀ tid, tid ∈ scope → s tid = t tid

private def goal4LateTouches (scope : List Tid) (n : NodeDecl) : Bool :=
  n.outs.any (fun tid => decide (tid ∈ scope))

private def goal4LateBackwardScope (g : GraphDecl)
    (nodes : List NodeDecl) (targets : List Tid) : List Tid :=
  nodes.foldr (fun n scope =>
    if goal4LateTouches scope n then
      n.ins ++ (g.replicaBuddies n).flatMap (fun m => m.ins) ++ scope
    else scope) targets

private theorem goal4Late_storeSet_scope_congr (scope : List Tid)
    (s t : Store) (pairs : List (Tid × Tensor))
    (h : Goal4LateScopeEq scope s t) :
    Goal4LateScopeEq scope (storeSet s pairs) (storeSet t pairs) := by
  intro tid htid
  unfold storeSet
  cases hp : pairs.find? (fun p => decide (p.1 = tid)) with
  | none => exact h tid htid
  | some p => rfl

private theorem goal4Late_map_store_eq {scope xs : List Tid} {s t : Store}
    (h : Goal4LateScopeEq scope s t)
    (hxs : ∀ tid ∈ xs, tid ∈ scope) : xs.map s = xs.map t := by
  apply List.map_congr_left
  intro tid htid
  exact h tid (hxs tid htid)

private theorem goal4Late_buddy_map_store_eq (g : GraphDecl) (scope : List Tid)
    (n : NodeDecl) (s t : Store) (h : Goal4LateScopeEq scope s t)
    (idx : Nat)
    (hread : ∀ m ∈ g.replicaBuddies n, m.ins.getD idx 0 ∈ scope) :
    (g.replicaBuddies n).map (fun m => s (m.ins.getD idx 0)) =
      (g.replicaBuddies n).map (fun m => t (m.ins.getD idx 0)) := by
  apply List.map_congr_left
  intro m hm
  exact h _ (hread m hm)

private theorem goal4Late_applyNode_scope_congr (g : GraphDecl) (scope : List Tid)
    (s t : Store) (n : NodeDecl) (h : Goal4LateScopeEq scope s t)
    (hins : ∀ tid ∈ n.ins, tid ∈ scope) :
    Goal4LateScopeEq scope (applyNode g s n) (applyNode g t n) := by
  have hargs := goal4Late_map_store_eq h hins
  intro tid htid
  unfold applyNode
  rw [hargs]
  exact goal4Late_storeSet_scope_congr scope s t _ h tid htid

private theorem goal4Late_faithful_step_scope_congr (g : GraphDecl)
    (scope : List Tid) (s t : Store) (n : NodeDecl)
    (h : Goal4LateScopeEq scope s t)
    (hins : ∀ tid ∈ n.ins, tid ∈ scope)
    (hget : ∀ i < 5, n.ins.getD i 0 ∈ scope)
    (hbuddy : ∀ m ∈ g.replicaBuddies n, ∀ i < 5,
      m.ins.getD i 0 ∈ scope) :
    Goal4LateScopeEq scope (applyNodeDistributedFaithful g s n)
      (applyNodeDistributedFaithful g t n) := by
  unfold applyNodeDistributedFaithful
  by_cases hshuffle : n.op = "OpName.FW_maybe_shuffle"
  · rw [if_pos hshuffle, if_pos hshuffle]
    have hv : applyNodeFaithfulShuffleValue g s n =
        applyNodeFaithfulShuffleValue g t n := by
      unfold applyNodeFaithfulShuffleValue
      dsimp only
      rw [goal4Late_buddy_map_store_eq g scope n s t h 0
          (fun m hm => hbuddy m hm 0 (by decide)),
        h _ (hget 1 (by decide))]
    rw [hv]
    exact goal4Late_storeSet_scope_congr scope s t _ h
  · rw [if_neg hshuffle, if_neg hshuffle]
    by_cases hunshuffle : n.op = "OpName.FW_maybe_unshuffle"
    · rw [if_pos hunshuffle, if_pos hunshuffle]
      have hv : applyNodeFaithfulUnshuffleValue g s n =
          applyNodeFaithfulUnshuffleValue g t n := by
        unfold applyNodeFaithfulUnshuffleValue
        dsimp only
        rw [goal4Late_buddy_map_store_eq g scope n s t h 0
            (fun m hm => hbuddy m hm 0 (by decide)),
          h _ (hget 1 (by decide))]
      rw [hv]
      exact goal4Late_storeSet_scope_congr scope s t _ h
    · rw [if_neg hunshuffle, if_neg hunshuffle]
      by_cases hattn : n.op = "OpName.FW_attn_zigzag"
      · rw [if_pos hattn, if_pos hattn]
        have hv : applyNodeFaithfulZigzagAttnValue g s n =
            applyNodeFaithfulZigzagAttnValue g t n := by
          unfold applyNodeFaithfulZigzagAttnValue
          dsimp only
          rw [goal4Late_buddy_map_store_eq g scope n s t h 0
              (fun m hm => hbuddy m hm 0 (by decide))]
          split
          · rw [h _ (hget 1 (by decide)), h _ (hget 2 (by decide)),
              h _ (hget 3 (by decide)), h _ (hget 4 (by decide))]
          · have hk : ((g.replicaBuddies n).map
                (fun m => m.ins.getD 1 0)).map s =
                ((g.replicaBuddies n).map (fun m => m.ins.getD 1 0)).map t := by
              simp only [List.map_map, Function.comp_apply]
              exact goal4Late_buddy_map_store_eq g scope n s t h 1
                (fun m hm => hbuddy m hm 1 (by decide))
            have hvv : ((g.replicaBuddies n).map
                (fun m => m.ins.getD 2 0)).map s =
                ((g.replicaBuddies n).map (fun m => m.ins.getD 2 0)).map t := by
              simp only [List.map_map, Function.comp_apply]
              exact goal4Late_buddy_map_store_eq g scope n s t h 2
                (fun m hm => hbuddy m hm 2 (by decide))
            rw [hk, hvv, h _ (hget 3 (by decide)), h _ (hget 4 (by decide))]
        rw [hv]
        exact goal4Late_storeSet_scope_congr scope s t _ h
      · rw [if_neg hattn, if_neg hattn]
        unfold applyNodeDistributed
        by_cases hmoe : n.op = "OpName.FW_all2all_moe_gmm"
        · rw [if_pos hmoe, if_pos hmoe]
          have hv : applyNodeFullExpertMoE_value g s n =
              applyNodeFullExpertMoE_value g t n := by
            unfold applyNodeFullExpertMoE_value
            dsimp only
            rw [h _ (hget 0 (by decide)), h _ (hget 1 (by decide)),
              h _ (hget 2 (by decide)),
              goal4Late_buddy_map_store_eq g scope n s t h 3
                (fun m hm => hbuddy m hm 3 (by decide)),
              goal4Late_buddy_map_store_eq g scope n s t h 4
                (fun m hm => hbuddy m hm 4 (by decide))]
          rw [hv]
          exact goal4Late_storeSet_scope_congr scope s t _ h
        · rw [if_neg hmoe, if_neg hmoe]
          unfold applyNodeRingAttn
          rw [if_neg hattn, if_neg hattn]
          by_cases hwindow : n.op = "OpName.FW_attn_sliding_window"
          · rw [if_pos hwindow, if_pos hwindow]
            have hv : applyNodeRingAttn_sliding_window g s n =
                applyNodeRingAttn_sliding_window g t n := by
              unfold applyNodeRingAttn_sliding_window ringAttnBuddies
              dsimp only
              rw [goal4Late_buddy_map_store_eq g scope n s t h 0
                    (fun m hm => hbuddy m hm 0 (by decide)),
                goal4Late_buddy_map_store_eq g scope n s t h 1
                    (fun m hm => hbuddy m hm 1 (by decide)),
                goal4Late_buddy_map_store_eq g scope n s t h 2
                    (fun m hm => hbuddy m hm 2 (by decide)),
                h _ (hget 3 (by decide)), h _ (hget 4 (by decide))]
            rw [hv]
            exact goal4Late_storeSet_scope_congr scope s t _ h
          · rw [if_neg hwindow, if_neg hwindow]
            exact goal4Late_applyNode_scope_congr g scope s t n h hins

private theorem goal4Late_faithful_step_graph_eq (g₁ g₂ : GraphDecl)
    (s : Store) (n : NodeDecl)
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

private theorem goal4Late_fold_scope_congr (g₁ g₂ : GraphDecl)
    (scope : List Tid) (nodes : List NodeDecl) (s t : Store)
    (hst : Goal4LateScopeEq scope s t)
    (hranks : g₁.numRanks = g₂.numRanks)
    (hfacts : ∀ n ∈ nodes,
      g₁.replicaBuddies n = g₂.replicaBuddies n ∧
      (∀ tid ∈ n.ins, tid ∈ scope) ∧
      (∀ i < 5, n.ins.getD i 0 ∈ scope) ∧
      (∀ m ∈ g₂.replicaBuddies n, ∀ i < 5, m.ins.getD i 0 ∈ scope)) :
    Goal4LateScopeEq scope
      (nodes.foldl (applyNodeDistributedFaithful g₁) s)
      (nodes.foldl (applyNodeDistributedFaithful g₂) t) := by
  induction nodes generalizing s t with
  | nil => exact hst
  | cons n rest ih =>
      simp only [List.foldl]
      have hn := hfacts n List.mem_cons_self
      have hgraph := goal4Late_faithful_step_graph_eq g₁ g₂ s n hranks hn.1
      have hscope := goal4Late_faithful_step_scope_congr g₂ scope s t n hst
        hn.2.1 hn.2.2.1 hn.2.2.2
      apply ih
      · intro tid htid
        rw [hgraph]
        exact hscope tid htid
      · intro m hm
        exact hfacts m (List.mem_cons_of_mem n hm)

private theorem goal4Late_fold_to_filter (g : GraphDecl) (scope : List Tid)
    (nodes : List NodeDecl) (s t : Store) (hst : Goal4LateScopeEq scope s t)
    (hfacts : ∀ n ∈ nodes, goal4LateTouches scope n = true →
      (∀ tid ∈ n.ins, tid ∈ scope) ∧
      (∀ i < 5, n.ins.getD i 0 ∈ scope) ∧
      (∀ m ∈ g.replicaBuddies n, ∀ i < 5, m.ins.getD i 0 ∈ scope))
    (hskip : ∀ n ∈ nodes, goal4LateTouches scope n = false →
      n.outs ≠ [] ∧ ∀ tid ∈ scope, tid ∉ n.outs) :
    Goal4LateScopeEq scope
      (nodes.foldl (applyNodeDistributedFaithful g) s)
      ((nodes.filter (fun n => goal4LateTouches scope n)).foldl
        (applyNodeDistributedFaithful g) t) := by
  induction nodes generalizing s t with
  | nil => exact hst
  | cons n rest ih =>
      simp only [List.foldl, List.filter]
      cases ht : goal4LateTouches scope n with
      | false =>
          simp only [ht, Bool.false_eq_true, if_false]
          have hstep : Goal4LateScopeEq scope
              (applyNodeDistributedFaithful g s n) t := by
            intro tid htid
            rw [applyNodeDistributedFaithful_eq_of_not_mem_outs g s n tid
              (hskip n List.mem_cons_self ht).1
              ((hskip n List.mem_cons_self ht).2 tid htid)]
            exact hst tid htid
          exact ih _ _ hstep
            (fun m hm => hfacts m (List.mem_cons_of_mem n hm))
            (fun m hm => hskip m (List.mem_cons_of_mem n hm))
      | true =>
          simp only [ht, if_true]
          have hn := hfacts n List.mem_cons_self ht
          have hstep := goal4Late_faithful_step_scope_congr g scope s t n hst
            hn.1 hn.2.1 hn.2.2
          exact ih _ _ hstep
            (fun m hm => hfacts m (List.mem_cons_of_mem n hm))
            (fun m hm => hskip m (List.mem_cons_of_mem n hm))

private def goal4LateSmTargets : List Tid :=
  [5628, 5682, 5736, 5790, 5844, 5898, 5952, 6006, 6060, 6114, 6168, 6222]
private def goal4LatePmTargets : List Tid :=
  [9832, 9833, 9986, 9987, 10140, 10141, 10294, 10295, 10448, 10449,
   10602, 10603, 10756, 10757, 10910, 10911, 11064, 11065, 11218, 11219,
   11372, 11373, 11526, 11527]

private def goal4LateSm1Prefix := sm_goal_1.nodes.take 909
private def goal4LateSm4Prefix := sm_goal_4.nodes.take 914
private def goal4LatePm1Prefix := pm_goal_1.nodes.take 2001
private def goal4LatePm4Prefix := pm_goal_4.nodes.take 1998

private def goal4LateSmScope : List Tid :=
  goal4LateBackwardScope sm_goal_4 goal4LateSm4Prefix
    (goal4LateBackwardScope sm_goal_1 goal4LateSm1Prefix (0 :: goal4LateSmTargets))
private def goal4LatePmScope : List Tid :=
  goal4LateBackwardScope pm_goal_4 goal4LatePm4Prefix
    (goal4LateBackwardScope pm_goal_1 goal4LatePm1Prefix (0 :: goal4LatePmTargets))

private theorem goal4Late_sm_filter_eq :
    goal4LateSm4Prefix.filter (fun n => goal4LateTouches goal4LateSmScope n) =
      goal4LateSm1Prefix.filter (fun n => goal4LateTouches goal4LateSmScope n) := by
  native_decide

private theorem goal4Late_pm_filter_eq :
    goal4LatePm4Prefix.filter (fun n => goal4LateTouches goal4LatePmScope n) =
      goal4LatePm1Prefix.filter (fun n => goal4LateTouches goal4LatePmScope n) := by
  native_decide

private theorem goal4Late_sm_filter_facts (g : GraphDecl)
    (hg : g = sm_goal_4 ∨ g = sm_goal_1) :
    (∀ n ∈ (if g = sm_goal_4 then goal4LateSm4Prefix else goal4LateSm1Prefix),
      goal4LateTouches goal4LateSmScope n = true →
      (∀ tid ∈ n.ins, tid ∈ goal4LateSmScope) ∧
      (∀ i < 5, n.ins.getD i 0 ∈ goal4LateSmScope) ∧
      (∀ m ∈ g.replicaBuddies n, ∀ i < 5, m.ins.getD i 0 ∈ goal4LateSmScope)) ∧
    (∀ n ∈ (if g = sm_goal_4 then goal4LateSm4Prefix else goal4LateSm1Prefix),
      goal4LateTouches goal4LateSmScope n = false →
      n.outs ≠ [] ∧ ∀ tid ∈ goal4LateSmScope, tid ∉ n.outs) := by
  rcases hg with rfl | rfl
  · native_decide
  · have hne : sm_goal_1 ≠ sm_goal_4 := by native_decide
    simp only [hne, if_false]
    native_decide

private theorem goal4Late_pm_filter_facts (g : GraphDecl)
    (hg : g = pm_goal_4 ∨ g = pm_goal_1) :
    (∀ n ∈ (if g = pm_goal_4 then goal4LatePm4Prefix else goal4LatePm1Prefix),
      goal4LateTouches goal4LatePmScope n = true →
      (∀ tid ∈ n.ins, tid ∈ goal4LatePmScope) ∧
      (∀ i < 5, n.ins.getD i 0 ∈ goal4LatePmScope) ∧
      (∀ m ∈ g.replicaBuddies n, ∀ i < 5, m.ins.getD i 0 ∈ goal4LatePmScope)) ∧
    (∀ n ∈ (if g = pm_goal_4 then goal4LatePm4Prefix else goal4LatePm1Prefix),
      goal4LateTouches goal4LatePmScope n = false →
      n.outs ≠ [] ∧ ∀ tid ∈ goal4LatePmScope, tid ∉ n.outs) := by
  rcases hg with rfl | rfl
  · native_decide
  · have hne : pm_goal_1 ≠ pm_goal_4 := by native_decide
    simp only [hne, if_false]
    native_decide

private theorem goal4Late_sm_common_facts :
    sm_goal_4.numRanks = sm_goal_1.numRanks ∧
    ∀ n ∈ goal4LateSm1Prefix.filter (fun n => goal4LateTouches goal4LateSmScope n),
      sm_goal_4.replicaBuddies n = sm_goal_1.replicaBuddies n ∧
      (∀ tid ∈ n.ins, tid ∈ goal4LateSmScope) ∧
      (∀ i < 5, n.ins.getD i 0 ∈ goal4LateSmScope) ∧
      (∀ m ∈ sm_goal_1.replicaBuddies n, ∀ i < 5,
        m.ins.getD i 0 ∈ goal4LateSmScope) := by
  native_decide

private theorem goal4Late_pm_common_facts :
    pm_goal_4.numRanks = pm_goal_1.numRanks ∧
    ∀ n ∈ goal4LatePm1Prefix.filter (fun n => goal4LateTouches goal4LatePmScope n),
      pm_goal_4.replicaBuddies n = pm_goal_1.replicaBuddies n ∧
      (∀ tid ∈ n.ins, tid ∈ goal4LatePmScope) ∧
      (∀ i < 5, n.ins.getD i 0 ∈ goal4LatePmScope) ∧
      (∀ m ∈ pm_goal_1.replicaBuddies n, ∀ i < 5,
        m.ins.getD i 0 ∈ goal4LatePmScope) := by
  native_decide

private theorem goal4Late_sm_prefix_scope (init : Store) :
    Goal4LateScopeEq goal4LateSmScope
      (goal4LateSm4Prefix.foldl (applyNodeDistributedFaithful sm_goal_4) init)
      (goal4LateSm1Prefix.foldl (applyNodeDistributedFaithful sm_goal_1) init) := by
  have h4f := goal4Late_sm_filter_facts sm_goal_4 (Or.inl rfl)
  have h1f := goal4Late_sm_filter_facts sm_goal_1 (Or.inr rfl)
  have hne : sm_goal_1 ≠ sm_goal_4 := by native_decide
  simp only [hne, if_false] at h1f
  have hinit : Goal4LateScopeEq goal4LateSmScope init init := fun _ _ => rfl
  have h4 := goal4Late_fold_to_filter sm_goal_4 goal4LateSmScope
    goal4LateSm4Prefix init init hinit (by simpa using h4f.1) (by simpa using h4f.2)
  have h1 := goal4Late_fold_to_filter sm_goal_1 goal4LateSmScope
    goal4LateSm1Prefix init init hinit (by simpa using h1f.1) (by simpa using h1f.2)
  rw [goal4Late_sm_filter_eq] at h4
  have hc := goal4Late_fold_scope_congr sm_goal_4 sm_goal_1 goal4LateSmScope
    (goal4LateSm1Prefix.filter (fun n => goal4LateTouches goal4LateSmScope n))
    init init hinit goal4Late_sm_common_facts.1 goal4Late_sm_common_facts.2
  intro tid htid
  rw [h4 tid htid, hc tid htid]
  exact (h1 tid htid).symm

private theorem goal4Late_pm_prefix_scope (init : Store) :
    Goal4LateScopeEq goal4LatePmScope
      (goal4LatePm4Prefix.foldl (applyNodeDistributedFaithful pm_goal_4) init)
      (goal4LatePm1Prefix.foldl (applyNodeDistributedFaithful pm_goal_1) init) := by
  have h4f := goal4Late_pm_filter_facts pm_goal_4 (Or.inl rfl)
  have h1f := goal4Late_pm_filter_facts pm_goal_1 (Or.inr rfl)
  have hne : pm_goal_1 ≠ pm_goal_4 := by native_decide
  simp only [hne, if_false] at h1f
  have hinit : Goal4LateScopeEq goal4LatePmScope init init := fun _ _ => rfl
  have h4 := goal4Late_fold_to_filter pm_goal_4 goal4LatePmScope
    goal4LatePm4Prefix init init hinit (by simpa using h4f.1) (by simpa using h4f.2)
  have h1 := goal4Late_fold_to_filter pm_goal_1 goal4LatePmScope
    goal4LatePm1Prefix init init hinit (by simpa using h1f.1) (by simpa using h1f.2)
  rw [goal4Late_pm_filter_eq] at h4
  have hc := goal4Late_fold_scope_congr pm_goal_4 pm_goal_1 goal4LatePmScope
    (goal4LatePm1Prefix.filter (fun n => goal4LateTouches goal4LatePmScope n))
    init init hinit goal4Late_pm_common_facts.1 goal4Late_pm_common_facts.2
  intro tid htid
  rw [h4 tid htid, hc tid htid]
  exact (h1 tid htid).symm

private theorem goal4Late_sm_suffix_facts : ∀ tid ∈ goal4LateSmTargets,
    (∀ n ∈ sm_goal_4.nodes.drop 914, n.outs ≠ []) ∧
    (∀ n ∈ sm_goal_4.nodes.drop 914, tid ∉ n.outs) ∧
    (∀ n ∈ sm_goal_1.nodes.drop 909, n.outs ≠ []) ∧
    (∀ n ∈ sm_goal_1.nodes.drop 909, tid ∉ n.outs) ∧
    tid ∈ goal4LateSmScope := by
  native_decide

private theorem goal4Late_pm_suffix_facts : ∀ tid ∈ goal4LatePmTargets,
    (∀ n ∈ pm_goal_4.nodes.drop 1998, n.outs ≠ []) ∧
    (∀ n ∈ pm_goal_4.nodes.drop 1998, tid ∉ n.outs) ∧
    (∀ n ∈ pm_goal_1.nodes.drop 2001, n.outs ≠ []) ∧
    (∀ n ∈ pm_goal_1.nodes.drop 2001, tid ∉ n.outs) ∧
    tid ∈ goal4LatePmScope := by
  native_decide

/-- Every late SM gate-score observable agrees with Goal 1 on its own dependency
scope.  In particular this does not claim equality of the globally filtered node
lists: the final L23 independent branches are sorted differently. -/
theorem goal4_late_sm_to_goal1 (init : Store) (tid : Tid)
    (htid : tid ∈ goal4LateSmTargets) :
    denoteGraphDistributedFaithful sm_goal_4 init tid =
      denoteGraphDistributedFaithful sm_goal_1 init tid := by
  rcases goal4Late_sm_suffix_facts tid htid with ⟨g4nil, g4write, g1nil, g1write, hscope⟩
  rw [denoteGraphDistributedFaithful_eq_prefix sm_goal_4 init tid 914 g4nil g4write,
    denoteGraphDistributedFaithful_eq_prefix sm_goal_1 init tid 909 g1nil g1write]
  exact goal4Late_sm_prefix_scope init tid hscope

/-- PM counterpart for both rank-local gate-score observables at every late layer. -/
theorem goal4_late_pm_to_goal1 (init : Store) (tid : Tid)
    (htid : tid ∈ goal4LatePmTargets) :
    denoteGraphDistributedFaithful pm_goal_4 init tid =
      denoteGraphDistributedFaithful pm_goal_1 init tid := by
  rcases goal4Late_pm_suffix_facts tid htid with ⟨g4nil, g4write, g1nil, g1write, hscope⟩
  rw [denoteGraphDistributedFaithful_eq_prefix pm_goal_4 init tid 1998 g4nil g4write,
    denoteGraphDistributedFaithful_eq_prefix pm_goal_1 init tid 2001 g1nil g1write]
  exact goal4Late_pm_prefix_scope init tid hscope

#print axioms goal4_late_sm_to_goal1
#print axioms goal4_late_pm_to_goal1

end
end TrainVerify.Denote.GeneratedPatterns
