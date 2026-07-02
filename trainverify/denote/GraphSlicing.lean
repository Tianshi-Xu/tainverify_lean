/- # Universal graph slicing lemma — REAL PROOF (route B, 2026-07-02).

  Motivation. `denoteGraph` is `List.foldl applyNode`. When the pipeline
  extracts a **local subgraph** `g_local` (topological subsequence of the
  global `g`) plus a local initial store `initLocal` that agrees with the
  global initial store on the tids g_local touches, the local computation
  must agree with the global one on every tid g_local writes — provided
  no g-only node writes into g_local's tid space.

  This lemma is the graph-generic backbone for the cut+Bridge audit
  architecture. Once proven, `cut_to_full` bridges become fully verifiable
  for any future model line.

  🔥 The previous `axiom` version of this file was **false as stated** — it
  lacked `List.Sublist g_local.nodes g.nodes` and `g.nodes.Nodup`.
  Counter-example without Sublist: `g.nodes = [n₁; n₂]` with both writing
  tid 7, and `g_local.nodes = [n₂; n₁]` — same node set, permuted order,
  different output. Nodup ensures each g-node's role is unambiguous
  (skipped-or-included is a per-node decision, not per-occurrence).
-/
import denote.Denote
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote

open TrainVerify.Denote

/-- Store agreement on a predicate set. -/
def StoreAgreesOn (s₁ s₂ : Store) (P : Tid → Prop) : Prop :=
  ∀ tid, P tid → s₁ tid = s₂ tid

/-- Every tid that any node in `g` reads. -/
def graphReads (g : GraphDecl) : Tid → Prop :=
  fun tid => ∃ n ∈ g.nodes, tid ∈ n.ins

/-- Every tid that any node in `g` writes. -/
def graphWrites (g : GraphDecl) : Tid → Prop :=
  fun tid => ∃ n ∈ g.nodes, tid ∈ n.outs

/-- Every tid used by `g` (either read or written). -/
def graphTids (g : GraphDecl) : Tid → Prop :=
  fun tid => graphReads g tid ∨ graphWrites g tid

/-!
### Auxiliary: `shapeEnvOfList` lookup lemma

Used by cut_to_full bridges to reduce `StoreShapesHold init env` to
membership facts about `env`'s underlying list.
-/

theorem mem_of_shapeEnvOfList_eq_some {xs : List (Tid × Shape)} {tid sh}
    (h : shapeEnvOfList xs tid = some sh) : (tid, sh) ∈ xs := by
  unfold shapeEnvOfList at h
  cases hf : xs.find? (fun p => p.1 = tid) with
  | none => rw [hf] at h; simp at h
  | some pair =>
    rw [hf] at h
    obtain ⟨t, s⟩ := pair
    simp only [Option.some.injEq] at h
    subst h
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [decide_eq_true_eq] at hpred
    subst hpred
    exact hmem

/-- InitGoalsHold distributes over list concatenation. Used by cut_to_full
    bridges to combine the global `initGoals` with per-goal `prereqs`
    intermediate proofs. -/
theorem InitGoalsHold_append {numParts : Nat} {xs ys : List LineageGoal}
    {Sm Pm : Store}
    (hxs : InitGoalsHold numParts xs Sm Pm)
    (hys : InitGoalsHold numParts ys Sm Pm) :
    InitGoalsHold numParts (xs ++ ys) Sm Pm := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hxs g h
  · exact hys g h


/-!
### Supporting lemma — pointwise applyNode congruence
-/

/-- **The key lemma**: `applyNode g s₁ n tid = applyNode g s₂ n tid` at any
    single `tid`, provided:
    (1) the two stores agree on `n.ins`, so `n.ins.map s₁ = n.ins.map s₂`
        (this makes the zipped payload identical on both sides);
    (2) the two stores agree at `tid` itself, which handles the case where
        `tid ∉ n.outs` and `applyNode` falls through to the store.

    Notably, this avoids any op-specific `evalOp` length reasoning — we
    case-split on whether `find?` returns `some` or `none` and dispatch. -/
theorem applyNode_congr_at
    (g : GraphDecl) (n : NodeDecl) (s₁ s₂ : Store) (tid : Tid)
    (hAgreeIns : ∀ t ∈ n.ins, s₁ t = s₂ t)
    (hAgreeFall : s₁ tid = s₂ tid) :
    applyNode g s₁ n tid = applyNode g s₂ n tid := by
  have hmap : n.ins.map s₁ = n.ins.map s₂ := by
    apply List.map_congr_left
    intro x hx
    exact hAgreeIns x hx
  unfold applyNode
  rw [hmap]
  -- Both sides are `storeSet s? (n.outs.zip (evalOp ... (n.ins.map s₂)))`
  -- with identical `pairs` list. Case-split on find?:
  --   some ⟨k, v⟩ → both return v (same on both sides)
  --   none        → both fall through to s tid, use hAgreeFall
  unfold storeSet
  cases hfound : (n.outs.zip (evalOp g.numRanks n.rank n.op n.params (List.map s₂ n.ins))).find?
    (fun p => decide (p.1 = tid)) with
  | none => exact hAgreeFall
  | some kv => rfl

/-- **Lemma D**: `applyNode` preserves store-agreement on a set `P`, provided
    `P` contains all input tids of the node. -/
theorem applyNode_preserves_agreement
    (g : GraphDecl) (n : NodeDecl) (s₁ s₂ : Store) (P : Tid → Prop)
    (hIns : ∀ tid ∈ n.ins, P tid)
    (hAgree : ∀ tid, P tid → s₁ tid = s₂ tid) :
    ∀ tid, P tid → applyNode g s₁ n tid = applyNode g s₂ n tid := by
  intro tid hP
  apply applyNode_congr_at g n s₁ s₂ tid
  · intro t ht; exact hAgree t (hIns t ht)
  · exact hAgree tid hP

/-- **Lemma E**: a one-sided `applyNode` step preserves agreement on P
    when the node writes no P-tid. -/
theorem applyNode_agree_left
    (g : GraphDecl) (n : NodeDecl) (s₁ s₂ : Store) (P : Tid → Prop)
    (hOutsDisjoint : ∀ tid, P tid → tid ∉ n.outs)
    (hAgree : ∀ tid, P tid → s₁ tid = s₂ tid) :
    ∀ tid, P tid → s₁ tid = applyNode g s₂ n tid := by
  intro tid hP
  have hNotOut : tid ∉ n.outs := hOutsDisjoint tid hP
  rw [applyNode_eq_of_not_mem_outs g s₂ n tid hNotOut]
  exact hAgree tid hP

/-!
### Sublist / Nodup helper
-/

/-- If `a :: t` is `Nodup` and `Sublist l t`, then `a ∉ l`.
    Used in the `cons` case of the main Sublist induction: when we skip
    `a` on the RHS but keep it on the LHS, `Nodup` forbids `a` from
    reappearing in the LHS's tail. -/
theorem List.not_mem_of_nodup_cons_of_sublist_tail
    {α : Type _} {a : α} {t l : List α}
    (hNodup : (a :: t).Nodup) (hSub : List.Sublist l t) :
    a ∉ l := by
  intro hMem
  have hMemT : a ∈ t := hSub.mem hMem
  exact (List.nodup_cons.mp hNodup).1 hMemT

/-!
### Main theorem — auxiliary form
-/

/-- **Auxiliary foldl-level statement.** Both sides use `applyNode g`
    (the LHS fold-function is rewritten via `applyNode_congr_numRanks`
    at the top-level call site). -/
theorem denoteGraph_slice_agrees_aux
    (g : GraphDecl) (P : Tid → Prop) :
    ∀ (G_nodes gl_nodes : List NodeDecl),
      List.Sublist gl_nodes G_nodes →
      G_nodes.Nodup →
      (∀ n ∈ gl_nodes, ∀ tid, tid ∈ n.ins → P tid) →
      (∀ n ∈ G_nodes, n ∉ gl_nodes → ∀ tid, P tid → tid ∉ n.outs) →
      ∀ (sG sL : Store),
      (∀ tid, P tid → sL tid = sG tid) →
      ∀ tid, P tid →
        (gl_nodes.foldl (applyNode g) sL) tid
          = (G_nodes.foldl (applyNode g) sG) tid := by
  intro G_nodes gl_nodes hSub
  induction hSub with
  | slnil =>
    -- gl_nodes = [], G_nodes = []. Both folds return init store.
    intro _hNodup _hIns _hNI sG sL hAgree tid hP
    simp only [List.foldl_nil]
    exact hAgree tid hP
  | @cons l₁ l₂ a hSub' ih =>
    -- gl_nodes = l₁ (unchanged), G_nodes = a :: l₂.
    -- a ∈ G_nodes but a ∉ gl_nodes (by Nodup of a::l₂ + Sublist l₁ l₂).
    intro hNodup hIns hNI sG sL hAgree tid hP
    -- a ∉ gl_nodes = l₁, by Nodup.
    have haNotIn : a ∉ l₁ :=
      List.not_mem_of_nodup_cons_of_sublist_tail hNodup hSub'
    -- a doesn't write any P-tid: hNI applied to a (∈ a::l₂, ∉ l₁).
    have haNoWrite : ∀ tid, P tid → tid ∉ a.outs := by
      apply hNI a (by simp) haNotIn
    -- Update the invariant: sL still agrees with applyNode g sG a on P.
    have hAgree' : ∀ tid, P tid → sL tid = applyNode g sG a tid := by
      intro t hPt
      exact applyNode_agree_left g a sL sG P haNoWrite hAgree t hPt
    -- Nodup of a::l₂ implies Nodup of l₂.
    have hNodupTail : l₂.Nodup := (List.nodup_cons.mp hNodup).2
    -- hIns unchanged (gl_nodes = l₁ unchanged).
    -- hNI restricts to `n ∈ l₂` from `n ∈ a::l₂`.
    have hNI' : ∀ n ∈ l₂, n ∉ l₁ → ∀ tid, P tid → tid ∉ n.outs := by
      intro n hn hnNotIn t hPt
      exact hNI n (List.Mem.tail a hn) hnNotIn t hPt
    -- Rewrite RHS: fold (a::l₂) sG tid = fold l₂ (applyNode g sG a) tid.
    change (l₁.foldl (applyNode g) sL) tid = ((a :: l₂).foldl (applyNode g) sG) tid
    rw [List.foldl_cons]
    -- Apply IH with sG := applyNode g sG a, sL := sL.
    exact ih hNodupTail hIns hNI' _ sL hAgree' tid hP
  | @cons₂ l₁ l₂ a hSub' ih =>
    -- gl_nodes = a :: l₁, G_nodes = a :: l₂.
    -- Both sides process `a` first.
    intro hNodup hIns hNI sG sL hAgree tid hP
    rw [List.foldl_cons, List.foldl_cons]
    -- Show that applyNode g sL a agrees with applyNode g sG a on P.
    have haIns : ∀ t ∈ a.ins, P t := hIns a (by simp)
    have hAgree' : ∀ t, P t → applyNode g sL a t = applyNode g sG a t := by
      intro t hPt
      exact applyNode_preserves_agreement g a sL sG P haIns hAgree t hPt
    -- Restrict hIns to l₁ (tail of gl_nodes).
    have hIns' : ∀ n ∈ l₁, ∀ t, t ∈ n.ins → P t := by
      intro n hn t ht
      exact hIns n (List.Mem.tail a hn) t ht
    -- hNI restricts to l₂, l₁.
    have hNI' : ∀ n ∈ l₂, n ∉ l₁ → ∀ t, P t → t ∉ n.outs := by
      intro n hn hnNotIn t hPt
      -- Need to show n ∉ a::l₁ (i.e. n ≠ a AND n ∉ l₁).
      -- n ∈ l₂, and Nodup (a::l₂) means a ∉ l₂, so n ≠ a.
      have hNaNotInL2 : a ∉ l₂ := (List.nodup_cons.mp hNodup).1
      have hnNeA : n ≠ a := fun he => hNaNotInL2 (he ▸ hn)
      have hnNotInGL : n ∉ a :: l₁ := by
        intro hIn
        cases hIn with
        | head => exact hnNeA rfl
        | tail _ hInL1 => exact hnNotIn hInL1
      exact hNI n (List.Mem.tail a hn) hnNotInGL t hPt
    -- Nodup of tail.
    have hNodupTail : l₂.Nodup := (List.nodup_cons.mp hNodup).2
    -- Apply IH.
    exact ih hNodupTail hIns' hNI' (applyNode g sG a) (applyNode g sL a)
      hAgree' tid hP

/-!
### Main theorem — user-facing
-/

/-- **Universal graph-slice agreement lemma.**

    If:
    1. `g.numRanks = g_local.numRanks`.
    2. `g_local.nodes` is a topological subsequence of `g.nodes`
       (`List.Sublist`).
    3. `g.nodes.Nodup` — nodes appear at most once (pipeline invariant:
       the emitter never duplicates a node).
    4. `initLocal` agrees with `initGlobal` on every tid used by `g_local`.
    5. Global nodes not in `g_local` don't write to any tid in
       `graphTids g_local`.

    Then `denoteGraph g_local initLocal tid = denoteGraph g initGlobal tid`
    for every tid written by `g_local`. -/
theorem denoteGraph_slice_agrees
    (g g_local : GraphDecl)
    (hRanks : g.numRanks = g_local.numRanks)
    (hSublist : List.Sublist g_local.nodes g.nodes)
    (hNodup : g.nodes.Nodup)
    (initGlobal initLocal : Store)
    (hInit : StoreAgreesOn initLocal initGlobal (graphTids g_local))
    (hNoInterference :
      ∀ n ∈ g.nodes, n ∉ g_local.nodes →
        ∀ tid, graphTids g_local tid → tid ∉ n.outs)
    (tid : Tid) (hOut : graphWrites g_local tid) :
    denoteGraph g_local initLocal tid = denoteGraph g initGlobal tid := by
  -- Rewrite g_local's fold function to `applyNode g` via numRanks_eq.
  have hFn : applyNode g_local = applyNode g :=
    applyNode_congr_numRanks _ _ hRanks.symm
  -- Set P := graphTids g_local. writes ⊆ tids, so hOut gives P tid.
  set P : Tid → Prop := graphTids g_local with hP_def
  have hP_tid : P tid := Or.inr hOut
  -- ins ⊆ reads ⊆ tids.
  have hIns : ∀ n ∈ g_local.nodes, ∀ t, t ∈ n.ins → P t := by
    intro n hn t ht
    exact Or.inl ⟨n, hn, ht⟩
  -- Unfold denoteGraph on both sides.
  unfold denoteGraph
  -- LHS uses applyNode g_local; rewrite to applyNode g.
  rw [hFn]
  -- Apply the aux with sG := initGlobal, sL := initLocal.
  exact denoteGraph_slice_agrees_aux g P g.nodes g_local.nodes hSublist hNodup
    hIns hNoInterference initGlobal initLocal hInit tid hP_tid

/-!
### Convenience: cut-input-derivation lemmas

For cut_to_full bridges. Once we know a tid is an init tid of `g` (not
written by any node in `g`), we can trade the raw store for the computed
store at that tid.

**Non-base cut_to_full note (2026-07-02)**: fully generic cut_to_full for
non-base goals (whose `cut_initGoals` contain intermediateGoals defined
on computed stores) needs a **fixed-point-on-writes** lemma of the form:

```
denoteGraph g (denoteGraph g initGlobal) tid = denoteGraph g initGlobal tid
    -- for tid ∈ graphWrites g, given g.nodes.Nodup + topological order
```

That lemma requires a fresh induction over `g.nodes` (topological order
preservation) — it is NOT a corollary of `denoteGraph_slice_agrees`.
It's not yet proven; without it, the M2 emitter can only handle base-case
goals (whose `cut_initGoals = initGoals`). Non-base goals fall back to
hand-written per-goal `sm_frame_*_self` / `pm_frame_*_self` helpers (see
`denote/gpt_ly4_regen/GoalNNBridge.lean` for the existing hand-written
patterns).
-/

/-- If `tid` is not written by any node in `g`, then
    `denoteGraph g init tid = init tid`. -/
theorem denoteGraph_at_init_tid
    (g : GraphDecl) (init : Store) (tid : Tid)
    (h : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraph g init tid = init tid := by
  unfold denoteGraph
  exact denoteGraph_tid_eq_of_forall_not_mem_outs g g.nodes init tid h

/-!
### Fixed-point-on-writes for `denoteGraph g` (P0 work, 2026-07-02)

Goal: prove `denoteGraph_slice_self_agrees`, which enables non-base
`cut_to_full` bridges. Reduces to:

```
denoteGraph g (denoteGraph g init) tid = denoteGraph g init tid
    -- for tid ∈ graphWrites g, given g.nodes.Nodup + topological order
```

Strategy:
1. **`IsTopoSorted g.nodes`**: every node's ins are either (a) not written by any
   node in g (true "input" tids), OR (b) written by a **strictly earlier** node.
2. **`applyNode_at_out_from_ins`**: at `tid ∈ n.outs`, `applyNode g s n tid` only
   depends on `s` at `n.ins` — the storeSet fallback fires ONLY when evalOp
   produces fewer entries than `|n.outs|`, which never happens for well-formed
   nodes (WellFormedNode predicate).
3. **`foldl_stable_at_writes`**: joint induction on prefix length k. At each
   step, the intermediate stores S_k(s) and S_k(s') agree on tids-written-by-
   prefix-k, given topological sort ensures earlier writes propagate correctly.
4. **Final lemma**: `denoteGraph g s = denoteGraph g s' on graphWrites g`
   whenever `s = s'` on `graphInits g` (init tids of g).
-/

/-- **WellFormedNode**: `evalOp` for this op with this params on any ins-length
    args produces at least `|outs|` entries. This is a per-op-family property
    that holds for all ops the pipeline generates. -/
def IsWellFormedNode (g : GraphDecl) (n : NodeDecl) : Prop :=
  ∀ s : Store, (evalOp g.numRanks n.rank n.op n.params (n.ins.map s)).length ≥ n.outs.length

/-- **`IsWellFormedGraph`**: every node in the graph is well-formed. -/
def IsWellFormedGraph (g : GraphDecl) : Prop :=
  ∀ n ∈ g.nodes, IsWellFormedNode g n

/-- **`IsTopoSorted`**: for every node `nodes[j]` and every tid it reads,
    either the tid is unwritten by any node in `nodes` (init tid), OR
    it's written by some strictly earlier node `nodes[i]` with `i < j`. -/
def IsTopoSorted (nodes : List NodeDecl) : Prop :=
  ∀ j, ∀ (hj : j < nodes.length), ∀ (tid : Tid), tid ∈ (nodes[j]'hj).ins →
    (∀ n ∈ nodes, tid ∉ n.outs) ∨
    (∃ i, ∃ (hij : i < j), tid ∈ (nodes[i]'(Nat.lt_trans hij hj)).outs)

/-- Helper: for `tid ∈ n.outs` with `evalOp` producing enough entries,
    `applyNode g s n tid` depends only on `n.ins.map s`. -/
theorem applyNode_at_out_congr_of_ins_agree
    (g : GraphDecl) (n : NodeDecl) (s₁ s₂ : Store) (tid : Tid)
    (hwf : IsWellFormedNode g n)
    (hout : tid ∈ n.outs)
    (hAgreeIns : ∀ t ∈ n.ins, s₁ t = s₂ t) :
    applyNode g s₁ n tid = applyNode g s₂ n tid := by
  have hmap : n.ins.map s₁ = n.ins.map s₂ := by
    apply List.map_congr_left
    intro x hx
    exact hAgreeIns x hx
  unfold applyNode
  rw [hmap]
  -- The two `storeSet` sides differ only by fallback. Show `find?` hits.
  set vals := evalOp g.numRanks n.rank n.op n.params (n.ins.map s₂) with hvals
  set pairs := n.outs.zip vals with hpairs
  have hlen : n.outs.length ≤ vals.length := hwf s₂
  have h_tid_in_keys : tid ∈ pairs.map Prod.fst := by
    show tid ∈ (n.outs.zip vals).map Prod.fst
    rw [List.map_fst_zip hlen]
    exact hout
  -- Show find? returns some, then both storeSets return the same v.
  have h_find_some : (pairs.find? (fun p => decide (p.1 = tid))).isSome := by
    apply List.find?_isSome.mpr
    obtain ⟨p, hp_mem, hp_fst⟩ : ∃ p ∈ pairs, p.1 = tid := by
      rcases List.mem_map.mp h_tid_in_keys with ⟨p, hp_mem, hp_eq⟩
      exact ⟨p, hp_mem, hp_eq⟩
    exact ⟨p, hp_mem, by simp [hp_fst]⟩
  unfold storeSet
  rcases Option.isSome_iff_exists.mp h_find_some with ⟨⟨t, v⟩, hv⟩
  rw [hv]

/-- Helper: if `tid` is not written by any node in a prefix `pre`, then the
    fold's value at `tid` equals the initial `s tid`. -/
theorem foldl_applyNode_at_not_written
    (g : GraphDecl) (pre : List NodeDecl) (s : Store) (tid : Tid)
    (h : ∀ n ∈ pre, tid ∉ n.outs) :
    (pre.foldl (applyNode g) s) tid = s tid := by
  induction pre generalizing s with
  | nil => simp [List.foldl]
  | cons a l ih =>
    simp only [List.foldl]
    rw [ih]
    · exact applyNode_eq_of_not_mem_outs g s a tid (h a List.mem_cons_self)
    · intro n hn; exact h n (List.mem_cons_of_mem _ hn)

/-- **`writesOfPrefix`**: tids written by any node in the prefix `pre`. -/
def writesOfPrefix (pre : List NodeDecl) (tid : Tid) : Prop :=
  ∃ n ∈ pre, tid ∈ n.outs

/-- Helper: at step k, if tid ∉ graphWrites of ANY node in nodes (fully init tid),
    then S_k(s) tid = s tid. -/
theorem foldl_applyNode_init_preserved
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store) (tid : Tid)
    (h : ∀ n ∈ nodes, tid ∉ n.outs) (k : Nat) :
    ((nodes.take k).foldl (applyNode g) s) tid = s tid := by
  apply foldl_applyNode_at_not_written
  intro n hn
  exact h n (List.mem_of_mem_take hn)

/-!
### Joint fold agreement (topologically-sorted well-formed graphs)

The main structural lemma: if two initial stores `s₁ s₂` agree on all tids
NOT written by any node in `g.nodes`, then their `foldl (applyNode g)` results
agree on all tids that ARE written by g plus all tids NOT written by g
(effectively on ALL tids that matter). Propagates via topological order.
-/

/-- Sub-property: at step k, the two folds agree on
    (`writesOfPrefix (nodes.take k)`) ∪ (`unwritten by any node in nodes`). -/
def AgreementFrontier (g : GraphDecl) (nodes : List NodeDecl)
    (s₁ s₂ : Store) (k : Nat) : Prop :=
  ∀ tid, (writesOfPrefix (nodes.take k) tid ∨
          (∀ n ∈ nodes, tid ∉ n.outs)) →
    ((nodes.take k).foldl (applyNode g) s₁) tid =
    ((nodes.take k).foldl (applyNode g) s₂) tid

/-- Helper: `outs_disjoint_across_nodes` — no tid is written by two different
    nodes. Stated as: for any pair of distinct nodes in the list, their outs
    are disjoint. -/
def OutsDisjoint (nodes : List NodeDecl) : Prop :=
  ∀ n₁ ∈ nodes, ∀ n₂ ∈ nodes, n₁ ≠ n₂ →
    ∀ tid, tid ∈ n₁.outs → tid ∉ n₂.outs

/-- Main fold-induction lemma (invariant version).

    Under `IsWellFormedGraph g`, `IsTopoSorted g.nodes`, `OutsDisjoint g.nodes`,
    `g.nodes.Nodup`, and `hInit` (agreement on unwritten tids), at every prefix
    step `k` the two folds agree on all "settled" tids. -/
theorem foldl_applyNode_frontier_holds
    (g : GraphDecl) (s₁ s₂ : Store)
    (hwf : IsWellFormedGraph g)
    (htopo : IsTopoSorted g.nodes)
    (hdisj : OutsDisjoint g.nodes)
    (hnodup : g.nodes.Nodup)
    (hInit : ∀ tid, (∀ n ∈ g.nodes, tid ∉ n.outs) → s₁ tid = s₂ tid) :
    ∀ k, AgreementFrontier g g.nodes s₁ s₂ k := by
  intro k
  induction k with
  | zero =>
    intro tid hset
    simp only [List.take_zero, List.foldl]
    -- k=0: writesOfPrefix (take 0) is empty, so hset must be case (b): unwritten.
    rcases hset with hwrite | hunw
    · rcases hwrite with ⟨n, hn, _⟩
      simp [List.take_zero] at hn
    · exact hInit tid hunw
  | succ k ih =>
    intro tid hset
    -- Split on whether take (k+1) = take k (k ≥ length) or has an extra node.
    by_cases hk : k < g.nodes.length
    · -- take (k+1) = take k ++ [nodes[k]]
      have hk1 : k + 1 ≤ g.nodes.length := hk
      -- Get the k-th node.
      set n_k := g.nodes[k]'hk with hn_k_def
      have h_take_succ : g.nodes.take (k + 1) = g.nodes.take k ++ [n_k] := by
        rw [hn_k_def]
        exact List.take_succ_eq_append_getElem hk
      -- Rewrite both fold sides using take_succ.
      rw [h_take_succ]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      -- Set intermediate stores S1_k := fold s₁ (take k), S2_k := fold s₂ (take k).
      set S1_k : Store := (g.nodes.take k).foldl (applyNode g) s₁ with hS1_k
      set S2_k : Store := (g.nodes.take k).foldl (applyNode g) s₂ with hS2_k
      -- Goal: applyNode g S1_k n_k tid = applyNode g S2_k n_k tid.
      -- Case-split on whether tid ∈ n_k.outs.
      by_cases htid_out : tid ∈ n_k.outs
      · -- Case A2: tid written by node[k]. Use applyNode_at_out_congr_of_ins_agree.
        -- Need hwf n_k (well-formed) and S1_k, S2_k agree on n_k.ins.
        have h_n_k_in_nodes : n_k ∈ g.nodes := by
          rw [hn_k_def]
          exact List.getElem_mem hk
        have hwf_nk : IsWellFormedNode g n_k := hwf n_k h_n_k_in_nodes
        apply applyNode_at_out_congr_of_ins_agree g n_k S1_k S2_k tid hwf_nk htid_out
        -- Show S1_k tid_in = S2_k tid_in for each tid_in ∈ n_k.ins.
        intro tid_in htid_in
        -- Use topo sort: tid_in either unwritten OR written by earlier node.
        have h_topo_case := htopo k hk tid_in htid_in
        rcases h_topo_case with h_unw | h_earlier
        · -- Unwritten case: apply ih with "case (b)" or use init preservation.
          have h_S1_eq : S1_k tid_in = s₁ tid_in :=
            foldl_applyNode_init_preserved g g.nodes s₁ tid_in h_unw k
          have h_S2_eq : S2_k tid_in = s₂ tid_in :=
            foldl_applyNode_init_preserved g g.nodes s₂ tid_in h_unw k
          rw [h_S1_eq, h_S2_eq]
          exact hInit tid_in h_unw
        · -- Earlier-writer case: use IH.
          rcases h_earlier with ⟨i, hij, htid_out_i⟩
          apply ih tid_in
          left
          -- Show tid_in is written by nodes.take k (since it's written by nodes[i] with i < k).
          have h_i_lt_all : i < g.nodes.length := Nat.lt_trans hij hk
          have h_i_in_take_len : i < (g.nodes.take k).length := by
            rw [List.length_take]; omega
          have h_mem_take : (g.nodes.take k)[i]'h_i_in_take_len ∈ g.nodes.take k :=
            List.getElem_mem h_i_in_take_len
          have h_getElem_eq : (g.nodes.take k)[i]'h_i_in_take_len = g.nodes[i]'h_i_lt_all :=
            List.getElem_take
          rw [h_getElem_eq] at h_mem_take
          exact ⟨g.nodes[i]'h_i_lt_all, h_mem_take, htid_out_i⟩
      · -- Case A1 or non-writing at this step: applyNode fixes tid to S_k tid.
        rw [applyNode_eq_of_not_mem_outs g S1_k n_k tid htid_out,
            applyNode_eq_of_not_mem_outs g S2_k n_k tid htid_out]
        -- Apply IH: tid must be settled by step k.
        apply ih tid
        rcases hset with hw | hu
        · -- tid ∈ writesOfPrefix (take (k+1)) but tid ∉ n_k.outs.
          -- So tid must be written by some earlier node in take k.
          rcases hw with ⟨n, hn_mem, hn_out⟩
          rw [h_take_succ] at hn_mem
          simp only [List.mem_append, List.mem_singleton] at hn_mem
          rcases hn_mem with hn_in_pre | hn_eq_nk
          · left; exact ⟨n, hn_in_pre, hn_out⟩
          · -- hn_eq_nk : n = n_k, but tid ∈ n.outs = n_k.outs contradicts htid_out.
            subst hn_eq_nk
            exact absurd hn_out htid_out
        · right; exact hu
    · -- k ≥ length: take (k+1) = take k = nodes, no change.
      push_neg at hk
      have hkge : g.nodes.length ≤ k := hk
      have h_take_eq : g.nodes.take (k + 1) = g.nodes.take k := by
        rw [List.take_of_length_le (Nat.le_succ_of_le hkge),
            List.take_of_length_le hkge]
      rw [h_take_eq]
      exact ih tid (by
        rcases hset with hw | hu
        · left
          rcases hw with ⟨n, hn, hout⟩
          rw [h_take_eq] at hn
          exact ⟨n, hn, hout⟩
        · right; exact hu)

/-!
### Corollaries: denoteGraph agreement + fixed-point on writes
-/

/-- Corollary of the frontier lemma: `denoteGraph g s₁ tid = denoteGraph g s₂ tid`
    for every tid that is written by g or unwritten by g (equivalently: for all
    tids that "matter"), given `s₁ = s₂` on unwritten tids. -/
theorem denoteGraph_agrees_on_writes
    (g : GraphDecl) (s₁ s₂ : Store)
    (hwf : IsWellFormedGraph g)
    (htopo : IsTopoSorted g.nodes)
    (hdisj : OutsDisjoint g.nodes)
    (hnodup : g.nodes.Nodup)
    (hInit : ∀ tid, (∀ n ∈ g.nodes, tid ∉ n.outs) → s₁ tid = s₂ tid)
    (tid : Tid) (hset : (∃ n ∈ g.nodes, tid ∈ n.outs) ∨
                        (∀ n ∈ g.nodes, tid ∉ n.outs)) :
    denoteGraph g s₁ tid = denoteGraph g s₂ tid := by
  unfold denoteGraph
  have h_frontier := foldl_applyNode_frontier_holds g s₁ s₂ hwf htopo hdisj hnodup hInit
    g.nodes.length
  -- Rewrite take length = whole list.
  have h_take_all : g.nodes.take g.nodes.length = g.nodes := by
    exact List.take_of_length_le (Nat.le_refl _)
  rw [← h_take_all]
  apply h_frontier tid
  rcases hset with hw | hu
  · left
    rcases hw with ⟨n, hn, hout⟩
    rw [h_take_all]
    exact ⟨n, hn, hout⟩
  · right; exact hu

/-- **`denoteGraph_fixed_point_on_writes`**: applying `denoteGraph g` to a
    store that's already the result of `denoteGraph g` yields the same value
    at any write tid. Equivalent to the "self-slice-agrees" lemma. -/
theorem denoteGraph_fixed_point_on_writes
    (g : GraphDecl) (init : Store)
    (hwf : IsWellFormedGraph g)
    (htopo : IsTopoSorted g.nodes)
    (hdisj : OutsDisjoint g.nodes)
    (hnodup : g.nodes.Nodup)
    (tid : Tid)
    (hset : (∃ n ∈ g.nodes, tid ∈ n.outs) ∨ (∀ n ∈ g.nodes, tid ∉ n.outs)) :
    denoteGraph g (denoteGraph g init) tid = denoteGraph g init tid := by
  -- Apply `denoteGraph_agrees_on_writes` with s₁ := denoteGraph g init, s₂ := init.
  -- They agree on unwritten tids because denoteGraph g init tid = init tid for
  -- unwritten tids (foldl_applyNode_at_not_written on the whole nodes list).
  have hInit_agree : ∀ tid, (∀ n ∈ g.nodes, tid ∉ n.outs) →
      (denoteGraph g init) tid = init tid := by
    intro t h
    unfold denoteGraph
    exact foldl_applyNode_at_not_written g g.nodes init t h
  -- Symmetric: (init) ≠ (denoteGraph g init) at writes generally, but we only
  -- need agreement on unwritten tids for the outer call.
  have h_apply := denoteGraph_agrees_on_writes g (denoteGraph g init) init
    hwf htopo hdisj hnodup hInit_agree tid hset
  exact h_apply

/-- **`denoteGraph_slice_self_agrees`**: the M2 non-base unblocker. For a slice
    `g_local ⊆ g` that's well-formed + topologically sorted + outs-disjoint +
    nodup, and shares g's structural properties, `denoteGraph g_local` applied
    to the computed store equals `denoteGraph g` at slice-write tids. -/
theorem denoteGraph_slice_self_agrees
    (g g_local : GraphDecl)
    (hRanks : g.numRanks = g_local.numRanks)
    (hSublist : List.Sublist g_local.nodes g.nodes)
    (hNodup_g : g.nodes.Nodup)
    (hwf_g : IsWellFormedGraph g)
    (htopo_g : IsTopoSorted g.nodes)
    (hdisj_g : OutsDisjoint g.nodes)
    (hNoInterference :
      ∀ n ∈ g.nodes, n ∉ g_local.nodes →
        ∀ tid, graphTids g_local tid → tid ∉ n.outs)
    (initGlobal : Store) (tid : Tid) (hOut : graphWrites g_local tid) :
    denoteGraph g_local (denoteGraph g initGlobal) tid =
    denoteGraph g initGlobal tid := by
  -- Step 1: apply slice_agrees with initLocal = initGlobal' := denoteGraph g initGlobal.
  -- StoreAgreesOn is trivial (same store).
  have h_agree : StoreAgreesOn (denoteGraph g initGlobal) (denoteGraph g initGlobal)
      (graphTids g_local) := fun _ _ => rfl
  have h_slice := denoteGraph_slice_agrees g g_local hRanks hSublist hNodup_g
    (denoteGraph g initGlobal) (denoteGraph g initGlobal) h_agree
    hNoInterference tid hOut
  rw [h_slice]
  -- Step 2: apply fixed-point-on-writes to fold on the RHS.
  -- tid ∈ graphWrites g_local ⊆ graphWrites g (via hSublist).
  have h_in_g : ∃ n ∈ g.nodes, tid ∈ n.outs := by
    rcases hOut with ⟨n, hn_local, hn_out⟩
    exact ⟨n, hSublist.subset hn_local, hn_out⟩
  exact denoteGraph_fixed_point_on_writes g initGlobal hwf_g htopo_g hdisj_g
    hNodup_g tid (Or.inl h_in_g)

end TrainVerify.Denote
