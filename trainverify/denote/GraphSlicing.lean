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

end TrainVerify.Denote
