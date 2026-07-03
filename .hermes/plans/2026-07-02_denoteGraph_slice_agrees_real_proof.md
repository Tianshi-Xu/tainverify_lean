# denoteGraph_slice_agrees — REAL PROOF plan (route B)

**Goal:** replace the `axiom denoteGraph_slice_agrees` in
`trainverify/denote/GraphSlicing.lean` with a **theorem** that proves the
subsequence-general version, so downstream cut_to_full bridges (and
YOCO Pattern_2/1/3/4) can be built on axiom-free foundations.

**Direction from 子鱼 (2026-07-02):** "真证，必须真证" → route B (full
subsequence). No axiom shortcut, no `sorry`-committed placeholder.

**Estimated wall time:** 1–2 days. Committing progress frequently under
`work-from-main-2026-06-12`.

---

## Current statement (the axiom to replace)

```lean
axiom denoteGraph_slice_agrees
    (g g_local : GraphDecl)
    (_hRanks : g.numRanks = g_local.numRanks)
    (initGlobal initLocal : Store)
    (_hInitLocal :
      StoreAgreesOn initLocal (denoteGraph g initGlobal) (graphReads g_local))
    (_hNoInterference :
      ∀ n ∈ g.nodes, n ∉ g_local.nodes →
        ∀ tid, graphTids g_local tid → tid ∉ n.outs)
    (tid : Tid) (_hOut : graphWrites g_local tid) :
    denoteGraph g_local initLocal tid = denoteGraph g initGlobal tid
```

### 🔥 The statement is **false as stated** — first fix, then prove

Counter-example: `g.nodes = [n₁; n₂]` with `n₁.outs = [7]`, `n₂.outs = [7]`,
`n₁.op ≠ n₂.op`. Take `g_local.nodes = [n₂; n₁]` (permutation, both nodes
present, `∉ g_local.nodes` never triggers so hypothesis vacuously true).
Then `denoteGraph g` returns `n₂`'s value for tid 7, but
`denoteGraph g_local` returns `n₁`'s value. Not equal.

**Missing hypothesis: `List.Sublist g_local.nodes g.nodes`** — g_local
must be a *topological subsequence* (order-preserving subset) of g.

The pipeline actually satisfies this: `sm_goal_N` / `pm_goal_N` are extracted
by keeping the nodes at positions in a specific index set of the global
`sm.nodes` / `pm.nodes`, in the same order. So adding the `Sublist`
hypothesis is not a scope reduction — it's the actual invariant the emitter
enforces (implicitly).

Even with `Sublist`, `hNoInterference` is still needed. Without it: `g.nodes
= [n₁; n₂; n₃]`, `g_local = [n₁; n₃]` (skip n₂), if n₂ writes some tid that
n₃ reads, the two runs disagree — that's exactly the "hidden write" case.

---

## Reformulated statement (target)

```lean
theorem denoteGraph_slice_agrees
    (g g_local : GraphDecl)
    (hRanks : g.numRanks = g_local.numRanks)
    (hSublist : List.Sublist g_local.nodes g.nodes)
    (initGlobal initLocal : Store)
    (hInitLocal :
      StoreAgreesOn initLocal (denoteGraph g initGlobal) (graphReads g_local))
    (hNoInterference :
      ∀ n ∈ g.nodes, n ∉ g_local.nodes →
        ∀ tid, graphTids g_local tid → tid ∉ n.outs)
    (tid : Tid) (hOut : graphWrites g_local tid) :
    denoteGraph g_local initLocal tid = denoteGraph g initGlobal tid
```

**Deprecate the old axiom entirely.** No back-compat: the axiom currently
has zero call sites (`grep` confirms), it was written speculatively for a
future emitter that hasn't been built.

---

## Proof strategy

The core intuition: `denoteGraph = foldl applyNode`. Induct on `hSublist`
(the `Sublist` structure gives us three cases: `slnil`, `cons`, `cons₂`).
Maintain a **store-agreement invariant** as we walk both node lists in lockstep.

### Central invariant

Let `sG k := (g.nodes.take k).foldl (applyNode g) initGlobal`.
Let `sL j := (g_local.nodes.take j).foldl (applyNode g_local) initLocal`.

**Invariant `INV(j, k)`:** for every `tid ∈ graphTids g_local`, `sL j tid = sG k tid`, provided:
- `List.Sublist (g_local.nodes.take j) (g.nodes.take k)` (we're at consistent positions)
- `sG k` up to k has processed every g_local node that appears in the first `j` positions of g_local
- Nodes in `(g.nodes.take k) \ (g_local.nodes.take j)` don't write any `graphTids g_local` tid

**Base case (j=0, k=0):** `sL 0 = initLocal`, `sG 0 = initGlobal`.
`hInitLocal` gives agreement on `graphReads g_local`. For agreement on
**writes** at the base, note: at step 0 no writes have happened; the LHS
is `initLocal tid` for a write-tid, and if the pipeline's `initLocal`
matches `initGlobal` on writes too... hmm, this needs care.

**Actually the cleaner formulation:** don't try to keep `sL` and `sG`
in agreement on *all* `graphTids` throughout the induction. Instead:

> Whenever `g_local.nodes.take j = g.nodes.take k ∩ g_local.nodes` (as
> subsequence), for every tid **read by any of the remaining** g_local
> nodes at position ≥ j, `sL j tid = sG k tid`.

But this is hairy. Let me try a **third framing** that's more directly
suggested by Sublist induction:

### Framing (final): parallel-walk with agreement-on-relevant

Define
```lean
def sliceRelevant (g_local : GraphDecl) : Tid → Prop :=
  graphReads g_local ∪ (fun t => t ∉ graphWrites g_local ∧ ...)
```
...no, still hairy.

### Simplest correct framing: the "run g_local inside g" identity

**Lemma A (rename):** the `List.foldl` over `g_local.nodes` using `applyNode g`
equals the `List.foldl` using `applyNode g_local`, provided `g.numRanks =
g_local.numRanks`. This is `applyNode_congr_numRanks` (already proved,
`Denote.lean:5814`).

So we can rewrite the goal to
`(g_local.nodes.foldl (applyNode g) initLocal) tid
 = (g.nodes.foldl (applyNode g) initGlobal) tid`
where **both sides use `applyNode g`**. This is much easier to induct on
because the fold function is the same.

**Lemma B (the actual induction):** Given `List.Sublist gl_nodes G_nodes`,
and appropriate hypotheses,
```
(gl_nodes.foldl (applyNode g) sL0) tid = (G_nodes.foldl (applyNode g) sG0) tid
```
for `tid ∈ graphWrites g_local`, assuming
- `∀ n ∈ G_nodes, n ∉ gl_nodes → ∀ tid, graphTids g_local tid → tid ∉ n.outs`
- `∀ tid ∈ graphTids g_local, sL0 tid = sG0 tid`

Note the second hypothesis is the **stronger** agreement: on **all** of
`graphTids`, not just reads. We upgrade the top-level user-facing statement
to require this stronger hypothesis, but it's actually satisfied by the
pipeline (initLocal for a `graphWrites` tid is arbitrary because writes
overwrite it — we can take initLocal to agree with `denoteGraph g initGlobal`
on those tids too by choosing initLocal freely on the write-only set).

**Actually the user-facing statement can hide this:** for write-only tids
(∈ graphWrites g_local, ∉ graphReads g_local, ∉ initLocal domain), we can
adjust initLocal to match `denoteGraph g initGlobal`. The output at those
tids depends only on which node last wrote them, which will be a `g_local`
node in both computations (since the missing g nodes don't write them by
`hNoInterference`). So the initial value doesn't matter for the final value.

To keep the proof clean, let me instead **strengthen `hInitLocal` slightly**:
```
hInitLocal : StoreAgreesOn initLocal (denoteGraph g initGlobal) (graphTids g_local)
```
(agreement on all g_local tids, not just reads). This is trivially true in the
pipeline (initLocal can be set = `denoteGraph g initGlobal` restricted to
`graphTids g_local`, unrestricted elsewhere). Simpler statement, simpler proof.

### Full Sublist induction (Lemma B)

Case `slnil`: `gl_nodes = []`, `G_nodes = []` (well, `slnil` is `[] ≤ []`
but `Sublist` allows `[] ≤ anything`). Actually `List.Sublist` induction
gives:
- `slnil : [].Sublist []`  ← wait, actually `Sublist` in Lean has 3 constructors:
  - `slnil : List.Sublist [] []`
  - `cons {l₁ l₂} (a) : Sublist l₁ l₂ → Sublist l₁ (a::l₂)` (a is in G_nodes but not gl_nodes)
  - `cons₂ {l₁ l₂} (a) : Sublist l₁ l₂ → Sublist (a::l₁) (a::l₂)` (a is in both)

  Hmm actually `sublist_nil` iff `l = []`, so `Sublist l []` forces `l = []`.
  So the recursive cases are:
  - Both empty: `slnil`
  - RHS non-empty, LHS empty: `cons` from `slnil` (or generally from any Sublist)
  - Both non-empty with matching head: `cons₂`
  - Both non-empty with mismatched head: `cons` (head of RHS not in LHS)

**Induction principle** (`List.Sublist.rec` or equivalent `induction ... with`):

Case 1 (`slnil`): both lists empty, both folds return their init. LHS =
`sL0 tid`, RHS = `sG0 tid`. `graphWrites g_local tid` is false for any tid
because `g_local` has no nodes. So `hOut` is vacuous, this case is trivial
(or: the theorem is trivially true because the conclusion has no witnesses).

Case 2 (`cons a hSub`): `gl_nodes` doesn't have `a` at the front, `G_nodes`
does. So the G-side fold processes `a` first, then processes the tail with
the recursive Sublist. By `hNoInterference` (applied to `a`), `a.outs` are
all outside `graphTids g_local`. So `applyNode g sG0 a` agrees with `sG0`
on all `graphTids g_local` tids. Apply IH with `sG0' := applyNode g sG0 a`
and `sL0' := sL0`. The precondition `sL0' tid = sG0' tid` for `graphTids`
tids holds by combining `sL0 tid = sG0 tid` (by outer hyp) with
`sG0' tid = sG0 tid` (by `hNoInterference` on `a`).

Case 3 (`cons₂ a hSub`): both sides process `a`. Apply IH with
`sG0' := applyNode g sG0 a` and `sL0' := applyNode g sL0 a`. Precondition:
`sL0' tid = sG0' tid` for `graphTids` tids. This requires showing
`applyNode g sL0 a tid = applyNode g sG0 a tid` given `sL0 tid = sG0 tid`
for **all input tids of a** (which are ⊆ `graphReads g_local` ⊆
`graphTids g_local`) and **all output tids of a** (which are ⊆
`graphWrites g_local` ⊆ `graphTids g_local`).

This is the **key congruence lemma**:

**Lemma C (applyNode congruence on agreement):** For any `g`, `n`, `s₁`, `s₂`,
if `s₁ tid = s₂ tid` for every `tid ∈ n.ins ∪ n.outs`, then
`applyNode g s₁ n tid = applyNode g s₂ n tid` for every
`tid ∈ n.ins ∪ n.outs`.

Actually we need it for every tid in `graphTids g_local`, not just `n.ins ∪
n.outs`. For tids **not** in `n.outs`, `applyNode g s n tid = s tid` (by
`applyNode_eq_of_not_mem_outs`, already proved `Denote.lean:5877`). For
tids in `n.outs`, the output value depends only on `n.ins` values via
`evalOp`, so agreement on `n.ins` gives agreement on the output.

So **Lemma C simplifies to:** if `∀ tid ∈ n.ins, s₁ tid = s₂ tid`, then
for every `tid`:
- if `tid ∉ n.outs`: `applyNode g s₁ n tid = s₁ tid` and `applyNode g s₂ n
  tid = s₂ tid`, both equal `s tid` if `s₁ tid = s₂ tid` at that tid;
- if `tid ∈ n.outs`: both equal the same `evalOp` output value.

That's clean.

### Summary: 3 supporting lemmas + 1 main theorem

1. **Lemma C (applyNode input-agree ⟹ output-agree):**
   ```
   applyNode_congr_of_ins_agree :
     ∀ (g : GraphDecl) (n : NodeDecl) (s₁ s₂ : Store),
       (∀ tid ∈ n.ins, s₁ tid = s₂ tid) →
       ∀ tid ∈ n.outs, applyNode g s₁ n tid = applyNode g s₂ n tid
   ```

2. **Lemma D (applyNode preserves store-agreement on a set):**
   ```
   applyNode_preserves_agreement :
     ∀ (g : GraphDecl) (n : NodeDecl) (s₁ s₂ : Store) (P : Tid → Prop),
       (∀ tid, tid ∈ n.ins → P tid) →  -- ins are in P
       (∀ tid, tid ∈ n.outs → P tid) → -- outs are in P
       (∀ tid, P tid → s₁ tid = s₂ tid) →
       ∀ tid, P tid → applyNode g s₁ n tid = applyNode g s₂ n tid
   ```

3. **Lemma E (single-side step preserves agreement — for `cons` case):**
   ```
   applyNode_agree_left :
     ∀ (g : GraphDecl) (n : NodeDecl) (s₁ s₂ : Store) (P : Tid → Prop),
       (∀ tid, tid ∈ n.outs → ¬ P tid) →  -- n doesn't touch P-tids
       (∀ tid, P tid → s₁ tid = s₂ tid) →
       ∀ tid, P tid → s₁ tid = applyNode g s₂ n tid
   ```

4. **Main theorem `denoteGraph_slice_agrees_aux`:** the foldl-level statement,
   inducts on `hSublist`. Then `denoteGraph_slice_agrees` unfolds
   `denoteGraph = foldl` and applies the aux.

---

## Task breakdown (bite-sized, each ~15-40 min)

### Task 1: Reformulate the statement (`GraphSlicing.lean`)

- Change `axiom` → `theorem ... := by sorry` (stub for now).
- Add `hSublist : List.Sublist g_local.nodes g.nodes`.
- Change `hInitLocal` to `StoreAgreesOn initLocal (denoteGraph g initGlobal) (graphTids g_local)`.
- Add `import Mathlib.Data.List.Sublists` if needed.
- Build should stay green (sorry is expected but visible in `#print axioms`).
- **Do NOT commit yet** — sorry visible in `#print axioms` is off-limits.
- Verify build: `lake build denote.GraphSlicing`.

### Task 2: Prove Lemma C (applyNode input-agree ⟹ output-agree)

Path: unfold `applyNode`, both sides expand `storeSet` with the same
`n.outs.zip (evalOp ... (ins.map s))` structure. The `List.find?` on
`(tid = tid')` gives the same output value if `ins.map s₁ = ins.map s₂`,
which follows from pointwise agreement.

Uses:
- `List.map_congr` (mathlib) or manual: `ins.map s₁ = ins.map s₂` when
  `∀ x ∈ ins, s₁ x = s₂ x`.

### Task 3: Prove Lemma D (applyNode preserves agreement on set P ⊇ ins ∪ outs)

Case split on `tid ∈ n.outs`:
- Yes: use Lemma C. Needs `∀ tid ∈ n.ins, s₁ tid = s₂ tid`, which follows
  from ins ⊆ P + agreement on P.
- No: both sides fall through to `s₁ tid = s₂ tid` via
  `applyNode_eq_of_not_mem_outs`.

### Task 4: Prove Lemma E (single-side step preserves agreement)

For `tid ∈ P`: `applyNode g s₂ n tid = s₂ tid` by
`applyNode_eq_of_not_mem_outs` (given `n.outs ∩ P = ∅`), so
`applyNode g s₂ n tid = s₂ tid = s₁ tid` (last step by outer agreement).

Simpler than Lemma D — one-sided.

### Task 5: Prove `denoteGraph_slice_agrees_aux` (foldl-level, Sublist induction)

Induct on `hSublist : List.Sublist gl_nodes G_nodes`.

Statement:
```
theorem denoteGraph_slice_agrees_aux
    (g : GraphDecl) (G_nodes gl_nodes : List NodeDecl)
    (hSublist : List.Sublist gl_nodes G_nodes)
    (P : Tid → Prop)
    (hIns : ∀ n ∈ gl_nodes, ∀ tid, tid ∈ n.ins → P tid)
    (hOuts : ∀ n ∈ gl_nodes, ∀ tid, tid ∈ n.outs → P tid)
    (hNoInterference : ∀ n ∈ G_nodes, n ∉ gl_nodes → ∀ tid, P tid → tid ∉ n.outs)
    (sG sL : Store) (hAgree : ∀ tid, P tid → sL tid = sG tid) :
    ∀ tid, P tid → (gl_nodes.foldl (applyNode g) sL) tid
                    = (G_nodes.foldl (applyNode g) sG) tid
```

Induction cases:
- `slnil`: both folds return init, use `hAgree`.
- `cons a hSub`: RHS steps through a, LHS doesn't. Use Lemma E on RHS to
  show `applyNode g sG a` still agrees with `sL` on P; apply IH.
- `cons₂ a hSub`: both step through a. Use Lemma D to show
  `applyNode g sL a` and `applyNode g sG a` agree on P; apply IH.

Membership hypotheses (`hIns`, `hOuts`, `hNoInterference`) propagate:
- `cons a hSub`: `hIns/hOuts` unchanged (gl_nodes unchanged),
  `hNoInterference` restricted to `G_nodes.tail`.
- `cons₂ a hSub`: `hIns/hOuts` restricted to `gl_nodes.tail` (a's
  contribution absorbed into IH's premise via Lemma D).

### Task 6: Wire the aux into `denoteGraph_slice_agrees`

- Set `P := graphTids g_local`.
- Verify `∀ n ∈ g_local.nodes, ∀ tid ∈ n.ins, graphTids g_local tid` from
  the definition of `graphReads` ⊆ `graphTids`.
- Same for `n.outs`.
- Apply aux with `sG := initGlobal`, `sL := initLocal`.
- Instantiate at `tid := tid` (the hypothesis of the main theorem).
- Need to show `graphTids g_local tid` given `graphWrites g_local tid` —
  trivially since `graphWrites ⊆ graphTids`.

### Task 7: Kill the sorry, verify axioms clean

- Once Task 6 closes, remove the `sorry` and the file has zero sorryAx.
- Run `#print axioms denoteGraph_slice_agrees` — must be only the kernel
  triple `[propext, Classical.choice, Quot.sound]`. If anything else
  appears (any axiom leaked in), backtrack.
- Also run `#print axioms gpt_main_all_goals` from
  `denote/gpt_ly4_regen/MainTheorem.lean` to confirm the production main
  theorem still has clean axioms (`GraphSlicing.lean` isn't in that
  closure — it's only in future yoco cut+Bridge lines).

### Task 8: Commit + push

```bash
cd trainverify
git add denote/GraphSlicing.lean
git commit -m "GraphSlicing: real proof of denoteGraph_slice_agrees (subsequence version)

Replaces the temporary axiom with a full theorem. Adds
List.Sublist g_local.nodes g.nodes hypothesis (the actual invariant the
emitter enforces). Proof: induction on Sublist + parallel-fold agreement
invariant. Zero new axioms, kernel triple only.

Prep work for YOCO Pattern_2/1/3/4 cut_to_full bridges."
git push origin work-from-main-2026-06-12
```

---

## Files touched

- **Modify:** `trainverify/denote/GraphSlicing.lean` (statement + full proof)
- No changes to `Denote.lean` (all supporting lemmas already exist:
  `applyNode_congr_numRanks`, `applyNode_eq_of_not_mem_outs`,
  `denoteGraph_nodes_cons`, `denoteGraph_nodes_append`, etc.)

## Risks & fallbacks

- **Risk 1: Lemma C's `evalOp` congruence needs a `List.map_congr` step.**
  If mathlib version differs, prove `map_congr` inline (5 lines).
- **Risk 2: Sublist induction leaves messy `⟨...⟩` in `hOuts` decomposition.**
  Mitigation: use `intro n hmem tid htid` explicitly rather than
  `apply`-style.
- **Risk 3: `hIns/hOuts` restriction on `cons₂` requires `tail` reasoning.**
  Might need helper: `List.Sublist.tail_of_cons₂`. Standard mathlib
  should have this.
- **Risk 4: Timing.** If Task 5 (the Sublist induction) drags past Day 1
  end, ship what's proven and re-plan. Do NOT commit sorry-versions.

## Verification steps

```bash
cd ~/.hermes/workspace/tainverify_lean/trainverify

# After each task:
lake build denote.GraphSlicing

# After Task 6:
lake env lean -e '#print axioms TrainVerify.Denote.denoteGraph_slice_agrees'
# Expected: [propext, Classical.choice, Quot.sound]

# Sanity: gpt_ly4_regen main theorem still green
lake --old build denote.gpt_ly4_regen.MainTheorem
lake env lean -e '#print axioms denote.gpt_ly4_regen.MainTheorem.gpt_main_all_goals'
```
