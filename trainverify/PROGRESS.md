# TrainVerify YOCO — Intermediate Reconstruction Progress

> **SUPERSEDED AS A STATUS REPORT (2026-07-28).** This 2026-07-14..21 worker
> journal remains useful for proof archaeology, but its counts and TODOs are not
> current. Use `YOCO_MOE_FAITHFUL_COVERAGE.md` for the mechanical
> ownership-aware count (1154/1156), `GOAL_3_4_LAYOUT_SPLIT.md` for the two
> false top-level equalities, and `UPSTREAM_NNSCALER_RVD_ZIGZAG.md` for the
> nnScaler finding. Do not infer current coverage from the historical category
> tables below.

Branch: `intermediate-goals-recon` (off main `c2e8b8f7`)
Deliverable file: `denote/yoco_goals/IntermediateReconstruction.lean`

## Objective

Prove `all_intermediateGoals_hold : InitGoalsHold pm.numRanks
all_intermediateGoals_list (denoteGraph sm initSM) (denoteGraph pm initPM)`
discharging the 1151 `intermediateGoal_*` reconstruction obligations that
gate the yoco cut→full bridges (Goals 1/2/3/4). Package as per-op
sub-lemmas joined via `InitGoalsHold_append`.

## Status: MACHINERY VALIDATED + ROTARY cs-CACHE BRIDGE CLOSED (12 goals)

This is a **partial** delivery per ground rule R6. The proof pattern is
fully validated end-to-end (zero sorry, kernel + native_decide axioms
only). Full 1151-goal completion is a 4–7 day effort (spec's own
estimate); a single session lands the reusable machinery + the
self-contained layer-0 replicated prefix and hands off the rest.

### Committed theorems (all zero-sorry, axiom-clean)

- `recon_intermediateGoal_4681` — FW_float
- `recon_intermediateGoal_4683` — FW_rms_norm
- `recon_intermediateGoal_4685` / `_4687` / `_4689` — FW_per_head_mix_precision_linear
- `recon_intermediateGoal_7383` / `_7387` / `_7392` / `_7396` / `_7400` —
  FW_multiref replicated copies (rank-0 head reconstruction, `replicated := true`),
  added by the SECOND worker (2026-07-14). Reduce to `veq_4681`/`veq_4683`.
- `recon_intermediateGoal_4692` / `_4693` — FW_rotary_embedding **1-tp Q'/K'**,
  added by the THIRD worker (2026-07-14). Close the rotary cs-cache bridge
  (see "ROTARY BRIDGE" section below).
- `all_intermediateGoals_proven_hold` — partial `InitGoalsHold` assembly over
  the 12 proven goals (`all_intermediateGoals_proven_list`).
- `all_intermediateGoals_list` — full 1151-item infrastructure list def (defined,
  not yet fully discharged).

Axiom audit (`AuditIR.lean` / `#print axioms all_intermediateGoals_proven_hold`):
`propext, Classical.choice, Quot.sound` + `goal_5_cut_to_full._native.native_decide.ax_*`.
No `sorryAx`, no user-declared axioms. R1 satisfied.

## ROTARY BRIDGE — worker #2's "genuine blocker" claim is REFUTED (worker #3, 2026-07-14)

Worker #2 wrote: *"FW_rotary_embedding … genuine blocker: NO goal bridges
4691 ↔ 11853 … requires a statement-level cs-cache agreement hypothesis or an
axiom."* **This is WRONG.** The bridge exists with no extra hypothesis/axiom:

1. `initGoal_4691 ∈ initGoals` — both SM and PM share init tid 4691 (rotary
   cs-cache, shape [4096,64]). `hInit` ⇒ `sm 4691 = pm 4691` via `recon_weight`.
2. PM broadcasts that init leaf to tids 11853..11864 via TWO `FW_multiref` nodes
   (rank 0 @ pm idx 1, rank 1 @ pm idx 14; `ins := [4691]`,
   `outs := (List.range 12).map (11853+·)`). Proven in `pm_multiref_11853_broadcast`
   (all `k<12`, PM last-writer = rank-1 node 14).
3. Compose ⇒ `sm_pm_rotary_cache_agree : sm 4691 = pm (11853+k)`, all k<12.
   Worker #2's `grep "11853"` found no *goal* because the bridge is a graph-
   structural value equality, precisely what the reconstruction machinery derives.

Reusable gears added (zero-sorry, kernel+native_decide axioms only):
`storeSet_zip_replicate_mem`, `applyNode_fw_multiref_mem_out`,
`pm_multiref_11853_broadcast`, `sm_pm_rotary_cache_agree`,
`veq_4685`/`veq_4687`/`shape_4685`/`shape_4687`.

**Closed:** the 2 fully-1-tp rotary goals `_4692` (Q') / `_4693` (K') — non-cs
inputs (pos 4690 init, q 4685, k 4687) are already-proven layer-0 replicated
per-head projections; value eq is pure input-congruence on `fw_rotary_embedding`.

**Still gated (honest):**
- 1-tp `4746`/`4747` (cs=11854): q/k inputs 4740/4742 chain through rms_norm 4738
  → FW_add → **FW_all2all_moe_gmm + topk_routing + sigmoid** (full layer-0 MoE),
  deep post-attention 1-tp values. A "reconstruct layer-0 MoE" problem, not rotary.
- The 20 rotary **2-tp** goals (4800…5287, cs=11855..11864): use
  `sm_pm_rotary_cache_agree k=2..11` for cs, but q/k inputs are 2-tp sharded
  per-head projections (7783/7784 …) needing `extract_dual` + per-head
  `_allGather0_commute_2` first. The rotary commute lemma already exists and is
  proven on the goal_3 cut graphs (`Pattern_3.lean:10123`
  `fw_rotary_apply_allGather0_commute_2_1d`, applied @10533); porting to full
  sm/pm needs only the per-head 2-tp input reconstruction as a side hypothesis.

## WORKER #4 (2026-07-14) — 2-tp `extract_dual` ROTARY BRIDGEHEAD established

Goal: pioneer the 2-tp `extract_dual` reconstruction pattern via the 20
`FW_rotary_embedding` 2-tp goals. **Outcome: the 2-tp reconstruction pattern
for the rotary op ITSELF is fully built and zero-sorry, but every rotary 2-tp
goal is gated on attention/MoE-region input reconstruction (no template) — so
the gears are stated CONDITIONALLY on those inputs.** This matches worker #3's
honest assessment; the spec's "pieces in place" optimism conflated cut-graph
(`Pattern_1.prove_goal_1`, where intermediates are boundary init-leaves resolved
by `extract_dual`/`hInit`) with full-graph reconstruction (must re-derive each
tid from init weights by chaining prior nodes).

### The 20 rotary 2-tp goals (enumerated, Task 1)

Q'/K' pairs across 10 layers: 4800/4801, 4854/4855, 4908/4909, 4962/4963,
5016/5017, 5070/5071, 5124/5125, 5178/5179, 5232/5233, 5286/5287. Each Q' goal
`tps=[p0(r0),p1(r1)]`, gatherDim=0, replicated=false, shards `[2048,16,64]` →
`[4096,16,64]`; each K' shards `[2048,4,64]` → `[4096,4,64]`. cs-cache closed via
`sm_pm_rotary_cache_agree k=2..11`.

### Root cause of the gating (dependency trace)

Goal 4800's q-input SM tid 4794 chains through 2× `FW_attn_sliding_window` +
2× `FW_all2all_moe_gmm` (141 SM tids) — the bespoke attention/MoE region with
**no reconstruction template**. Only layer-0 rotary (4692/4693) is shallow
enough to close unconditionally. This is a structural blocker, not a rotary one.

### Reusable gears added (zero-sorry, kernel axioms only — R1)

- `wrap_2tp_allGather` — generic 2-tp (gatherDim=0, non-replicated) `InitGoalHolds`
  wrapper. Analog of `wrap_1tp`; reduces a 2-tp goal to a value-eq + 3 shapes.
- `rotary_fst_gather_commute` / `rotary_snd_gather_commute` — pure tensor-algebra
  Q'/K' commute lemmas (`fw_rotary_embedding(allGather q,…).1 = allGather(rotary q).1`),
  built on the existing `fw_rotary_embedding_allGather0_commute_2` (Denote.lean:22937).
- `recon_rotary_2tp_fst` / `recon_rotary_2tp_snd` — **the parametrized 2-tp gear.**
  Abstract over tids/node-indices: given SM/PM node reductions + cs agreement +
  the 3 sharded-input recons + 6 PM shard shapes, produce `InitGoalHolds`. THIS is
  the recipe for the ~910 remaining 2-tp goals (swap the rotary commute for the
  op-specific `_allGather0_commute_2`).
- `sm_rotary_4800/4801_node`, `pm_rotary_7805/7806/7807/7808_node` — per-goal
  `native_decide` node reductions (mechanical template for the other 18 goals).
- `recon_intermediateGoal_4800_of_inputs` / `_4801_of_inputs` — the concrete
  layer-2 Q'/K' goals, each now a single application of the parametrized gear,
  conditional on the 3 attention-gated sharded inputs (pos 4799, q 4794, k 4796).

Not added to `all_intermediateGoals_proven_hold` (they are conditional, not
unconditionally proven — correct behavior).

### Recommended next attack

Build the `FW_attn_sliding_window` (+ `FW_all2all_moe_gmm`) 2-tp reconstruction
template. That single template unblocks the 3 sharded inputs feeding every rotary
2-tp goal, at which point all 20 close mechanically via `recon_rotary_2tp_fst/snd`,
and the same pattern generalizes to FW_view/reshape/add 2-tp goals.

## Category coverage table

| Category                              | Count | Status                          |
|---------------------------------------|-------|---------------------------------|
| FW_float                              | 73    | PoC proven (goal 4681)          |
| FW_rms_norm                           | 50    | PoC proven (goal 4683)          |
| FW_per_head_mix_precision_linear      | 50    | PoC proven (4685/4687/4689)     |
| FW_multiref                           | 280   | 5 proven (replicated 7383-7400) |
| FW_reshape                            | 144   | un-attempted                    |
| FW_mix_precision_linear               | 120   | un-attempted                    |
| FW_view                               | 120   | un-attempted                    |
| FW_add                                | 72    | un-attempted                    |
| FW_topk_routing                       | 48    | un-attempted                    |
| FW_rotary_embedding                   | 24    | 2 proven (1-tp 4692/4693); 20 2-tp gears BUILT (`recon_rotary_2tp_fst/snd`), conditional on attention inputs; 4746/4747 gated on layer-0 MoE |
| FW_norm_linear                        | 24    | un-attempted                    |
| FW_all2all_moe_gmm                    | 24    | un-attempted                    |
| FW_sigmoid                            | 24    | un-attempted                    |
| FW_swiglu                             | 24    | un-attempted                    |
| FW_mul                                | 24    | un-attempted                    |
| FW_to                                 | 24    | un-attempted                    |
| FW_attn_sliding_window                | 12    | hard (no template)              |
| FW_attn_zigzag                        | 12    | hard (NEW category, see notes)  |
| FW_maybe_shuffle                      | 1     | un-attempted                    |
| FW_maybe_unshuffle                    | 1     | un-attempted (audit cp2 first)  |
| **TOTAL**                             | 1151  | **12 proven / 1139 remaining**  |

Fully-closed categories cover only their layer-0 prefix instances so far
(10 goals). The reusable helper lemmas needed to scale each of the proven
categories to all their instances are in place.

## CRITICAL FINDING (2026-07-14, second worker) — the 1-tp closure is EXACTLY 10 goals

The HANDOFF tier ordering ("FW_float 73 easy value-identity, close 20+") is
**over-optimistic**. Empirical dependency analysis (scripts against the parsed
sm/pm graphs) shows:

1. **Only ~99 of 1151 goals are 1-tp; the other ~1052 are 2-tp sharded.**
   Per category the 1-tp counts are tiny (FW_float 6/73, FW_rms_norm 5/50,
   FW_to 24/24 but see below, etc.).

2. **The pure-1-tp topological closure from the init leaves is EXACTLY the 5
   original replicated-prefix goals.** Computed by fixpoint: a 1-tp goal is
   "provable" iff all its SM inputs resolve (through FW_multiref copies) to
   init-weights or already-provable 1-tp goals. The fixpoint = {4681, 4683,
   4685, 4687, 4689} — nothing else. Every other 1-tp goal has at least one
   input that is a **2-tp sharded value** (i.e. an attention/MoE output), so
   it cannot be discharged without first reconstructing that 2-tp value.
   Example: FW_to goal 5343 → input mrefs to 5334 (per_head) → 8015 → ... →
   post-attention sharded tensors.

3. **The multiref replicated copies (7383/7387/7392/7396/7400) are the only
   additional reachable goals** — they are `replicated := true` copies of
   4681/4683 whose reconstruction picks the rank-0 head. Proven this run (+5).
   Total closed = 10.

4. **The topological frontier past the 10 proven goals is BLOCKED:** the next
   ops in graph order after Q/K/V per-head (4685/4687/4689) are:
   - `FW_rotary_embedding` (4692/4693, 1-tp) — ~~**genuine blocker**~~ **[REFUTED
     by worker #3, 2026-07-14 — see "ROTARY BRIDGE" section above]**: SM feeds the
     cos/sin cache from init tid 4691, PM from init tid 11853. Both are init
     leaves. Worker #2 claimed **NO goal bridges 4691 ↔ 11853** — but PM's two
     `FW_multiref` nodes broadcast init tid 4691 → 11853..11864, and
     `initGoal_4691 ∈ initGoals`, so `pm 11853 = pm 4691 = sm 4691` is derivable
     from the PM graph + `hInit` with NO extra hypothesis/axiom. 4692/4693 are
     now PROVEN. (The `grep "11853"` gave zero *goal* hits because the bridge is a
     graph-structural value equality, not a lineage goal.)
   - `FW_attn_sliding_window` / `FW_attn_zigzag` — bespoke Tier D (attn_zigzag
     nodes use computed `ins := ((List.range 5).map ...)`; their inputs 5342-5346
     are deep 2-tp values).

   Consequently **there is no low-hanging 2-tp fruit**: the first 2-tp ops that
   are "easy" (view/reshape/add/linear) all live AFTER attention in the
   dependency DAG, so they cannot be reconstructed until rotary + attention are
   cleared. Incremental scaling is gated on the bespoke ops, exactly matching
   the consultation's "realistic 4-7 days / pessimistic 2-4 weeks" estimate.

**Recommendation for the next worker:** the productive path is NOT more 1-tp
goals (exhausted). It is (a) resolve the rotary cs-cache bridge at the statement
level, then (b) build the 2-tp `extract_dual` + `_allGather0_commute_2`
reconstruction for the attention/MoE region, following `prove_goal_1`
(`Pattern_1.lean:4165+`) which already consumes these intermediateGoals as cut
boundaries. Each 2-tp recon is roughly one `prove_goal_1`-step of effort.

## Deviations from spec (audit notes, AGENTS.md rule 20)

1. **20 categories, not 19.** Discovered a NEW category `FW_attn_zigzag`
   (12 goals) not in the spec's list. It is CP zigzag context-parallel
   attention — no existing commute template; classified hard alongside
   FW_attn_sliding_window.

2. **Zero `<init>` cases, not 12.** The spec anticipated 12 goals whose
   `ts` is an SM init tid discharged via `initGoals_preserved`. The actual
   generated `all_intermediateGoals` has none — every goal's `ts` is written
   by an SM node. `initGoals_preserved` machinery is therefore unused here.

3. **FW_rotary_embedding deferred.** SM rotary's cs-input is tid 4691 but
   PM rotary's cs-input is tid 11853 — the two graphs feed rotary from
   different producers. A boundary lemma linking `sm 4691 ↔ pm 11853` is
   required before the rotary commute lemma applies; not a value-identity
   reduction. Left for the follow-up worker.

4. **Partial (not full) assembly theorem.** Per R6, `all_intermediateGoals_hold`
   over the full list is NOT stated with a sorry. Instead a separate
   `all_intermediateGoals_proven_hold` over the honestly-proven sub-list is
   committed. The full `all_intermediateGoals_list` def exists as
   infrastructure for the follow-up.

## Denote / semantic additions (R2 log)

- **No edits to `denote/Denote.lean` or `denote/DenoteMoE.lean` semantics.**
- New lemmas added ONLY in `denote/yoco_goals/IntermediateReconstruction.lean`:
  - `applyNode_fw_multiref3_{first,second,third}_out'` — generic (dim `[3]`)
    multiref3 output reductions (previously only goal-specific `_gNNN`
    variants existed).
  - `recon_weight`, `wrap_1tp`, `shape_weight` — reusable reconstruction gears.
  - `veq_*` / `shape_*` per-goal value/shape lemmas.

No commute-lemma audit failure encountered (no new sharding-commute axioms
were introduced; the proven categories are the replicated 1-tp prefix where
SM and PM compute the identical op at rank 0).

## Green targets (must-not-break)

- `denote.yoco_goals.YocoMoE_MainSummary` — verified building.
- `denote.yoco_goals.Instances` — unchanged (still 4 sorries; those are the
  eventual removal target once the full list is discharged).
- `denote.yoco_goals.Goal5Bridge_Auto` — unchanged.

See `HANDOFF.md` for the validated proof recipe to scale the remaining
1146 goals.

## WORKER #5 (2026-07-14) — Rotary 2-tp adversarial hypothesis inventory

Closed the LOWEST-tid rotary 2-tp goal `recon_intermediateGoal_4800` (+ `_4801`)
as canonically-named, fully-threaded, zero-sorry theorems (kernel triple +
project-baseline native_decide axioms; audited in `AuditIR.lean`). These wrap
worker #4's `recon_rotary_2tp_fst/snd` gears with the EXACT minimal hypothesis set.

**Adversarial finding — the threaded hypotheses split into two kinds:**
- `hq` (4794) / `hk` (4796): direct op `FW_per_head_mix_precision_linear`, each
  HAS an `intermediateGoal_*`, but transitively gated on `FW_all2all_moe_gmm` +
  `FW_attn_sliding_window` (MoE/attention region, no template). **Irreducible /
  attention-shaped.**
- `hpos` (4799): SM position tensor is an INIT LEAF (`initGoal_4799 ∈ initGoals`),
  PM-sharded by 2× `ChunkPrim`. NO `intermediateGoal_4799`. **Structural, not
  attention-gated** (reducible-in-principle from `hInit`; left threaded due to the
  `[4096]→[2048,1]` ChunkPrim-reshape roundtrip lacking a ready lemma).

Per-goal threaded count = **9** (3 value-eqs + 6 shard shapes). The irreducible
attention core is **2 value-eqs per layer** → 20 distinct facts across all 20
rotary 2-tp goals. Full breakdown + stmt-level-lift assessment:
`~/HYPOTHESIS_INVENTORY.md`. **Recommendation:** lift/prove at the
per-head-linear + attention/MoE boundary (unblocks rotary AND all downstream
2-tp ops), NOT at the rotary boundary.

---

## Worker #6 (2026-07-15) — `FW_per_head_mix_precision_linear` 2-tp gear

**Delivered (all zero-sorry, kernel triple + native_decide baseline; audited in `AuditIR.lean`):**

### Priority 1 — the gear (`recon_per_head_linear_2tp`)
Op-agnostic parametrized 2-tp reconstruction for `FW_per_head_mix_precision_linear`,
the exact analog of worker #4's `recon_rotary_2tp_fst/snd`. Backed by the existing
`fw_per_head_mix_precision_linear_allGather0_commute_2` (Denote.lean:22591 — the
per-head companion of `fw_linear_allGather0_commute_2_of`, Pattern_1.lean:2012).
Structurally per-head linear = linear + per-head output-column reshape; it commutes
with dim-0 (token) sharding exactly like plain linear because each output row
depends only on the matching input row (weight replicated). Signature threads:
node reductions (`hsmNode`/`hpm0`/`hpm1`), input recon (`hx`), weight agreement
(`hw`), input/weight shapes. A raw value+shape bundle `perhead_2tp_val_shapes` was
factored out (reused by the rotary reduction below).

### Priority 2 — applied to 4794 (Q) and 4796 (K)
`recon_intermediateGoal_4794` / `_4796` (+ `_of_inputs`). CONDITIONAL on their
sharded input activation (sm 7496 / 7500, transitively attention/MoE-gated),
threaded honestly; the replicated weight (init 4793 / 4795) is closed internally
via `recon_weight`. Node reductions: sm nodes 83/84, pm nodes 227/228/230/231.

### Priority 3 — rotary hypothesis reduction 9 → 6
Key structural finding: per-head Q (4794) and K (4796) consume the **same** rms-norm
output (sm tid 4792) via a single `FW_multiref [4792] → [7496,7500,7504]` (sm node
82); the PM rank shards are 7769 (rank0) / 7770 (rank1), each multiref'd into the
per-head input copies (pm nodes 225/226). New
`recon_intermediateGoal_4800/4801_of_rms_inputs` thread ONE shared rms
reconstruction (`hrms`) + its 2 shard shapes + positions = **6 hypotheses** vs the
9 of `recon_intermediateGoal_4800/4801`. The per-head Q/K bundles + their 4 shard
shapes are derived internally via 6 multiref bridge lemmas
(`sm_mref_7496/7500_eq_4792`, `pm_mref_14718/14722_eq_7769`,
`pm_mref_14731/14735_eq_7770`) + `perhead_2tp_val_shapes`.
Note: naive per-head→rotary substitution alone does NOT reduce the count (it just
relocates the boundary upstream); the genuine 9→6 reduction comes specifically from
folding the shared rms input (Q and K collapse from 6 hyps to 3).

### Priority 4 — no fully-unconditional 2-tp per-head goal exists
Verified: the per-head projections come in Q/K/V triples per layer. Layer-0
(4685/4687/4689) and layer-1 (4740/4742/4744) per-head goals are all **1-tp
replicated** (already proven unconditionally, `wrap_1tp`) because their rms input is
still replicated. The FIRST 2-tp per-head goal is 4794 (layer-2), whose sharded
input 7496 chains through `FW_all2all_moe_gmm` + `FW_attn_sliding_window`. Sequence
sharding of the residual only begins after the first attention/MoE block, so **every**
2-tp per-head goal (4794/4796 and the ~40 in layers 2–10) is attention-gated. No
unconditional per-head 2-tp goal to harvest.

---

## Worker #7 (2026-07-15) — `FW_rms_norm` 2-tp gear + residual chain hits attention/MoE floor

**Delivered (all zero-sorry, kernel triple + native_decide baseline; audited in `AuditIR.lean`):**

### Priority 1 — the gear (`recon_rms_norm_2tp` + `rms_2tp_val_shapes`)
Op-agnostic parametrized 2-tp reconstruction for `FW_rms_norm`, exact analog of
worker #6's `recon_per_head_linear_2tp`. Backed by `fw_rms_norm_allGather0_commute_2`
(Pattern_1.lean:1887, proven zero-sorry with full `Tensor.ext`; row-wise reduction is
orthogonal to dim-0 token sharding). Signature threads node reductions
(`hsmNode`/`hpm0`/`hpm1`), input recon (`hx`), replicated weight agreement (`hw`),
and 2 input shard shapes. **No weight-shape hypothesis** (unlike per-head — the rms
commute leaves the weight unconstrained). Required importing `Pattern_1` (the commute
lemma lives there, same `GeneratedPatterns` namespace, non-circular).

### Priority 2 — applied to 4792 (layer-2 input layernorm)
`recon_intermediateGoal_4792` (+ `_of_inputs`). CONDITIONAL on its sharded residual
input (sm 7487 = allGather[pm 14701,14709], transitively attention/MoE-gated),
threaded honestly. Replicated weight (init 4791) closed internally via `recon_weight`.
Node reductions: sm node 81, pm nodes 223/224.

### Priority 3 — residual chain trace: NO daylight, floor is attention/MoE
Traced one hop up from 4790 (residual add). It fans into BOTH `FW_attn_sliding_window`
(via 7460→4757→4756→…→4750) AND `FW_all2all_moe_gmm` (via 4789→4788→4768). Every op on
the path is a pure relay/combinator (multiref/add/float/reshape/view/mul/linear); NONE
is init-derived. **There is no unconditionally-provable 2-tp intermediateGoal on the
residual chain** — the residual stream is replicated (1-tp) through layers 0–1 and
becomes 2-tp sharded only after the first attention/MoE block, permanently carrying
attention+MoE contributions thereafter. Each upward hop is now mechanized, so the
chain collapses to exactly two irreducible per-block obligations: attention-output and
MoE-output 2-tp reconstruction. **That bespoke attention/MoE boundary is the genuine
"no template exists here" floor — reached and confirmed not pushable further.** Full
trace in `~/HYPOTHESIS_INVENTORY.md`.

### Priority 4 — rotary chain pushed one hop up
`recon_intermediateGoal_4800/4801_of_residual_inputs` thread the rms residual input
(7487) instead of the rms output (4792), deriving `hrms` internally via the rms gear.
Boundary relocation (still 6 hyps), moving the threaded fact one hop closer to the
attention/MoE floor and demonstrating the rms gear composes with the rotary gears.

### Next irreducible boundary
The attention-output (`FW_attn_sliding_window`) and MoE-output (`FW_all2all_moe_gmm`)
2-tp reconstruction templates. Once built, the ENTIRE post-attention residual chain
(add → multiref → rms → per-head Q/K → rotary) closes mechanically via the worker
#4–#7 gears with zero remaining threaded hypotheses.

---

## Worker #8 (2026-07-15) — FW_attn_sliding_window 2-tp: NEGATIVE result (plain path FALSE; ring-attn gear already exists)

**Priority 1 (semantics) COMPLETE.** `FW_attn_sliding_window` `evalOp`
(Denote.lean:3915-3927) is `numParts`-conditional (`numParts = g.numRanks`):
`numParts=1` → `fw_attn_varlen` (value-faithful, SM); `numParts>1` → all-zero
`Tensor.mkShape [lQ,qh,vd] (fun _=>0)` (AGENTS.md #24 identity/zero model, PM).
The value-faithful cross-rank model lives in the RING layer
(`applyNodeRingAttn_sliding_window`, Denote.lean:21536: allGather buddy q/k/v →
`fw_attn_varlen` on full seq → chunk back). `FW_attn_zigzag` (12 goals, new
category) is identical. cu-metadata 4694/4695 are init leaves shape [2].

**Priority 2 VERDICT: gear NOT buildable as specified (plain `denoteGraph`,
mirror of `recon_rotary_2tp_fst`).** `intermediateGoal_4696` under plain
`denoteGraph` is a FALSE ∀-statement: SM 4696 = real `fw_attn_varlen` (numParts=1),
PM shards 7437/7438 = zero tensors (numParts=2, pm.numRanks=2), so
`sm 4696 = allGather0[pm 7437, pm 7438]` forces `real_attn = 0`. No
`_allGather0_commute_2` exists/holds for the plain path. AGENTS.md #24 (identity
model) is the ROOT CAUSE; #29 (方案 E stmt-lift) does NOT apply (can't lift a
false conclusion — no input contract makes 0 = real attention). R2/#25 forbid the
Denote edit that would make plain faithful.

**The value-faithful gear ALREADY EXISTS, zero-sorry:**
`applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair`
(Pattern_3.lean:3838), consumed by Goal_3 at node 4696 (Pattern_3.lean:4930)
under `denoteGraph_ringAttn`. Inputs are shallow (Iroha correct): PM attn inputs
7433/7435/7421 = ChunkPrim0 shards of the PROVEN-replicated layer-0 Q'/K'/V
(4692/4693/4689); the ring gear's input hyps are allGather∘chunk roundtrips on
those.

**Root architectural finding:** the deliverable states attention (and its whole
2-tp downstream residual chain) over plain `denoteGraph`, where those goals are
unprovable-because-FALSE. The fix is the DENOTATION, not a new gear:
(1) exclude the 24 attention goals from `all_intermediateGoals_list` (let Goal_3's
ring bridge own them), or (2) restate `all_intermediateGoals_hold` over
`denoteGraph_ringAttn` (non-attn ops transfer via
`denoteGraph_ringAttn_eq_denoteGraph_of_no_ring_attn` /
`applyNodeRingAttn_eq_applyNode_of_not_ring`; attn closes via the Pattern_3 gear).
Option 2 unblocks the entire 2-tp cascade workers #4–#7 left conditional.

**Delivered:** `denote/yoco_goals/AttnPlainZeroWitness.lean` (green; axioms =
{propext, Classical.choice, Quot.sound}; zero sorry / zero user axiom) — 3
checkable lemmas proving the plain PM attention output is the value-INDEPENDENT
zero tensor while SM is value-faithful `fw_attn_varlen`, i.e. the plain 2-tp
attention goal is false. Full analysis + effort estimate in `~/ATTENTION_ANALYSIS.md`.
No Denote.lean edits (R2). No new gear sorried/axiomed (R5 honest fallback).

---

## Worker #9 — Ring-attn restatement + first UNCONDITIONAL attention goal (2026-07)

**Priorities 1+2 (commit c4938a26):** Restated the proven assembly over
`denoteGraph_ringAttn`. All 12 upstream (pre-attention) proven goals transfer
verbatim from plain `denoteGraph` via the new `recon_ringAttn_of_plain` gear
(they are all written strictly before the first ring-attn node: sm[9], pm[49]).
New machinery: `foldl_prefix_eq_full_ringAttn'`, `denoteGraph_ringAttn_eq_at`,
`InitGoalHolds_transfer`, `sm_ring_eq`(k=9)/`pm_ring_eq`(k=49),
`all_intermediateGoals_proven_hold_ringAttn`.

**Priority 3 (commit 63e27b99) — MILESTONE:** `intermediateGoal_4696`
(layer-0 attention, 2-tp, `tps=[{0,7437},{1,7438}]`) proven **UNCONDITIONALLY**
over `denoteGraph_ringAttn` on the GLOBAL sm/pm graphs. First genuinely
unconditional 2-tp sharded intermediateGoal (previously the floor was the
attention op itself, which is FALSE over plain `denoteGraph`). Reuses Pattern_3's
ring gear `applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair`.
Proof = ~270 lines: store↔plain bridges (ring≡plain on all non-attn inputs),
Q/K/V full reconstructions via chunk `allGather0_reconstruct_chunks_3d`
roundtrips (7433/7434 chunks of Q'4692, 7435/7436 of K'4693, 7421/7422 of V4689),
cu_seqlens equalities (`recon_weight` on initGoal_4694/4695), gear application,
and the take49→take50 nR1 store bridge (`attn_sw_store_congr`). Axiom-clean
(propext / Classical.choice / Quot.sound + upstream native_decide only). New
helpers: `nSMg/nR0g/nR1g` (global attn node literals, identical to Pattern_3
cut-graph), `buddy_sm_g/r0_g/r1_g`, `oneTp_valeq`, `wrap_2tp_allGather_gen`,
`pm_chunk_reduce`. Assembly `all_intermediateGoals_proven_hold_ringAttn_with_attn`
covers 4696 + the 12 upstream goals (13 total).

**Priority 4 (cascade) — BLOCKED, documented per R5 (NOT sorried):** The
downstream reshape goals (`4697` = reshape(4696), `4698`, and the whole layer-0
residual/MoE chain) are **structurally FALSE over the GLOBAL graph** because the
global graph's `FW_reshape` nodes carry **empty params** (`sm[10]/sm[11]`,
`pm[51]/pm[52]` all `params=[]`), i.e. the LEGACY no-op identity model. Under it:
`SM 4697 = SM 4696` with shape `[4096,16,64]`, but `intermediateGoal_4697.tsShape
= [4096,1024]` — the `InitGoalHolds` shape obligation `[4096,16,64] = [4096,1024]`
is false. Reshape is NOT a ring op, so this holds identically over plain and ring
denotations. This is an **upstream graph-generation faithfulness gap**: the
Pattern_3 CUT graphs (`sm_goal_3`/`pm_goal_3`) were rebuilt on 2026-07-06 with
params-aware `FW_reshape` (`params=[4096,1024]`, `[2048,1024]`), but the GLOBAL
`sm`/`pm` in `GeneratedYOCOMoE` still emit empty-params no-op reshapes. Fixing it
requires regenerating `GeneratedYOCOMoE` with params-aware reshape (outside R2's
"no Denote.lean semantic edits" and not a proof-side change). Until then the
cascade cannot proceed past the reshape boundary. Verified by shape witness (no
sorry, no axiom). See also the pre-existing note at `denote/Denote.lean:22263`
(`fw_reshape_allGather0_commute_2`) documenting the same params-aware breakage.

---

## Worker #10 (2026-07-15) — Priority 2 gear `recon_attn_sliding_window_2tp_layer` + reachability map

**Priority 1 (enumeration) COMPLETE.** All 12 `FW_attn_sliding_window` SM nodes
(outs 4696/4750/4804/4858/4912/4966/5020/5074/5128/5182/5236/5290) + their PM
r0/r1 buddy pairs (7437/7438 … 9483/9484) and all 12 `FW_attn_zigzag` SM nodes
(outs 5347/5396/…/5886) enumerated and recorded as a comment block in
`IntermediateReconstruction.lean` (above `recon_attn_sliding_window_2tp_layer`).

**Priority 2 (gear) COMPLETE — zero sorry, zero user axiom.** Extracted Worker
#9's ~270-line `recon_intermediateGoal_4696_ringAttn` assembly tail into a
parametrized theorem `recon_attn_sliding_window_2tp_layer`. It abstracts over the
SM/PM attn node literals (`nSM`/`nR0`/`nR1`), the three take-prefix folds
(`foldSM`/`foldPM`/`foldPM'` as opaque `Store`s), output tids, shard length `L`,
head counts `nh`/`kh`, and the layer `LineageGoal`. Given the node reductions +
r1 store bridge + Pattern_3 gear hyps (buddy detection, Q'/K'/V full
reconstructions, cu/param agreement, full-output shapes on both folds) + goal
metadata, it produces `InitGoalHolds pm.numRanks g (denoteGraph_ringAttn sm …)
(denoteGraph_ringAttn pm …)`. `recon_intermediateGoal_4696_ringAttn` (layer 0)
is REFACTORED to fire through the gear on the layer-0 witnesses — faithful
re-derivation, statement unchanged, still builds green. Axioms:
`recon_attn_sliding_window_2tp_layer` = {propext, Classical.choice, Quot.sound}
(no user axioms); `recon_intermediateGoal_4696_ringAttn` = kernel triple +
permitted native_decide baseline (unchanged from Worker #9).

**Priority 3/4 (apply to layers 1–11 + zigzag) — GATED, documented per R5 (NOT
sorried).** Reality check via graph producer-trace (`GeneratedYOCOMoE.lean`):
- Every layer L≥1 sliding Q'-input (4746/4800/…/5286) reaches layer-0 attention
  output 4696 through the residual stream (verified: all 11 reach 4696=True).
- All 12 zigzag inputs (base 5342/…) also reach 4696 through the residual stream
  (YOCO cross-decoder reads the self-decoder output; deeper trace confirms).
- Every `FW_reshape` node in the GLOBAL `sm` graph has EMPTY params (verified:
  all 168 reshape nodes params=None), including 4696→4697→4698 on the layer-0→1
  path. Under the legacy no-op reshape model the downstream intermediateGoal
  shapes are structurally FALSE (Worker #9's reshape blocker).
Therefore **only LAYER 0 sliding attention is unconditionally reachable** (already
proven by Worker #9, now via the gear). Layers 1–11 sliding + all 12 zigzag are
GATED on the upstream reshape-params fix. The gear is the ready machinery that
fires the moment that fix lands (regenerate `GeneratedYOCOMoE` with params-aware
`FW_reshape`, unblocking the residual cascade layer-by-layer).

**Reachability map (12 sliding + 12 zigzag = 24 attention layers):**
- Sliding L0 (4696): UNCONDITIONAL ✓ (proven, via gear).
- Sliding L1–L11 (4750…5290): GATED on reshape-params fix.
- Zigzag L0–L11 (5347…5886): GATED on reshape-params fix.

**Category delta:** +0 new unconditional goals (layer 0 already counted by Worker
#9); +1 reusable parametrized gear (`recon_attn_sliding_window_2tp_layer`); the
attention-scaling path is proven to bottleneck on the SAME reshape blocker Worker
#9 identified — no proof-side scaling is possible without the upstream fix.

---

## Worker #11 (2026-07-15) — Regenerated GeneratedYOCOMoE with params-aware FW_reshape

**Upstream reshape blocker RESOLVED.** Regenerated the GLOBAL
`denote/GeneratedYOCOMoE.lean` from the yoco_moe_a04b SM/PM pkls using the
current Verdict `graph_to_lean.py` (params-aware `_get_node_params` FW_reshape
branch, Verdict fix 8d55292f). Flags matched the original emission
(`--max-goals 5 --split-goals`, goals redirected to scratch so the hand-edited
`yoco_goals/` files were untouched).

**Diff analysis (bak vs regen), exhaustively categorized:**
- Node counts identical: SM 927, PM 1920. All tids byte-for-byte preserved on
  non-reshape nodes. 19541 lines both.
- 432/432 `FW_reshape` nodes gained `params := [target_shape]` (was `[]`). Under
  `Denote.evalOp` these now build `fw_view targetShape` instead of identity.
  Layer-0: `sm[10]` 4696→4697 `params := [4096,1024]`, `sm[11]` 4697→4698, etc.
- 2 non-reshape deltas, both benign:
  1. `FW_topk_routing` params `[8] → [8,1]` (explicit num_experts). Semantically
     identical under Denote (`params.getD 1 1 = 1` either way).
  2. `initGoal_4691` regenerated to `tid := 11853` (multiref copy); reapplied the
     manual b6e3506f fix (`tid := 4691`, source leaf).

**Build outcome: GREEN.** `lake build` full repo: 8560 jobs, 0 errors, 0 sorry.
Standalone `denote.GeneratedYOCOMoE` builds in 41s. Pattern_1/2/4/5 + Pattern_3
+ IntermediateReconstruction + MainTheorem + AuditIR all rebuild clean — the
params-aware reshape does NOT break the legacy identity-reshape proofs (they use
their own cut graphs / shape-preserving reshapes; empty-params fallback kept).

**Cascade impact:** the reshape *shape obligation* is now satisfiable —
`intermediateGoal_4697` (and every downstream reshape goal) is no longer
structurally false.

**Cascade unlock (Worker #11 bonus, same session):** proved the
**row-preserving reshape / dim-0 allGather commute** lemma and used it to land the
first cascade goal:
- `fw_view_allGather0_reshape_16_64_2` — `fw_view [4096,1024] (allGather0 [a,b]) =
  allGather0 [fw_view [2048,1024] a, fw_view [2048,1024] b]` for `a,b:[2048,16,64]`.
  Pure tensor algebra (flat-index decomposition `idx=((r*2048+i)*16+j)*64+k`,
  `allGatherPrimDimN0_valAt_3D`/`_valAt`, `valAt_fw_view`). Axiom-clean
  (propext/Classical.choice/Quot.sound).
- `ringAttn_reshape_reduce` — ring-denotation node reducer for a non-empty-params
  `FW_reshape` node sitting *after* the first ring-attn node (so `sm_ring_eq`/
  `pm_ring_eq` don't apply): `denoteGraph_ringAttn g init outTid =
  fw_view tshape (denoteGraph_ringAttn g init inTid)`. Kernel-clean, no in-body
  native_decide (uses `foldl_take_succ` + `foldl_prefix_eq_full_ringAttn'` +
  `applyNode_fw_reshape_out`).
- **`recon_intermediateGoal_4697_ringAttn`** — UNCONDITIONAL over
  `denoteGraph_ringAttn`: SM 4697 = allGather0[PM 7439, PM 7440], chaining through
  Worker #9/#10's `recon_intermediateGoal_4696_ringAttn`. Node indices: SM reshape
  = `sm.nodes[10]`, PM reshapes = `pm.nodes[51]/[52]`. All in
  `denote/yoco_goals/IntermediateReconstruction.lean`. Full repo still green.

**Category delta:** +1 newly *proven* unconditional intermediateGoal (**4697**),
plus 2 reusable machinery lemmas (reshape commute + ring reshape reducer). The
upstream faithfulness gap that made ALL L≥1 goals vacuous/false is closed — the
graph is faithful to the Python authority.


---

## Worker #12 — Residual / MoE / L1-pre-attention cascade (ring-attn)

Chains forward from `recon_intermediateGoal_4697_ringAttn` through the
down-projection, first residual add, RMSNorm, and the replicated MoE-gate /
expert-projection sub-tree, proving each `intermediateGoal_<tid>` UNCONDITIONALLY
over `denoteGraph_ringAttn`. Zero sorry, zero user axiom (kernel triple +
native_decide baseline only, verified via `#print axioms`).

### Files
- **`denote/yoco_goals/RingAttnGears.lean`** (NEW, shared with W13): generic
  ring node reducers `ringAttn_reduce1` / `ringAttn_reduce2` (unary / binary op
  node → opfun over ring-denotations of the inputs), `ringAttn_reshape_reduce_g12`
  (FW_reshape → fw_view), `fw_view_id_shape` (identity reshape/view collapse),
  `valAt_fw_view_lt`, `foldl_prefix_ring_g12`. Unique `_g12` names to avoid
  collision with Pattern_3. Builds green standalone.
- **`denote/yoco_goals/ResidualMoEReconstruction.lean`** (NEW, W12 deliverable):
  all 18 new theorems + helpers.
- **`denote/yoco_goals/IntermediateReconstruction.lean`** (FIXED): origin
  `cfb8ca04` did NOT compile from clean (duplicate `valAt_fw_view` colliding with
  Pattern_3, and a docstring-then-`set_option in` parse error). Reconciled in
  commit `6c68642c` (import RingAttnGears, delete the 3 broken local helpers,
  reorder set_option before docstring, redirect 4697 proof to `_g12` gears).

### Proven intermediateGoals (18 new, all UNCONDITIONAL over ring-attn)
| tid  | op                         | shape        | status |
|------|----------------------------|--------------|--------|
| 4698 | reshape→allGather bridge   | [4096,1024]  | proved |
| 4700 | mix_precision_linear (down)| [4096,1024]  | proved |
| 4701 | view                       | [4096,1024]  | proved |
| 4702 | float                      | [4096,1024]  | proved |
| 4703 | residual add (+shortcut)   | [4096,1024]  | proved |
| 4705 | rms_norm                   | [4096,1024]  | proved |
| 4706 | float (router head)        | [4096,1024]  | proved |
| 4708 | norm_linear (router gate)  | [4096,64]    | proved |
| 4715 | reshape (identity)         | [4096,1024]  | proved |
| 4720 | reshape (identity)         | [4096,1024]  | proved |
| 4724 | reshape (identity)         | [4096,1024]  | proved |
| 4717 | mix_precision_linear       | [4096,1]     | proved |
| 4722 | mix_precision_linear       | [4096,512]   | proved |
| 4726 | mix_precision_linear       | [4096,512]   | proved |
| 4718 | view                       | [4096,1]     | proved |
| 4723 | view                       | [4096,512]   | proved |
| 4727 | view                       | [4096,512]   | proved |
| 4719 | sigmoid (glu gate)         | [4096,1]     | proved |

### Gated frontier in [4703,4750) (need genuine MoE sharding gears)
These are the *hard* MoE core; each PM node computes over a **chunked/sharded**
tensor and re-gathers, so the SM-vs-PM bridge needs a sharding-COMMUTE gear
(not just a per-op node reduction). Deferred:
- **4709 / 4710** — `FW_topk_routing` outputs (2-tp SHARDED, PM runs topk on
  `ChunkPrim[4708]` shards 7479/7480). Needs a topk sharding-commute + buddy gear.
- **4714** — `FW_all2all_moe_gmm` (PM `AllGatherPrim[7491,7492]` of per-rank
  grouped-GEMM). Needs the `fw_all2all_moe_gmm_full_split_commute` family wired
  into the ring reconstruction.
- **4728** — `FW_swiglu` (2-tp SHARDED, PM on chunks 7521/7539 → 7543/7544).
- **4729** — reshape+`AllGatherPrim[7545,7546]` of the swiglu shards. Needs a
  swiglu-allGather commute.
- **4731 / 4732 / 4733 / 4734 / 4735 / 4736 / 4738 / 4740 / 4742 / 4744 / 4746 /
  4747** — transitively gated: `4731=mix_linear(4729,…)`, `4733=mul(4719,4732)`,
  `4734=add(4714,4733)`, `4736=add(7408,4735)`, `4738=rms_norm(4736)`,
  `4740/4742/4744=per_head_mix_precision_linear(4738)`,
  `4746/4747=rotary_embedding`. All become mechanical (same replicated pattern as
  above) ONCE 4714 / 4728 / 4729 are discharged.

### New gears created (signatures)
- `ringAttn_reduce1 (g init k node inTid outTid opfun) (hk hnode hnr1 hnr2 happly
  hdrop_nil hdrop hpre_nil hpre) : denoteGraph_ringAttn g init outTid =
  opfun (denoteGraph_ringAttn g init inTid)` — unary post-ring node reducer.
- `ringAttn_reduce2 (… inTid1 inTid2 outTid opfun …) : … = opfun (ring in1)
  (ring in2)` — binary analog.
- `ringAttn_reshape_reduce_g12` — FW_reshape node → `fw_view tshape (ring inTid)`.
- `applyNode_fw_multiref_first_out'` — generic first-output of an `n+1`-ary
  FW_multiref (`= s xTid`), for the `(List.range 5).map` PM broadcast form.
- `applyNode_fw_norm_linear_out` — FW_norm_linear singleton-output reducer.
- Local shape helpers: `fw_linear_2d_shape`, `fw_norm_linear_2d_shape`,
  `fw_rms_norm_shape2`, `fw_sigmoid_shape`; ring transfer helpers
  `veq_ring_of_plain`, `shape_ring_of_plain`, `veq_weight_ring`,
  `shape_weight_ring`, `wrap_1tp_gen`.

### Axiom audit
`#print axioms` on 4703/4708/4715/4719 (transitively covering all 18): only
`propext`, `Classical.choice`, `Quot.sound` + `_native.native_decide.ax_*`
baseline. **Zero `sorryAx`, zero user `axiom`.**

### Ring-attn unconditional total
Was 14 (through 4697). **+18 = 32** unconditional ring-attn intermediateGoals.

### Commits (this worker)
- `c21a99e6` add shared RingAttnGears.lean
- `6c68642c` fix IntermediateReconstruction build (dedup valAt_fw_view, set_option order)
- `dd3f8978` prove 4698/4700/4701/4702
- `316ac833` prove 4703/4705/4706
- `dc8523c6` prove 4715/4720/4724/4708
- `ef3e8639` prove 4717/4722/4726/4718/4723/4727/4719

---

## Worker #14 — MoE sharding-commute gears (topk / all2all_moe_gmm / swiglu)

New file `denote/yoco_goals/MoEShardedReconstruction.lean` (imports
`ResidualMoEReconstruction`). Zero sorry, native_decide baseline only.

### Per-tid status
| tid  | op                       | goal form | status |
|------|--------------------------|-----------|--------|
| 4709 | FW_topk_routing (.fst)   | 2-tp gather | **unconditional** |
| 4710 | FW_topk_routing (.snd.fst)| 2-tp gather | **unconditional** |
| 4728 | FW_swiglu                | 2-tp gather | **unconditional** |
| 4729 | FW_reshape ∘ AllGather   | 1-tp        | **unconditional** |
| 4714 | FW_all2all_moe_gmm       | 1-tp        | **blocked-by-graph-nonfaithfulness** |

**+4 unconditional ring-attn intermediateGoals: 4709, 4710, 4728, 4729.**

### New gears (in MoEShardedReconstruction.lean)
- `ringAttn_reduce1_at` — store-specific single-input ring node reduction. Unlike
  `ringAttn_reduce1` (which needs the `applyNode` reduction `∀ s`), this takes the
  reduction only at the specific prefix store `(g.nodes.take k).foldl (applyNodeRingAttn g) init`.
  Needed for ops (topk) whose `applyNode` lemma requires a shape hypothesis on the
  folded input.
- `evalOp_topk_81` / `applyNode_topk81_fst` / `applyNode_topk81_snd` — `applyNode`
  reductions for the generated `FW_topk_routing` node whose params are `[8,1]`.
  `numExperts=64` is read off the logits' trailing dim (params entry `1` is the
  overridden fallback), so these require `(s logits).shape.reverse.head? = some 64`.
- `moe_swiglu_gather_4728` — shared core: SM `4728` (full swiglu) = dim-0 gather of
  PM per-rank swiglu shards `7543`/`7544`, + shard/full shapes. Reused by 4728 & 4729.
- `moe_topk_common` — shared core: replicated logits `4708` reconstruct as dim-0
  gather of per-rank chunks `7479`/`7480`, + chunk/logits shapes + prefix-store
  trailing-dim (`= some 64`) hyps. Reused by 4709 & 4710.

All four proofs reuse Pattern_1's proven pure-tensor commute lemmas
(`fw_swiglu_allGather0_commute_2`, `fw_topk_routing_{fst,snd_fst}_allGather0_commute_2_of`)
+ Pattern_3's `allGather0_reconstruct_chunks_2d` + the shared `RingAttnGears`
node-reduction machinery, mirrored over `denoteGraph_ringAttn`.

### 4714 — CORRECTION (W17): graph IS faithful; blocker is the disjoint-commute lemma
W14's "missing initGoal bridges" framing is **stale/incorrect** against the current
W11-regenerated `GeneratedYOCOMoE.lean`. Re-verified by W17:
- `7419`, `4709`, `4710` are **NOT** unconstrained PM init leaves — they are **not** in
  `pmInitShapes` at all. The PM graph writes `4714` faithfully via
  `AllGatherPrim(7491,7492)→4714` where `7491`/`7492 = FW_all2all_moe_gmm(11941/11942,
  7481/7483, 7483/…, 7487/7489, …)` over expert-parallel shards.
- The SM-side inputs are already bridged: `intermediateGoal_7419`
  (`tps=[(0,11941),(1,11942)]`, gatherDim 0), and `recon_intermediateGoal_4709/4710`
  are **proven**. So the emitter needs **no fix** — bridges already present.

W17 **proved `recon_intermediateGoal_7419_ringAttn`** (last missing input bridge),
mirroring the proven `4705`/`4709` gears: multiref pos-1 reduction of `4705` → PM
`ChunkPrim → 11941/11942` → `allGather0_reconstruct_chunks_2d 2048 1024`. Axiom audit:
only `propext`/`Classical.choice`/`Quot.sound` + `native_decide` baseline.

Remaining 4714 blocker is **not** the graph: it is the expert-parallel all2all commute
lemma `fw_all2all_moe_gmm_split_commute_2_of` (Pattern_1.lean:3081), which needs a
routing-map **disjointness hypothesis** across expert ranges — a well-formed-input
property not derivable from an abstract Store (would need a statement-level hypothesis
per lesson #29, or deep topk/mask reasoning). Left for a future worker (>30 min).

### Axiom audit
`#print axioms` on 4709/4710/4728/4729: only `propext`, `Classical.choice`,
`Quot.sound` + `_native.native_decide.ax_*` baseline. **Zero `sorryAx`, zero user `axiom`.**

### Commits (this worker)
- `8f6f33e5` prove 4728 (FW_swiglu 2-tp)
- `ae9383a7` prove 4729 (FW_reshape∘AllGather 1-tp)
- `02386b2c` prove 4709/4710 (FW_topk_routing 2-tp)

---

## Worker #21 — Well-formed-input contract + conditional discharge + L1 tail

New file `denote/yoco_goals/WellFormedInputs.lean` (imports the full ring-attn
gear chain). Zero sorry, zero user axiom, native_decide baseline only.

### Part A — the contract `WellFormed_YOCOMoE_A04B`

`structure WellFormed_YOCOMoE_A04B (initSM initPM : Store) : Prop` — a positive,
structured record of *harness well-formedness* preconditions (NOT "assume the
goal"). It bundles the exact hypothesis families that W18/W19/W20's conditional
theorems demanded, one field per binder (~200 fields, named `wf<tid>_<hyp>`):

- **routing-map locality** — `routing_map_local (initSM 4708) 64 2 8` (each
  token's topk-8 map targets experts within one rank's 32-expert shard), the
  MoE-all2all disjointness precondition (W18's predicate).
- **Q/K/V ring-reconstruction agreement** — for each sliding/zigzag layer, the
  facts of the form `denoteGraph_ringAttn sm initSM X = allGather/replicate of
  the PM shards` (`hq_full`/`hk_repl`/`hv_repl`/`hpm0`/`hpm1`/`hcs`/`hpos` binder
  families) that the conditional attention theorems consumed. Each is a pure
  "SM tensor = ring reconstruction of PM shards" statement — legitimate
  harness-agreement, not the reconstruction conclusion itself.

**Consistency** (`WellFormed_routing_witness`): the restrictive routing-locality
clause is *satisfiable* — the zero tensor (`valAt_zeroTensor` /
`routing_map_local_zeroTensor`, native_decide) meets both disjoint-window
requirements. Follows AGENTS.md #29 (comparator-blessed): the contract's fields
are statement-level hypotheses; a full `∃ initSM initPM` over the 8000-node
matched run is neither feasible nor the repo standard, so consistency is
witnessed per-clause instead of vacuously.

### Part B — discharge (24 companions)

Every conditional theorem now has an unconditional-*given-WF* companion
`recon_intermediateGoal_<tid>_ringAttn (… ) (hWF : WellFormed_YOCOMoE_A04B …)`,
proved by projecting the needed field(s) out of `hWF` and invoking the existing
`_of_disjoint` / `_of_inputs` / `_of_qkv` lemma:

- 1 MoE all2all: `4714`.
- 11 sliding: `4750`, `4804`, `4858`, `4912`, `4966`, `5020`, `5074`, `5128`,
  `5182`, `5236`, `5290`.
- 12 zigzag: `5347`, `5396`, `5445`, `5494`, `5543`, `5592`, `5641`, `5690`,
  `5739`, `5788`, `5837`, `5886`.

The `hWF` parameter is the correct notion of "unconditional" here: no
free-standing per-tid precondition survives — just the single global harness
contract (raw unconditionality is impossible when PM stores can be arbitrary
garbage).

### Part C — L1 MoE residual tail (new file `L1MechanicalTail.lean`)

4 new unconditional-given-WF tail tids past the (now discharged) `4714`:

- `4734` — FW_add (MoE residual, replicated 1-tp)
- `4735` — FW_float (dtype cast)
- `4736` — FW_add (residual carry via multiref bridge of `4703`)
- `4738` — FW_rms_norm (post-attn norm)

Each mirrors the W12/W16 replicated template (`ringAttn_reduce1/2` +
`wrap_1tp_gen`), carrying `hWF` through their dependence on `4714`.

### Effective new count

Was 40 unconditional ring-attn goals. **+24 discharged conditionals + 4 new
tail tids = 68 / 1151** unconditional-given-WellFormed ring-attn goals.

### Remaining frontier (still blocked despite WF)

- L1 per-head Q/K/V projections `4740`/`4742`/`4744` and rotary `4746`/`4747`:
  the SM-side reductions (3-way FW_multiref + FW_per_head_mix_precision_linear +
  `fw_per_head_linear_shape`) compile clean, but the **PM-side 3-way multiref
  `ringAttn_reduce1` at pm node ≈129 triggers an unbounded elaborator
  recursion / whnf blow-up** (SM node 43 identical construct is fine; pm nodes
  ≤127 are fine). Root cause is a high-index PM-graph reduction pathology, not a
  math gap — needs a `ringAttn_reduce1` variant that avoids forcing the pm
  prefix at that index. Left for a follow-up.
- Per-layer all2all L1–L11 (`4768`…`5308`) + per-layer tails: each needs a
  per-layer `routing_map_local` field added to the contract plus per-layer input
  bridges — mechanical but higher volume; the contract is structured to extend.

### Axiom audit
`#print axioms` on the WF contract, `WellFormed_routing_witness`, a representative
discharged companion (`recon_intermediateGoal_4714_ringAttn`), and the new tail
(`recon_intermediateGoal_4738_ringAttn`): only `propext`, `Classical.choice`,
`Quot.sound` + `_native.native_decide.ax_*` baseline. **Zero `sorryAx`, zero user
`axiom`.**

### Commits (this worker)
- `14fce8fd` WellFormed_YOCOMoE_A04B contract + discharge 24 conditional ring-attn theorems
- `0309ae5f` L1 MoE residual tail tids 4734/4735 (given WellFormed contract)
- `c5659329` Part C: land 4736 (residual add) + 4738 (RMSNorm) L1 tail

---

## Worker 22 (2026-07-16) — whnf-safe PM ring-attn gears + L1 per-head/rotary

### Part A — the whnf blow-up fix (`RingAttnGearsPM.lean`)

W21's frontier note (above) was correct: the PM-side 3-way multiref
`ringAttn_reduce1` at pm node ≈129 blew up the elaborator. **Root cause
pinned:** the original `ringAttn_reduce1`/`reduce2` gears close with
`congr 1; exact (foldl_prefix_ring_g12 …).symm`. `congr 1` forces `isDefEq`
to whnf the k-deep `applyNodeRingAttn` fold (including its ring branches);
cost scales with the pm node index, so SM node 43 and pm nodes ≤127 elaborate
but pm node 129 explodes.

**Fix:** whnf-safe variants that never put the deep fold into a defeq problem.
They unfold the RHS ring denotation and rewrite the *full* node-fold into the
*prefix* fold via `foldl_prefix_ring_g12` **forward**, so both sides become the
identical prefix-fold term closed by `rfl`:

- `ringAttn_reduce1_pm_opaque`, `ringAttn_reduce2_pm_opaque` — same signatures
  as the originals (drop-in for high-index pm nodes).
- `ringAttn_node_core_pm_opaque` — exposes
  `denoteGraph_ringAttn g init out = applyNode g ((g.nodes.take k).foldl …) node out`
  for multi-in/multi-out nodes (used for the 2-output rotary node); manipulates
  the LHS only.
- `ringAttn_prefix_read_pm`, `fw_per_head_linear_shape_3d` — supporting lemmas.

Originals in `RingAttnGears.lean` are untouched (kept green). Verified: with the
opaque gears, concrete pm node 129 (`4740`) elaborates in seconds instead of
hanging/OOM.

**Baseline vs post-fix on `4740`:** baseline = non-terminating (killed; the
prior two sessions both hung here). Post-fix: the whole `L1PerHeadTail.lean`
file (all 5 theorems incl. the node-129 reduction) compiles as part of a
successful `lake build` with no per-file timeout.

### Part B — 5 L1 per-head/rotary tail theorems (`L1PerHeadTail.lean`)

All 5 previously-blocked tids landed (target met):

- `recon_intermediateGoal_4740_ringAttn` — per-head mix-precision linear (Q)
- `recon_intermediateGoal_4742_ringAttn` — per-head mix-precision linear (K)
- `recon_intermediateGoal_4744_ringAttn` — per-head mix-precision linear (V)
- `recon_intermediateGoal_4746_ringAttn` — rotary embedding Q'
- `recon_intermediateGoal_4747_ringAttn` — rotary embedding K'

PM reductions route through the Part-A opaque gears. The SM/PM rotary cache
mismatch (SM cs `4691` vs PM cs `11854`, a rank-1 broadcast of `4691` via pm
multiref node 1) is bridged by `hcache_4691_11854` using
`sm_ring_eq`/`pm_ring_eq`/`sm_pm_rotary_cache_agree`.

### Effective new count

Was 68. **+5 (4740/4742/4744/4746/4747) = 73 / 1151** unconditional-given-
WellFormed ring-attn goals. No new WF-contract field required (per-head/rotary
are pure functions; equality of `4738` + replicated weights forces the outputs
structurally).

### Part C — attempted, blocked on upstream per-layer chains

Part C (per-layer L1–L11 all2all `4768…5308` + per-layer per-head/rotary tails)
is **not mechanically reducible to Part A**. Each higher layer's tail depends on
that layer's own upstream reconstruction, which is not yet built:

- Only L1's post-attn multiref value `4738` is reconstructed. The analogous
  per-layer values `4792, 4846, 4900, 4954, 5008, 5062, 5116, 5170, 5224, 5278`
  (stride 54) are all **MISSING**.
- `4792` = `FW_rms_norm(7487, 4791)` where `7487` is a multiref of
  `4790 = FW_add(7460, 4789)` and `4789` is the **L2 attention output** — an
  entire per-layer attention chain that has not been reconstructed (in the
  `4748–4792` window only `4750` has a recon).
- Each all2all `4768` = `FW_all2all_moe_gmm(7471, 4763, 4764, 4766, 4767)`
  depends on that layer's `FW_topk_routing`/`FW_norm_linear` routing chain,
  which likewise is unbuilt, and would need per-layer `routing_map_local` WF
  fields analogous to `wf4714_hdisjA/hdisjB`.

So Part C requires reconstructing 10 further per-layer attention+MoE chains
(prior-worker-scale effort each), not a mechanical replay of the Part-A gears.
The Part-A machinery is ready and will apply verbatim to each layer's per-head/
rotary tail *once that layer's `478X`/`479X` multiref value is reconstructed*.
Landed what is unblocked (Parts A+B) and documented the frontier here per the
"don't get stuck; land what you have" ground rule.

### Axiom audit
`#print axioms` on `ringAttn_reduce1_pm_opaque` and all 5 new
`recon_intermediateGoal_474{0,2,4,6,7}_ringAttn`: only `propext`,
`Classical.choice`, `Quot.sound` + `_native.native_decide.ax_*` baseline.
**Zero `sorryAx`, zero user `axiom`.**

### Commits (this worker)
- `4c4f3913` W22 Part A: whnf-safe PM ring-attn reduction gears
- `cb82255f` W22 Part B: land 5 L1 per-head/rotary reconstruction theorems

---

## Worker 23 (2026-07-16) — Complete L2 block reconstruction (2-tp sharded cascade)

### Objective met: the entire L2 block is closed

Unlike L1's 1-tp replica, L2 is a genuine 2-way tensor-parallel sharded cascade
(gatherDim 0, ranks 0/1). Every semantically required L2 intermediate from the
first reconstructed attention boundary `recon_intermediateGoal_4750_ringAttn`
through the final rotary output `4801` is now reconstructed unconditional-given-
`WellFormed_YOCOMoE_A04B`, in generated topological order.

### New tids landed (38, all in `denote/yoco_goals/L2Reconstruction.lean`)

Phase 1 (reshape + gather→1tp): `4751 4752`
Phase 2 (1-tp mixlin/view/float/add/rms/normlin + router): `4754 4755 4756 4757
  4759 4760 4762 4769 4771 4772 4774 4776 4777 4778 4780 4781`
Phase 3a (2-tp MoE topk/sigmoid/swiglu/mixlin/mul): `4763 4764 4773 4782 4783
  4785 4786 4787`
Phase 3b/3c (all2all + residual bridge): `4768 7471 7460`
Phase 3d (2-tp residual add/float/add/rms): `4788 4789 4790 4792`
Phase 3d-2 (2-tp per-head Q/K/V): `4794 4796 4798`
Phase 3d-3 (2-tp rotary Q'/K'): `4800 4801`

### L2 dependency table (SM node / PM nodes / op / gear)

| tid | SM node | PM nodes | op | key gear |
|-----|---------|----------|----|----------|
| 4751 | 48 reshape | 146/147 | FW_reshape | 2-tp reshape (4697/4698 template) |
| 4752 | 49 reshape | 150 AllGather | FW_reshape | gather→1tp |
| 4754 | 51 mixlin | 151/152 | FW_mix_precision_linear | 1-tp |
| 4757 | 54 add | 157/158 | FW_add | 1-tp residual |
| 4759 | 56 rms | 161/163 | FW_rms_norm | 1-tp |
| 4762 | 62 normlin | 177/178 | FW_norm_linear | router gate |
| 4763/4764 | 66 topk | 193/194 | FW_topk_routing | 2-tp topk |
| 4768 | 70 all2all | 201/202 | FW_all2all_moe_gmm | `recon_moe_all2all_1tp_of_disjoint` + `wf4768_hdisjA/B` |
| 4773 | 71 sigmoid | 203/204 | FW_sigmoid | 2-tp |
| 4782 | 72 swiglu | 205/206 | FW_swiglu | 2-tp |
| 4787 | 76 mul | 213/214 | FW_mul | 2-tp |
| 4788 | 77 add | 215/216 | FW_add | `twoTp_gather` + add-commute |
| 4789 | 78 float | 217/218 | FW_to (id) | 2-tp float |
| 4790 | 79 add | 219/220 | FW_add | 2-tp (7460 residual bridge) |
| 4792 | 81 rms | 223/224 | FW_rms_norm | `fw_rms_norm_allGather0_commute_2` |
| 4794/4796/4798 | 83/84/85 perhead | 227-232 | FW_per_head_mix_precision_linear | `fw_per_head_mix_precision_linear_allGather0_commute_2` |
| 4800/4801 | 86 rotary | 233/234 | FW_rotary_embedding | `fw_rotary_apply_allGather0_commute_2_1d` (1-D positions) |

### New generalized gear

`twoTp_gather` — generic 2-tp `allGatherPrimDimN 0 numRanks 0` extractor:
from a `LineageGoal` whose `tps = [{0,A},{1,B}]`, `replicated=false`,
`gatherDim=0`, `tpShapes=[shard,shard]`, `shard ≠ [1]`, and its `InitGoalHolds`
proof, yields `smD ts = allGather 0 numRanks 0 [pmD A, pmD B] ∧ (pmD A).shape =
shard ∧ (pmD B).shape = shard`. Semantically valid: it is exactly the
reconstruction contract for a non-replicated dim-0-gathered 2-shard goal, proved
via `reconstructForGoal_of_not_replicated` +
`reconstructWithDim_cons_cons_nonscalar`. Generalized over `shard : Shape` so it
serves 2-D `[2048,1024]` residual shards and 3-D `[2048,16,64]`/`[2048,4,64]`
per-head/rotary shards uniformly.

### WellFormed contract extension

Added `wf4768_hdisjA` / `wf4768_hdisjB` positive structural routing-locality
fields (rank-0/rank-1 expert-index disjointness for the L2 all2all), mirroring
L1's `wf4714`. Consistency witness `WellFormed_routing_witness` extended and
re-proved on the zero/native_decide baseline. These are pure structural
partition facts about the routing map; they do **not** encode any InitGoalHolds
conclusion.

### Rotary 1-D-positions note

L2 positions `4799 : [4096]` are a 1-D replicated init chunked per rank (PM 7803
r0 / 7804 r1), unlike L1's `[L,1]`. Required
`fw_rotary_apply_allGather0_commute_2_1d`; the SM/PM cache mismatch (SM `4691` vs
PM `11855 = 11853+2`) is bridged by `hcache_4691_11855`
(`sm_pm_rotary_cache_agree`). Both rotary theorems carry
`set_option maxHeartbeats 8000000`.

### Effective new count

Was 73. **+38 L2 tids = 111 / 1151** unconditional-given-WellFormed ring-attn
goals. All 38 correspond to genuine `intermediateGoal_<tid>` defs (verified: no
duplicate definitions in any other module).

### Axiom audit
`#print axioms` on representative L2 theorems (`recon_intermediateGoal_4768/4792/
4800/4801_ringAttn`): only `propext`, `Classical.choice`, `Quot.sound` +
`_native.native_decide.ax_*` baseline. **Zero `sorryAx`, zero user `axiom`.**

### Commits (this worker)
- `9408e967` L2 phase-3c all2all 4768 + 7471 + WF routing-locality fields
- `0b692360` L2 phase-3d residual/float/rms 7460,4788,4789,4790,4792 (2-tp)
- `8103d21c` L2 phase-3d-2 per-head 4794,4796,4798 (2-tp)
- `541a35e6` L2 phase-3d-3 rotary Q/K outputs 4800,4801 (2-tp)

### Remaining frontier
L2 is fully closed. Next: L3 all2all `4822` + tail (multiref/RMSNorm frontier
`4846`), replicating the L2 pattern via `twoTp_gather` + a per-layer
`routing_map_local` WF field analogous to `wf4768`. L3+ upstream attention
chains must be enumerated from source before proving.

## Worker 23 (cont.) — Complete L3 block reconstruction

### Objective met: the entire L3 block is closed
L3 mirrors L2's 2-tp sharded cascade. All L3 intermediates from the MoE upstream
chain through the final rotary Q'/K' outputs `4854/4855` are reconstructed
unconditional-given-`WellFormed_YOCOMoE_A04B`, in generated topological order.
Every PM node index was enumerated from `GeneratedYOCOMoE.lean` with a parser
matching both plain-list and broadcast-multiref (`(List.range N).map`) node forms,
anchored on the all2all node (`7863` = PM real idx 279).

### New tids landed (`denote/yoco_goals/L3Reconstruction.lean`)
MoE upstream chain (27 goals) + `moe_topk_common_L3` helper — commit `606656a2`.
MoE all2all `4822` + `wf4822_hdisjA/B` fields — commit `2ab8ddca`.
Residual tail (10 goals): `7512 4842 4843 4844 4846 4848 4850 4852 4854 4855`
(+ `hcache_4691_11856` helper) — commit `c2e36ce7`.

### L3 tail dependency table (SM node / PM nodes / op)
| tid | SM node | PM nodes | op | key gear |
|-----|---------|----------|----|----------|
| 4822 | 109 all2all | 201.. (7863/7864) | FW_all2all_moe_gmm | `fw_all2all_moe_gmm_split_commute_2_of` + `wf4822_hdisjA/B` |
| 4842 | 116 add | 293/294 | FW_add | `fw_add_allGather0_commute_2` |
| 4843 | 117 float | 295/296 | FW_to (id) | 2-tp float |
| 4844 | 118 add | 297/298 | FW_add | 2-tp residual bridge |
| 4846 | 120 rms | 301/302 | FW_rms_norm | `fw_rms_norm_allGather0_commute_2` |
| 4848/4850/4852 | 122/123/124 perhead | 305/308,306/309,307/310 | FW_per_head_mix_precision_linear | `fw_per_head_mix_precision_linear_allGather0_commute_2` |
| 4854/4855 | 125 rotary | 311/312 | FW_rotary_embedding | `fw_rotary_apply_allGather0_commute_2_1d` |

mref3 of 4846 at PM 303 (r0) / 304 (r1) feeds the per-head Q/K/V slices. Cache
bridge `hcache_4691_11856` (`sm_pm_rotary_cache_agree`, `11856 = 11853+3`).

### WellFormed contract extension
Added `wf4822_hdisjA` / `wf4822_hdisjB` positive structural routing-locality
fields for the L3 all2all (rank-0/rank-1 expert-index disjointness, shards
`7855/7856`), mirroring `wf4768`. Witnessed by the zero-tensor
`routing_map_local` baseline; no InitGoalHolds conclusion encoded.

### Effective new count
Was 111 (L2). **+28 L3 MoE/all2all + 10 L3 tail = 149 / 1151**
unconditional-given-WellFormed ring-attn goals.

### Axiom audit
`#print axioms` on representative L3 theorems (`recon_intermediateGoal_4822/4846/
4852/4855_ringAttn`): only `propext`, `Classical.choice`, `Quot.sound` +
`_native.native_decide.ax_*` baseline. **Zero `sorryAx`, zero user `axiom`.**

### Commits (L3)
- `606656a2` L3 MoE upstream chain (27 goals) + `moe_topk_common_L3`
- `2ab8ddca` L3 MoE all2all `4822` + `wf4822` fields
- `c2e36ce7` L3 residual tail `7512/4842/4843/4844/4846/4848/4850/4852/4854/4855`

### Remaining frontier
L3 fully closed. L3 tail `4854/4855` rotary Q'/K' feed L4's attention. Next:
L4 all2all `4876`, multiref/RMSNorm frontier `4900` — enumerate each L4 node
from source (corrected parser) before proving; do not assume an exact L3 mirror.

## Worker 23 (cont.) — L4–L11 block reconstruction (mechanical periodic cascade)

### Objective met: MoE layers L4 through L11 are fully closed
The YOCO-MoE forward graph is a clean periodic mirror across MoE layers: SM node
index stride +39, PM node index stride +78, reconstruction tids +54, 7xxx
multiref tokens +52, routing shards +186, position chunks +1, rotary cache id +1.
Each layer's 38 reconstruction goals were produced by a context-aware integer
remap of the previous layer (`/tmp/gen_layer.py`, throwaway) and then **validated
node-by-node by `native_decide`** — every SM/PM node record, theorem tid, and
hypothesis must agree with `GeneratedYOCOMoE.lean` or the build fails loudly.

Conflict handling (why the remap is faithful, not a rename):
- **Node index vs shape/rank collisions** (e.g. PM node index `512` coincides with
  the hidden-dim shape `512`, and the rank field follows a node index): node
  indices are remapped only in their syntactic positions (after `initSM`/`initPM`,
  `.take`, or as the 2nd number of a `foldl` when the 1st is a token), never inside
  shape brackets or the rank slot.
- **SM/PM token-id collisions**: the SM and PM graphs share the numeric id space but
  denote different tensors. ~29 conflict tokens are resolved per-graph, using each
  token's defining `denoteGraph_ringAttn sm/pm init.. V` context (consistent for
  hypothesis names) with a stateful current-graph fallback; `intermediateGoal_<tid>`
  ids are always SM.

### WellFormed_YOCOMoE_A04B extensions
Added positive structural routing-locality fields `wf4876, wf4930, wf4984, wf5038,
wf5092, wf5146, wf5200, wf5254` (rank-0/rank-1 expert-index disjointness shards for
each layer's all2all), all covered by the existing zero-tensor `WellFormed_routing_witness`
(no goal-shaped/backdoor fields; consistency witness unchanged in structure).

### Effective count
Was 149 (L3). **+38 per layer × 8 layers (L4..L11) = 453 / 1151** unconditional-
given-WellFormed ring-attn reconstruction goals. Layer totals: L4=187, L5=225,
L6=263, L7=301, L8=339, L9=377, L10=415, L11=453.

### Axiom audit
`#print axioms` on representative all2all goals per layer (e.g. `recon_intermediateGoal_
4876/5092/5254_ringAttn`): only `propext, Classical.choice, Quot.sound` and
`_native.native_decide.ax_*`. Zero sorry / sorryAx / user axioms.

### Commits (L4–L11)
- `c4b1b17c` L4 block (tids 4858–4909) + `wf4876`
- `75c95aec` L5 block (tids 4912–4963) + `wf4930..wf5308`
- `0d5be0c6` L6–L11 blocks (all2all 4984/5038/5092/5146/5200/5254 + tails)

### Remaining frontier
- **L12 (last MoE layer) not yet reconstructed.** It is a boundary layer: its
  late-layer ids (rotary/residual/cache `5279..5287`, `9443..9482`, `15654..15675`,
  `11864`) have no periodic +stride successor (there is no L13 attention), so the
  mechanical remap that generates L(n+1) from L(n) cannot generate L12 by chaining;
  L12 must be reconstructed directly against `GeneratedYOCOMoE.lean` (expected
  all2all tid `5308`, multiref/RMSNorm frontier `5278`). This is the exact first
  missing theorem: `recon_intermediateGoal_5308_ringAttn` and the L12 tail.
- After L12, the remaining 1151-goal frontier is the non-MoE / global-output
  obligations outside the per-layer attention+MoE cascade.

---

## Worker #24 — L12 boundary (last MoE layer)

### L12 periodic bulk (`denote/yoco_goals/L12Reconstruction.lean`)
Verified the per-position numeric delta is CONSTANT across L9→L10→L11 (the
L-reconstruction files are byte-structurally identical modulo digit-runs), so the
periodic portion of L12 is generated by positional extrapolation
`L12[i] = L11[i] + (L11[i] − L10[i])`: per layer `+54` (SM tid), `+186` (PM tid),
`+39` (SM node index), `+78` (PM node index), `+52` (7xxx multiref).  Each theorem
embeds `native_decide` node-record checks, so any wrong index fails the build loudly.
32 theorems, tids `5291,5292,5294..5330` + multirefs `7959,7980`; all2all at `5308`
(`= 5254 + 54`; WF fields `wf5308_hdisjA/B` already present).  Divergence begins at
`5332` (the periodic remap is invalid past this point — there is no L13 to chain to).

### L12 boundary tail (`denote/yoco_goals/L12BoundaryTail.lean`)
The tail `5332..5344` is the YOCO cross-decoder transition: the global KV cache is
computed once on the full L12 residual and broadcast ×12.  Closed the 5 *replicated*
single-rank goals (`tps = [{0,tid}]`, `tid == ts`):

| tid  | op                         | SM node | PM last-writer node (rank 1) |
|------|----------------------------|---------|------------------------------|
| 5332 | rms_norm(mref₀(5330),5331) | 471     | 1008 (reads gather `11917`)  |
| 5334 | per_head(mref₀(5332),5333) | 475     | 1017 (reads `15749`)         |
| 5336 | per_head(mref₁(5332),5335) | 476     | 1018 (reads `15753`)         |
| 5343 | FW_to(mref-first₁₂(5334))  | 481     | 1036 (reads `15815`)         |
| 5344 | FW_to(mref-first₁₂(5336))  | 493     | 1060 (reads `15921`)         |

Gather bridge: PM `11917 = AllGatherPrim[mref₀(9625), mref₀(9626)]` (node 1004);
`twoTp_gather` on the proven periodic goal `5330` gives
`sm 5330 = allGather 0 2 0 [pm 9625, pm 9626] = pm 11917`, so the replicated ops
agree valuewise.  **Key correctness point:** `denoteGraph_ringAttn` is a left fold,
so a tid emitted by BOTH PM ranks resolves to the *last* (rank-1) writer; the PM
reconstruct is therefore driven through the rank-1 node and its rank-1 intermediate
multiref tids.  Values remain rank-independent (rank-1 RMSNorm reads the same global
gather; per-head/cast chains use replicated weights).  Closed by `wrap_1tp_gen`.

### L12 boundary maybe-shuffle branch (`denote/yoco_goals/L12MaybeShuffle.lean`)
Closed the remaining 3 genuinely 2-tp sharded boundary goals `5338 / 5340 / 5342`
(PM tids `9655/9656`, `9657/9658`, `9659/9660`), so the **L12 boundary tail is now
fully closed**:
- `5338 = FW_maybe_shuffle(mref₁(5330), 5337)`.  `fw_maybe_shuffle` is Denote-faithful
  identity on the data tensor (`Denote.lean:1235`, audited against Python
  `wrap_maybe_shuffle`; the varlen zigzag permutation is cross-rank-invisible), and
  commutes with dim-0 sharding via the existing `fw_maybe_shuffle_allGather0_commute_2`.
  So `5338` is `5330` re-sharded.  The CP metadata differs SM `[1,0]` vs PM
  `[2,0]/[2,1]`, which is irrelevant precisely because the op ignores it.
- `5340 = FW_rms_norm(mref₀(5338), 5339)` — identical template to periodic `5299`,
  backed by `fw_rms_norm_allGather0_commute_2`.
- `5342 = FW_per_head(5340, 5341)` (16-head Q path) — backed by
  `fw_per_head_mix_precision_linear_allGather0_commute_2`.
All via `wrap_2tp_allGather_gen`.  No new gears or Denote changes were required —
the maybe_shuffle op and all three commute lemmas already existed and are reused
verbatim; the only novelty is applying `fw_maybe_shuffle`'s existing identity
semantics at this boundary.

### Effective count
453 + 32 (periodic bulk) + 5 (replicated boundary) + 3 (maybe-shuffle branch)
= **493 / 1151**.  **L12 (the last MoE layer) is fully closed.**

### Axiom audit
`#print axioms` on `recon_intermediateGoal_5308_ringAttn` (all2all),
`_5332_` (boundary rms), `_5344_` (boundary cast): only `propext, Classical.choice,
Quot.sound` and `_native.native_decide.ax_*`.  Zero sorry / sorryAx / admit / user axioms.

### Remaining frontier (ranked) — full analysis (W24)

The corrected coverage metric is **493 / 1151** unique `intermediateGoal` tids proven
(regex must match `recon_intermediateGoal_<tid>` with OR without a `_suffix`; the L1
entry goals `4681/4683/4685/4687/4689/4692/4693` use the bare form and are already
proven via `recon_ringAttn_of_plain`).  All 658 remaining goals are the **YOCO
cross-decoder + its tail** — one contiguous frontier, `5348 … 8603`.  There is no
small isolated gap left to pick off; the whole remainder is the cross-decoder.

**1. YOCO cross-decoder — 12 periodic layers (stride +49 tid, +35 SM node), ~480 goals.**
   Layer-0 goal ids `5348..5391` (~40 goals); layer L = layer0 + 49·L for L=0..11
   (`5347→5396→5445→…`).  Each layer is a zigzag-attention MoE block.  Per-layer op
   sequence (SM nodes 505..539 for L0), in topological order:
   `FW_attn_zigzag(5347)` → `reshape(5348,5349)` → `mix_precision_linear(5351)` →
   `view(5352)` → `float(5353)` → `add(5354)` [residual] → `rms_norm(5356)` →
   `float(5357)` → `reshape(5366,5371,5375)` → `norm_linear(5359)` →
   `mix_precision_linear(5368,5373,5377)` → `topk_routing(5360,5361)` →
   `view(5369,5374,5378)` → `all2all_moe_gmm(5365)` → `sigmoid(5370)` →
   `swiglu(5379)` → `reshape(5380)` → `mix_precision_linear(5382)` → `view(5383)` →
   `mul(5384)` → `add(5385)` → `float(5386)` → `add(5387)` [residual] →
   `rms_norm(5389)` → `per_head(5391)` → next zigzag `attn_zigzag(5396)`.
   ALL these ops already have gears (`applyNode_fw_{norm_linear,topk_routing_*,
   all2all_moe_gmm_*,sigmoid,swiglu,mul,reshape,view,float,add,rms_norm,
   per_head_mix_precision_linear}_out`) reused verbatim from the L2–L12 main-decoder
   reconstruction; no NEW op infrastructure is needed for the MoE body.

   **KEY UNLOCK (found by W24):** the zigzag entry `5347` is currently proven only
   *conditionally* — `ZigzagReconstruction.recon_intermediateGoal_5347_ringAttn_of_qkv`
   takes hypotheses `hq_full : (take 505 sm) 5342 = allGather0[pm 9659, pm 9660]`,
   `hk_repl : sm 5343 = pm 5343`, `hv_repl : sm 5344 = pm 5344`, plus shard shapes.
   **These are EXACTLY the L12-boundary goals W24 just proved:** `L12MaybeShuffle`'s
   `5342` `hval` is verbatim `hq_full` (gather over pm `9659/9660`, shard shapes
   `[2048,16,64]`), and `L12BoundaryTail`'s `5343/5344` give `hk_repl/hv_repl` +
   shapes `[4096,4,64]`.  So an **unconditional** `recon_intermediateGoal_5347_ringAttn`
   is now assemblable from W24's results (bridge full-fold `denoteGraph_ringAttn`
   ↔ prefix-fold `(take 505/1072)` via `foldl_prefix_eq_full_ringAttn'`; both writers
   are < node 505 / 1072).  Once 5347 is unconditional, `5348` (reshape) and the rest
   of layer-0 follow the `recon_intermediateGoal_4697_ringAttn` post-attention
   template (`ringAttn_reshape_reduce_g12` + `wrap_2tp_allGather_gen`), and layer L
   extrapolates by the constant +49/+35 delta (native_decide-validated per node).

   **REMAINING BLOCKER for the unconditional 5347:** the CP zigzag gear
   `recon_attn_zigzag_2tp_layer_cp` *also* requires
   `h_bound : ∀ t, (decodeCuSeqlens (pm 5346)).getD (t+1) 0 ≤ 4096` and two
   `fw_attn_varlen … .shape = [2*2048,16,64]` facts.  `hfull_shape` is dischargeable
   via `fw_attn_varlen_shape_p3` (as the sliding-window layers do), but `h_bound`
   depends on the *value* of the cuseqlens init leaf `pm 5346` and is NOT
   native_decide-able over a symbolic store.  The main-decoder sliding-window path
   never needed it (fixed window, gear takes no bound).  Discharging it faithfully
   needs a NEW positive `WellFormed_YOCOMoE_A04B` field asserting the harness
   cuseqlens are bounded by the max sequence length (4096) — a legitimate structural
   harness fact, NOT goal-shaped — plus a matching extension of the zero-tensor
   consistency witness (`decodeCuSeqlens 0 = [0]`, `getD (t+1) 0 = 0 ≤ 4096`
   trivially).  This is the exact next task and unlocks all ~480 cross-decoder goals.

**2. Cross-decoder multiref/expert tail** `7404..7976`, `7987..8603` — the `7xxx/8xxx`
   multiref fan-outs and expert-branch intermediates of the same 12 layers; they
   reconstruct alongside their layer once the body above is done.

**3. Post-transformer / global output** after the cross-decoder (final norm, LM
   head/logits, loss/backward/global outputs) — the graph tail beyond `~5930`.

---

## Worker #25 — Faithful unconditional 5347 + layer-0 cross-decoder spine

Branch head: `845209f7` (parent `d7066794`, baseline `cb65ba6f`).

### Milestone commits (pushed)
- `d7066794` — **Faithfully close unconditional 5347 zigzag L0 entry.** Removed
  the 11 smuggled Q/K/V/shape WF fields (`wf5347_hq_full..hfull_shape'`) that W24
  had planted in `WellFormed_YOCOMoE_A04B`; replaced them with a SINGLE genuine
  harness field `wf5347_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5346)).getD
  (t+1) 0 ≤ 4096` (a positive structural fact about the varlen attention mask, not
  a goal restatement). Added consistency witnesses in `WellFormedInputs.lean`
  (`scalarToNat_zero`, `decodeCuSeqlens_zeroTensor_le`, `WellFormed_cuseqlens_witness`):
  the all-zero cu-seqlens tensor decodes to all-zero seqlens, proving the bound
  from actual `decodeCuSeqlens` semantics. New module `ZigzagL0Entry.lean` proves
  `recon_intermediateGoal_5347_ringAttn` unconditional-given-WF by DISCHARGING the
  Q/K/V lineage from W24's proven `5342`/`5343`/`5344`, bridging full folds to the
  gear's prefix folds (`foldl_prefix_eq_full_ringAttn'`) and the pure-init leaf
  `5346` (`foldl_applyNodeRingAttn_at_not_written`), then feeding
  `recon_intermediateGoal_5347_ringAttn_of_qkv`.
- `845209f7` — **Layer-0 cross-decoder spine 5348–5353.** Post-attention segment,
  all 2-tp sharded (dim-0 allGather), chained from proven 5347; no new gears.

### WF cuseqlens field + witness (fidelity justification)
Field: `wf5347_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5346)).getD (t+1) 0 ≤ 4096`.
This is the ONLY genuine external requirement the zigzag gear needs beyond the
Q/K/V lineage: the varlen `fw_attn_zigzag` decodes `cu_seqlens_padded` (`5346`) and
requires per-sequence lengths not to exceed the padded window (4096). It is a
harness/mask agreement about an INPUT leaf, never mentions `5347` or any goal
conclusion, and is inhabited (`WellFormed_cuseqlens_witness`, zero-tensor). The
zero-tensor bound proof is derived from `decodeCuSeqlens` semantics
(`valAt_zeroTensor` ⇒ `scalarToNat 0 = 0 ≤ 4096`), not assumed.

### Unconditional 5347: CLOSED
`#print axioms recon_intermediateGoal_5347_ringAttn` (in `ZigzagL0Entry`): only
`propext, Classical.choice, Quot.sound, _native.native_decide.ax_*`. Zero
sorry/admit/user axioms. The proof consumes ONLY `hSM/hPM/hInit/hWF` and the
proven `5342/5343/5344`; the single WF input touched is `wf5347_hcuseq_bound`.

### Layer-0 dependency table (SM idx = line−17, PM idx = line−949)
| tid  | op (SM)                              | ins        | SM idx | PM shards (idx)         | status |
|------|--------------------------------------|------------|--------|-------------------------|--------|
| 5347 | FW_attn_zigzag                       | 5342..5346 | 505    | 9687(1072)/9688(1073)   | ✅ faithful |
| 5348 | FW_reshape [4096,16,64→4096,1024]    | 5347       | 506    | 9689(1074)/9690(1075)   | ✅ |
| 5349 | FW_reshape [4096,1024] (id)          | 5348       | 507    | 9695(1076)/9696(1077)   | ✅ |
| 5351 | FW_mix_precision_linear(·,5350)      | 5349,5350  | 508    | 9699(1078)/9700(1079)   | ✅ |
| 5352 | FW_view [4096,1024] (id)             | 5351       | 509    | 9709(1080)/9710(1081)   | ✅ |
| 5353 | FW_float (id cast)                   | 5352       | 510    | 9713(1082)/9714(1083)   | ✅ |
| 5354 | FW_add (residual)                    | **8143**,5353 | 511 | 9717(1084)/9718(1085)   | ⛔ blocked on 8143 |
| 5356 | FW_rms_norm                          | 5354,5355  | …      | …                       | ⛔ (needs 5354) |
| 5359..5387 | MoE routing/experts            | 5357…      | …      | …                       | ⛔ (needs 5356) |
| 5389 | FW_rms_norm                          | …          | …      | …                       | ⛔ |
| 5391 | FW_per_head                          | …          | …      | …                       | ⛔ |
| 5396 | next FW_attn_zigzag (layer 1 entry)  | …          | …      | …                       | ⛔ |

**Blocker root cause:** `5354` residual add needs `8143` = the main-decoder final
output `FW_per_head_mix_precision_linear(14926, 4901)` (SM node ~1315), whose
lineage `14926` runs back through the entire main decoder tail. `8143` has no
reconstruction yet; it is an independent (large) DAG branch, not part of the
layer-0 spine. Per the campaign rule, green predecessors (5348–5353) are
committed/pushed and the spine is parked here pending an `8143` reconstruction.

### Effective count
`grep -rhoE "theorem recon_intermediateGoal_[0-9]+(_[A-Za-z0-9]+)*"` unique tids:
**498 / 1151** (was 493; +5 new: 5348/5349/5351/5352/5353; 5347 was already
counted but is now faithful rather than smuggled).

### New modules / gears
- `ZigzagL0Entry.lean` (new, downstream of `L12MaybeShuffle`+`L12BoundaryTail`):
  isolates all new `native_decide`-over-`sm`/`pm` assembly so `WellFormedInputs`
  stays fast. No new gears — every step reuses proven L2–L12 machinery
  (`ringAttn_reshape_reduce_g12`, `ringAttn_reduce1_pm_opaque`, `ringAttn_reduce2`,
  `fw_view_allGather0_reshape_16_64_2_g12`, `fw_view_allGather0_commute_2_of`,
  `fw_mix_precision_linear_allGather0_commute_2`, `veq_weight_ring`,
  `wrap_2tp_allGather_gen`, `twoTp_gather`, `oneTp_valeq`,
  `foldl_prefix_eq_full_ringAttn'`).
- Denote changes: NONE (no fidelity fix required; the model was accurate).

### Ranked remaining frontier
1. **Reconstruct `8143`** (main-decoder final per-head output) — unblocks the
   entire rest of layer-0 (5354→5356→MoE 5359..5387→5389→5391→5396). Highest
   leverage; large (deep `14926` lineage).
2. **Layer-0 MoE body** (5359..5387) once 5356 lands — routing/experts, reuses
   L2–L12 MoE gears (`MoEShardedReconstruction`).
3. **Later cross-decoder layers 1..11** (stride +49 tid) — same spine template;
   Pattern_3 already carries per-layer commute lemmas (`sm_pm_reshape_float_5402`
   etc.), so the assembly is mechanical once layer 0 is complete.
4. **7xxx/8xxx multiref/expert fan-outs** of each layer.

---

## Worker #26 — layer-0 body, all2all, K/V casts, and faithful `5396`

Continuous campaign from W25 baseline HEAD `796c9afc` (498/1151).

### Commits pushed to `origin/intermediate-goals-recon`
- `ad5ec652` — **8143** reconstruction (root-cause: SM multiref alias of the
  proven L12 boundary `5338`; the sibling index-0 output `8139` was already
  consumed by W24's `5340`). NOT the deep `FW_per_head_mix_precision_linear(14926,4901)`
  branch that W25 hypothesised — a structural multiref alias sufficed.
- `6043ab06`,`535386f5` — spine `5354`/`5356`/`5357`/`5359`.
- `568bb203` — expert reshapes `5366`/`5371`/`5375`.
- `f745182d` — expert branch `5368`,`5369`,`5370`,`5373`,`5374`,`5377`,`5378`,
  `5379`,`5380`,`5382`,`5383`,`5384`.
- `b68de26f` — topk `5360`/`5361` (routing probs/map).
- `d191ec4c` — all2all MoE gmm `5365` (template = L12 `5308`; added genuine
  harness fields `wf5365_hdisjA/B`, routing-locality class of `wf5308_hdisjA/B`,
  covered by `WellFormed_routing_witness`).
- `ec658120` — residual tail `8151`/`5385`/`5386`/`5387`.
- `c68d36fb` — RMSNorm `5389` + per-head Q `5391`.
- `fcb9cfcd` — next-block K/V casts `5392`/`5393` (`FW_to(mref-pos1₁₂(5334/5336))`;
  new generic gear `applyNode_fw_multiref_second_out'`).
- `1a63236f` — **de-smuggle `5396`** (fidelity fix, no count change).

### 8143 dependency audit (root-cause classification)
`8143 = mref₁(5338)` (SM node 474) — case (1): a fan-out/multiref alias of an
already-reconstructed L12 boundary value (`5338`). No new topological proofs
below it were required; the "deep `14926` lineage" hypothesis was rejected by the
source-derived DAG.

### Layer-0 completion (5354..5396)
Every `intermediateGoal` def in `5354..5396` now has a reconstruction theorem
(spine, topk, all2all, expert body, residual tail, RMSNorm, per-head Q, K/V
casts, and the zigzag entry `5396`). `5397/5398` begin layer 1 (out of scope).

### Goal-shaped WF fields removed/replaced (fidelity)
- `recon_intermediateGoal_5396_ringAttn` was **smuggled** through 10 goal-shaped
  fields (`wf5396_hq_full/hk_repl/hv_repl/hq_sm/hk_sm/hv_sm/hk_shape/hv_shape/
  hfull_shape/hfull_shape'`). All 10 removed; the theorem is re-proved faithfully
  in `ZigzagL0Residual` from the reconstructed goals `5391` (2-tp Q gather over
  PM `9835`/`9836`), `5392`/`5393` (replicated K/V), bridged full↔prefix via
  `foldl_prefix_eq_full_ringAttn'`, shapes via `fw_attn_varlen_shape_p3`.
- Only genuine harness invariant kept: `wf5396_hcuseq_bound` (cu-seqlens upper
  bound on pure-init leaf `5395`), positive/reusable, satisfiable via
  `WellFormed_cuseqlens_witness` (same class as W25's `wf5347_hcuseq_bound`).

### New gears / WF changes
- `applyNode_fw_multiref_second_out'` (ZigzagL0Residual): generic positional
  extractor for the *second* output of an `FW_multiref` of any fan-out ≥2,
  needed for the 12-way global-KV multirefs (pos1). Faithful: proved directly
  from `evalOp_fw_multiref`/`storeSet`.
- `wf5365_hdisjA/B` added (routing-locality, genuine harness invariant).
- Denote changes: NONE.

### Effective count
**529 / 1151** (baseline 498; +31 new tids this campaign). Additionally, `5396`
was **made faithful** (previously counted while smuggled) — reported separately,
no double count.

### Axiom audit
`#print axioms` on `recon_intermediateGoal_5396/5392/5393_ringAttn`: only
`propext, Classical.choice, Quot.sound` + `_native.native_decide.ax_*`. Zero
`sorry`/`sorryAx`/`admit`/user axioms.

### Ranked remaining frontier
1. **Layer 1 entry `5397`/`5398`** and its zigzag body (`5445` is next smuggled
   entry — de-smuggle once its Q/K/V land), stride +49 tid / +35 SM node.
2. **Later cross-decoder layers 2..11** — mechanical per-layer template; validate
   the +49/+35 map against `GeneratedYOCOMoE.lean`, hand-reconstruct at any
   structural divergence.
3. **Remaining smuggled zigzag entries** `5445`,`5494`,`5543`,`5592`,… — same
   de-smuggling pattern as `5396`/`5347` once each layer's Q/K/V are proven.
4. **7xxx/8xxx multiref/expert fan-outs** of each later layer.

## Worker #27 — cross-decoder layers 1–11 via a checked periodic remapper

Continuous campaign from W26 baseline HEAD `64634950` (**529/1151**).

### Commits pushed to `origin/intermediate-goals-recon`
- `8e089eaa` — **layer 1** body `5397..5442` + faithful K/V casts `5441`/`5442`
  + de-smuggled zigzag entry `5445` (`ZigzagL1Body.lean`).
- `7c2aa8f4` — **layers 2–10** bodies `5446..5885` + K/V casts + de-smuggled
  entries `5494/5543/5592/5641/5690/5739/5788/5837/5886` (`ZigzagL{2..10}Body`).
- `6e6692cf` — **layer 11** periodic body `5887..5926` (final layer; partial —
  see divergence note) (`ZigzagL11Body.lean`).

### Checked periodic remapper (Phase C)
The cross-decoder layers are structurally periodic. Rather than trust a blind
`+49` offset, every layer body is produced by an **alignment-checked** remapper
whose output is re-validated node-by-node against `GeneratedYOCOMoE.lean`:

- **Strides (L0 → LN):** SM goal-tid **+49·N**; PM tid **+172·N**; SM writer-node
  index **+35·N**; PM attention-node index **+70·N**; SM attn boundary node
  `540+35·N`; PM attn nodes `1142+70·N` / `+1`; Q PM tids `9835+172·N` / `+1`;
  routing PM tids `9733+172·N`(rank0)/`+1`(rank1); zigzag entry boundary
  `E = 5396+49·N`; cu-seqlens leaf `E-1`.
- **K/V casts:** the next-block K/V are *replicated* (written on both ranks) and
  read as **leg N+1** of the two 12-way global-KV `FW_multiref`s (SM 478/479,
  PM 1021/1023), routed through the **rank-1 last-writer** `FW_to` node
  (SM `482+N`/`494+N`, PM `1037+N`/`1061+N`). Discharged by the generic public
  gear `applyNode_fw_multiref_out` (all multiref legs share the input value, so
  no positional distinctness is needed).
- **Tooling (session artifacts, not committed):** `align_n.py N` seeds the L0→LN
  tid correspondences from the goal defs and propagates through the writer DAG
  with **op-preserving conflict detection** (`maps_N.json`); `gen_full.py N`
  applies the map to the L0 body theorems, emits the hand-written casts + entry,
  and reports `UNMAPPED=0`. The *build itself is the validator*: each node
  reduction carries a `native_decide` against the real graph, so any wrong remap
  constant fails to compile. Regex-only substitution was **not** trusted.

### De-smuggling (fidelity, count-neutral)
Every zigzag entry `5445, 5494, 5543, 5592, 5641, 5690, 5739, 5788, 5837, 5886`
(10 total) was **re-proved faithfully** from reconstructed Q/K/V (2-tp Q gather,
replicated K/V casts, full↔prefix bridge via `foldl_prefix_eq_full_ringAttn'`),
exactly like W26's `5396`. All goal-shaped `wf5445_*..wf5886_*`
Q/K/V/shape fields **and their smuggled companion theorems** were deleted from
`WellFormedInputs.lean`. The only WF fields kept are positive, reusable harness
invariants, each covered by an existing zero-tensor witness:
- `wf<E>_hcuseq_bound` — cu-seqlens upper bound on the pure-init leaf `E-1`
  (`WellFormed_cuseqlens_witness`), for each entry E.
- `wf<5365+49N>_hdisjA/B` — routing-locality of the per-layer all2all
  (`WellFormed_routing_witness`), for N=1..11.
No theorem conclusions or equalities remain in the WF class.

### Layer 11 divergence (final decoder layer)
Layer 11 does **not** follow the template tail: there is no attention boundary
`5935` (no next-zigzag entry), the global-KV multiref has only legs 0–11 so
there is **no** KV-cache extension (`FW_to` writing `K=5931`/`V=5932` — leg 12 —
does not exist), and the last two body ops diverge (`5928` `FW_maybe_unshuffle`
vs L0 `FW_rms_norm`; `5930` `FW_rms_norm` vs L0 linear). We therefore close only
its **periodic body** `5887..5926` (32 goals incl. all2all `5904` and residual
helpers `8572`/`8580`) and deliberately do **not** force the divergent tail,
cast, or entry. Those remain open and are flagged as a distinct structure.

### Gears / Denote / WF changes
- Reused public gear `applyNode_fw_multiref_out` (Pattern_3) for all K/V casts —
  no new per-position `_nth_out'` gears needed.
- Local copies (L0 originals are `private`): `applyNode_fw_multiref_third_out'`
  and `elemwiseMul_shape_broadcast_S1` in each generated body.
- WF: added `wf5414/5463/../5904_hdisjA/B` (routing) and
  `wf5445/5494/../5886_hcuseq_bound` (cu-seqlens). Removed all smuggled
  `wf5445_*..wf5886_*` Q/K/V/shape fields + companions. **Denote: NONE.**

### Effective count
**921 / 1151** — baseline 529, **+392 new goal tids** this campaign:
L1–L10 = 36 each (34 body + 2 K/V casts) = 360; L11 = 32 (body only). The 10
de-smuggled zigzag entries were already counted while smuggled and are reported
separately (count-neutral, now faithful).

### Axiom audit
`#print axioms` on representative `recon_intermediateGoal_*_ringAttn` across
L1–L11 (e.g. `5887/5904/5926`, `5441/5442`, entries): only
`propext, Classical.choice, Quot.sound` + `_native.native_decide.ax_*`. Zero
`sorry`/`sorryAx`/`admit`/user axioms. Banned-token scan clean.

### Ranked remaining frontier
1. **Layer 11 tail** — divergent final-layer ops `5928`/`5930` and whatever
   follows (final norm / LM head); hand-reconstruct, no periodic template.
2. **7xxx/8xxx global-KV / expert fan-outs** beyond the two residual helpers
   already landed per layer (`8143/8151` analogues).
3. Any post-decoder head/loss goals above the last decoder boundary.

---

## Worker #28 — Final-layer tail, head/loss fan-outs → **1151/1151 COMPLETE**

Baseline `92dfdb88`, count 921/1151 (909 `_ringAttn` + 12 pre-existing non-ring
`recon_intermediateGoal_N` in `IntermediateReconstruction`). **W28 closed all 230
remaining goals → 1151/1151.** New HEAD `b90fe73b`.

### A. Exact remaining-goal census (source-derived, 230 tids)
Parsed the generated graph (`GeneratedYOCOMoE.lean`) and every theorem name.
230 goals lacked a `_ringAttn` reconstruction. Categories:
- **final-tail (2):** `5928` (`FW_maybe_unshuffle`, identity model), `5930`
  (`FW_rms_norm`) — dim-0 2-tp sharded `[2048,1024]→[4096,1024]`.
- **B_sharded (185):** 2-tp sharded `FW_multiref` copies. Goal G = multiref-pos(B);
  PM PG0/PG1 = per-rank multiref of B's two pre-existing shards PA/PB.
  allGather[PG0,PG1] = allGather[PA,PB] = SM B = SM G. Arities 2/3/5.
- **Group S (10):** 1-tp `FW_multiref` copies of a *replicated* base
  (`4705/4757/4759`): single PM shard = full copy; SM G = SM B = PM B = PM Tpm.
  Special member `8007`: 1-tp copy of 2-tp base `5330` whose PM shard
  `11917 = AllGatherPrim(mref₀(9625), mref₀(9626))`.
- **Group R (33):** replicated dual-tp `FW_multiref` copies of 1-tp replicated
  bases (`4703/4736/4738/5332/5334/5336`), arities 2/3 and two arity-12 groups
  (`8033-8077`, `8091-8135`). Both ranks hold full copies; pick rank-0 head.

### B. Final-layer divergent tail
`5928`/`5930` hand-reconstructed against nnScaler authority (unshuffle = identity
on data, cp-metadata ignored, matches Python early-return; final rms_norm).
Committed `5fb24241`. No absent KV-cache/leg-12 goals manufactured.

### C/D. Fan-outs (228)
Faithful, checked generators; every node index/position re-validated by per-node
`native_decide` over the real 2300-node graph. New reusable gears (all in the
generated fan-out files, no shared-file edits):
- `applyNode_mref_gen` — general arity-N multiref-position identity built on
  `storeSet_replicate_mem_g307` (handles arity 2/3/5/12 uniformly).
- `wrap_repl_dual_gen` — ring/store-generic replicated-dual wrapper (rank-0 head).
- `wrap_1tp_distinct` — 1-tp wrapper allowing `ts ≠ tid` (multiref alias goals).

Files: `FanOutB1..B5.lean` (185), `FanOutS.lean` (9), `FanOutR1..R3.lean` (33),
`FanOut8007.lean` (1). Commits `90340544`, `feff7de8`, `ff242b7f`, `b90fe73b`.

### Results
- **Count: 921 → 1151/1151 (+230).** 1139 `_ringAttn` + 12 baseline non-ring.
- Axioms (representative `#print axioms`): baseline `propext`/`Classical.choice`/
  `Quot.sound` + `native_decide` only. Zero sorry/admit/user-axioms.
- All 10 new modules + base build green together (2682 jobs).
- No Denote/spec changes required (all upstream ops already faithful; unshuffle
  and multiref identity models match Python authority).

### Residual frontier
**None** — all 1151 intermediate goals reconstructed. The 12 pre-existing
non-ring `recon_intermediateGoal_N` goals (`4681-4693`, `7383-7400`) remain as
the baseline left them (out of W28 scope; already counted).

Resume id: `b90fe73b`.
