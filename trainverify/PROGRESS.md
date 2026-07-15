# TrainVerify YOCO — Intermediate Reconstruction Progress

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
