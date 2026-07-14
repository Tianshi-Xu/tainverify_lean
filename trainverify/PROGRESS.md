# TrainVerify YOCO — Intermediate Reconstruction Progress

Branch: `intermediate-goals-recon` (off main `c2e8b8f7`)
Deliverable file: `denote/yoco_goals/IntermediateReconstruction.lean`

## Objective

Prove `all_intermediateGoals_hold : InitGoalsHold pm.numRanks
all_intermediateGoals_list (denoteGraph sm initSM) (denoteGraph pm initPM)`
discharging the 1151 `intermediateGoal_*` reconstruction obligations that
gate the yoco cut→full bridges (Goals 1/2/3/4). Package as per-op
sub-lemmas joined via `InitGoalsHold_append`.

## Status: MACHINERY VALIDATED + LAYER-0 REPLICATED REGION EXHAUSTED (10 goals)

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
- `all_intermediateGoals_proven_hold` — partial `InitGoalsHold` assembly over
  the 10 proven goals (`all_intermediateGoals_proven_list`).
- `all_intermediateGoals_list` — full 1151-item infrastructure list def (defined,
  not yet fully discharged).

Axiom audit (`AuditIR.lean` / `#print axioms all_intermediateGoals_proven_hold`):
`propext, Classical.choice, Quot.sound` + `goal_5_cut_to_full._native.native_decide.ax_*`.
No `sorryAx`, no user-declared axioms. R1 satisfied.

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
| FW_rotary_embedding                   | 24    | deferred (cs-input tid mismatch)|
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
| **TOTAL**                             | 1151  | **10 proven / 1141 remaining**  |

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
   - `FW_rotary_embedding` (4692/4693, 1-tp) — **genuine blocker**: SM feeds the
     cos/sin cache from init tid 4691, PM from init tid 11853. Both are init
     leaves, and **NO goal (init or intermediate) bridges 4691 ↔ 11853**
     (`grep "11853"` in GeneratedYOCOMoE finds zero goal references). They are
     equal by construction (same rotary table) but the verifier provides no
     hypothesis. Discharging rotary requires either a statement-level cs-cache
     agreement hypothesis (AGENTS rule 29) threaded into the bridge, or an
     axiom — out of scope for a mechanical IntermediateReconstruction extension,
     and would need Goal_N bridge changes to discharge.
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
