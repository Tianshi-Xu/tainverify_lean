# TrainVerify YOCO — Intermediate Reconstruction Progress

Branch: `intermediate-goals-recon` (off main `c2e8b8f7`)
Deliverable file: `denote/yoco_goals/IntermediateReconstruction.lean`

## Objective

Prove `all_intermediateGoals_hold : InitGoalsHold pm.numRanks
all_intermediateGoals_list (denoteGraph sm initSM) (denoteGraph pm initPM)`
discharging the 1151 `intermediateGoal_*` reconstruction obligations that
gate the yoco cut→full bridges (Goals 1/2/3/4). Package as per-op
sub-lemmas joined via `InitGoalsHold_append`.

## Status: MACHINERY VALIDATED + LAYER-0 REPLICATED PREFIX PROVEN (5 goals)

This is a **partial** delivery per ground rule R6. The proof pattern is
fully validated end-to-end (zero sorry, kernel + native_decide axioms
only). Full 1151-goal completion is a 4–7 day effort (spec's own
estimate); a single session lands the reusable machinery + the
self-contained layer-0 replicated prefix and hands off the rest.

### Committed theorems (all zero-sorry, axiom-clean)

- `recon_intermediateGoal_4681` — FW_float
- `recon_intermediateGoal_4683` — FW_rms_norm
- `recon_intermediateGoal_4685` / `_4687` / `_4689` — FW_per_head_mix_precision_linear
- `all_intermediateGoals_proven_hold` — partial `InitGoalsHold` assembly over
  the 5 proven goals (`all_intermediateGoals_proven_list`).
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
| FW_multiref                           | 280   | un-attempted                    |
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
| **TOTAL**                             | 1151  | **5 proven / 1146 remaining**   |

Fully-closed categories cover only their layer-0 prefix instances so far
(5 goals). The reusable helper lemmas needed to scale each of the 3 proven
categories to all their instances are in place.

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
