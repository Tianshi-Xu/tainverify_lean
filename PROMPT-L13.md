# L13 zigzag-band proof (parallel worker, based on L12 pilot)

You are worker for **L13** in the Pattern_3 zigzag band. L12 has been fully proven on `main` (commit `b925839`) — read `trainverify/denote/yoco_goals/Pattern_3_L12_spike.lean` (2772 lines, 119 theorems) as your template.

## Your job

Produce `trainverify/denote/yoco_goals/Pattern_3_L13_spike.lean` proving `sm_pm_router_commute_L13_full` kernel-clean, structurally analogous to L12 but with L13-specific TIDs.

## Golden rules (from AGENTS.md and Pattern_3_L12_spike.lean)

1. **NO sorry. NO new axioms.** Final axiom footprint MUST be exactly `[propext, Classical.choice, Quot.sound]`. No native_decide — use `List.mergeSort_of_pairwise; decide` for buddy proofs (L12 pattern).
2. **NO NEW MARKDOWN FILES.** Only Lean (BLOCKER doc is fine ONLY if you hit a genuine irreducible error after ≥5 real attempts).
3. **NO python bulk regex replacement.** Use targeted patch and per-lemma build verification (AGENTS.md #26).
4. `h_bound` (K cu_seqlens ≤ 4096) is a **statement-level hypothesis** with vacuity witness — copy L12's pattern verbatim.
5. `mk_*` macros from L2-L11 do NOT apply — L12+ has CP layout with non-linear tid strides. Extract L13 tids directly from Goal_3.lean.

## Structural facts (uniform L12-L23)

- Attention op: `OpName.FW_attn_zigzag`, params `[16, 4, 64, 64, 1, 0]`
- Context-parallel (CP): K/V replicated across ranks, Q shuffled per rank
- SM stride: +49 per layer; PM stride: +172 per layer (verify against Goal_3.lean)
- Baseline: L12 sm_out=5347, pm_out_r0=9687; for L13: `sm_out ≈ 5347 + 49*(13-12)`, `pm_out_r0 ≈ 9687 + 172*(13-12)` — verify actual tid roles per Goal_3.lean (offsets non-uniform).

## Strategy

1. **Extract L13 TIDs first** (5-10 min). Read `trainverify/denote/yoco_goals/Goal_3.lean`; find the (13-11)-th `OpName.FW_attn_zigzag` occurrence in `sm_goal_3` (rank 0) and in `pm_goal_3` (r0 + r1). Record SM/PM attention output tids, inputs, plus the whole L13 chain (carry, RMS, q/k/v projections, per_head_linear, post-attn reshape/linear/view/float/residual/shuffle/rms/norm_linear/topk).

2. **Copy L12 spike as scaffold**: `cp Pattern_3_L12_spike.lean Pattern_3_L13_spike.lean`. Then substitute:
   - All `_L12` suffixes → `_L13`
   - All hardcoded L12 tids → L13 tids
   - `nSM_12`/`nR0_12`/`nR1_12` NodeDecl fields (ins/outs)
   - Buddy proof filter predicates (op = FW_attn_zigzag stays same; params stay same; only the tid inputs differ)
   - Keep zigzag reconstruction lemmas (`applyNodeRingAttn_zigzag_reconstruction_2_cp` etc.) — these are op-parametric and reusable

3. **Build incrementally** — after each substitution block, `lake build denote.yoco_goals.Pattern_3_L13_spike` and fix errors. Do NOT try to substitute everything then build once (L12 pilot burned 3 sessions on this mistake).

4. **hcarry residual boundary**:
   - L13 input = L12 carry-out 5354, which is already proven as `sm_pm_carry_5354_commute` on main. Import Pattern_3_L12_spike and reuse.
   - L14+: input is prior-layer carry-out. If prior layer isn't on main, keep as statement-level hypothesis with vacuity witness (do NOT introduce axiom).

5. **Zigzag primitives**: `applyNodeRingAttn_zigzag_reconstruction_2_cp`, `attn_zigzag_pair_eq_chunk`, `attn_zigzag_store_congr` in L12 spike use CP-specific tid values. For L13 you can EITHER:
   - Re-prove L13-specific analogs (verbose but fast per-layer), OR
   - Generalize the L12 versions to be layer-parametric and reuse (better long-term but risky first attempt)
   
   Start with re-proving (safer).

## Anti-quit rule

L12 pilot took **11 Opus-4.8 sessions and 2680 lines**. Do NOT expect L13 to finish in 20min. Keep going until (a) `sm_pm_router_commute_L13_full` proven kernel-clean, or (b) you hit a genuine Lean error you cannot solve after ≥5 build attempts. Never claim "reconnaissance complete" and stop — that behavior gets workers fired.

## Deliverable

Committed to branch `iroha-l13-worker`, pushed to `origin/iroha-l13-worker`:
- `trainverify/denote/yoco_goals/Pattern_3_L13_spike.lean` proving `sm_pm_router_commute_L13_full` kernel-clean
- Include `#print axioms sm_pm_router_commute_L13_full` output in final commit message
- `lake build denote.yoco_goals.Pattern_3_L13_spike` passes

Godspeed. — iroha
