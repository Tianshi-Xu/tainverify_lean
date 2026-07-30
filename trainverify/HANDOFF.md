# HANDOFF — Scaling YOCO Intermediate Reconstruction to all 1151 goals

> **SUPERSEDED (2026-07-28).** This is a historical worker handoff from commit
> `cfb8ca04`; do not use its status, counts, or final assembly instructions.
> The ownership-aware faithful corpus is now classified in
> `YOCO_MOE_FAITHFUL_COVERAGE.md`: 1154/1156 faithfully proven, with all sound ordinary/zigzag obligations closed and 2 discovered
> false top-level equalities. In
> particular, the instructions below to build cut→full bridges for goal_3/4 are
> wrong: those equalities are false on the audited CP2 graph because nnScaler's
> RVD model cannot represent the post-shuffle permuted layout. See
> `GOAL_3_4_LAYOUT_SPLIT.md` and `UPSTREAM_NNSCALER_RVD_ZIGZAG.md`.

This documents the **validated proof recipe** so a follow-up worker can
mechanically scale from the 5 proven goals to the remaining 1146.

## Where things are

- Deliverable: `denote/yoco_goals/IntermediateReconstruction.lean`
  (namespace `TrainVerify.Denote.GeneratedPatterns`).
- Categorizer: `python3 scripts/emit_intermediate_reconstruction.py`
  (add `--json` for per-goal ts/tps/tpShapes/op data).
- Axiom audit: `denote/yoco_goals/AuditIR.lean` (edit the `#print axioms`
  target then `lake build denote.yoco_goals.AuditIR`).
- Build (ALWAYS `ulimit -n 65535` first):
  `lake build denote.yoco_goals.IntermediateReconstruction 2>&1 | tail`
  Cold build ~9 min; incremental this-file-only ~3–12 s.

## The proof recipe (per goal)

Each `intermediateGoal_XXXX` obligation is
`InitGoalHolds pm.numRanks intermediateGoal_XXXX (denoteGraph sm initSM)
(denoteGraph pm initPM)`. Discharge it INDEPENDENTLY (no chaining through
other intermediate lemmas) by re-deriving tid `XXXX` from init leaves on
both graphs:

1. **Reduce SM side.** `sm_val initSM k T (by native_decide) (by native_decide)`
   rewrites `denoteGraph sm initSM T` to `applyNode (sm.nodes[k]) (prefix)`,
   where `k` = index of the SM node writing `T`. Then
   `rw [show sm.nodes[k]'(_) = {explicit node literal} from by native_decide]`
   and `rw [applyNode_<op>_out]` to expose the op applied to input tids.
2. **Resolve inputs.** For each input tid `i`, `rw [sm_prefix_eq initSM k i
   (by native_decide)]` rewrites `(take k prefix) i` back to
   `denoteGraph sm initSM i`. **CRITICAL: use the SAME index `k` as `sm_val`**
   (sm_val yields prefix `take k`; sm_prefix_eq must match `k`, NOT `k+1`).
3. **Same for PM** with `pm_val` / `pm_prefix_eq`. **PM last-writer rule:**
   when a tid is written by multiple PM nodes (both ranks), `pm_val` must use
   the LAST writer's index; its `hdrop` (over `drop (k+1)`) native_decide
   confirms no later write.
4. **Recurse to already-proven inputs.** Once both sides reduce to the op
   applied to input tids, substitute the input goals' `veq_*` lemmas.
5. **Wrap.** For 1-tp replicated-prefix goals use `wrap_1tp` (handles
   `reconstructForGoal_of_not_replicated` + `reconstructWithDim_singleton`).
   For 2-tp sharded goals use the extract_singleton/extract_dual +
   `_allGather0_commute_2` pattern from `Pattern_1.lean:4275-4797`.

## Node-index discovery (Python)

Node indices come from parsing `denote/GeneratedYOCOMoE.lean` (sm def @14,
pm def @946). sm has 927 nodes, pm has 1920. For a target tid, find the node
whose `outs` contains it. Example known indices (layer-0 prefix):
- sm: 4681@1, 4683@3, 7383(mref)@2, 4685@5, 4687@6, 4689@7, mref3@4.
- pm: 4680@26(AllReduce), 4681@27,28, 4683@31,32, per_head 4685@35,38 etc.

Extend the categorizer script to emit `(tid, sm_node_idx, pm_last_node_idx,
op, ins)` so the per-goal boilerplate can be code-generated.

## Category difficulty tiers (attack order)

- **Easiest (value-identity):** FW_float, FW_to — `applyNode_fw_float_out`
  gives `= s xTid`. Reduce directly to input recon. (73 + 24 goals.)
- **1-tp replicated ops (done pattern):** FW_rms_norm, FW_per_head_linear,
  FW_sigmoid, FW_swiglu, FW_mul — reuse `wrap_1tp`; need each op's
  `applyNode_*_out` + a shape lemma. Follow `recon_intermediateGoal_4683`.
- **2-tp sharded ops (harder):** FW_view, FW_reshape, FW_add,
  FW_mix_precision_linear, FW_multiref, FW_topk_routing, FW_all2all_moe_gmm.
  These need the `_allGather0_commute_2` commute lemmas already in
  `Pattern_1.lean` (grep `^theorem.*_allGather.*_commute` in yoco_goals/).
  Copy the extract_dual usage from `prove_goal_1` (`Pattern_1.lean:4165+`).
- **Bespoke (hardest):** FW_attn_sliding_window (12), FW_attn_zigzag (12,
  NEW), FW_rotary_embedding (24, needs sm4691↔pm11853 boundary),
  FW_maybe_shuffle (1), FW_maybe_unshuffle (1 — **audit cp2 fidelity first,
  AGENTS.md rule 20**).

## Assembly (final step)

Once per-op sub-lemmas `intermediateGoals_FW_XXX_hold : InitGoalsHold ...`
exist (one per category over its sub-list), join them with
`InitGoalsHold_append` (`denote/GraphSlicing.lean:76`) into
`all_intermediateGoals_hold` over `all_intermediateGoals_list`. The list def
is already present. Then:
1. Write `Goal_2_CutToFull.lean` (copy `gpt_ly4_regen/Goal5Bridge.lean:108-187`)
   using `all_intermediateGoals_hold` to close prereqs.
2. Replace the `prove_goal_2_from_pattern_2` sorry in `Instances.lean`.
3. Repeat Goal_1, Goal_4. Goal_3 uses only `[goal_5]` — trivial via
   `goal_5_intermediate`.
4. Rebuild `Instances.lean` (4 sorries → 0), then `MainTheorem.lean`.

## Gotchas (v4.31)

- `set_option linter.style.{setOption,nativeDecide,longLine} false` needed.
- Structure-literal node in a theorem BINDER type must be single-line with
  `(sm.nodes[sk]'hsk)` parenthesized. Inline `(by tac : T)` ascription as an
  rw arg fails to parse — use an in-scope `have`.
- After `rw [fw_*_shape ...]`, a trailing `rfl` is needed to reduce
  `List.reverse`/`++` on concrete shapes (rw's auto-rfl doesn't fire).
- `simp only [List.mem_cons]` leaves a trailing `∨ g ∈ []`; handle with an
  extra `rcases h with h | h` + `exact absurd h (by simp)`.

## UPDATE (2026-07-14, second worker): replicated-multiref pattern + frontier reality

- **New reusable gear:** `wrap_replicated_dual` handles `replicated := true`
  dual-tp goals (reconstruction = rank-0 head, `reconstructForGoal` true-branch =
  `tps.headD`). Pair with `applyNode_fw_multiref{2,3}_{first,second,third}_out'`
  to close replicated multiref copies. See `recon_intermediateGoal_7383` for the
  template (SM copy → source, PM rank-0 copy → source, then `veq_source`).

- **The "easy tier" is exhausted at 10 goals.** The pure-1-tp topological
  closure is exactly {4681,4683,4685,4687,4689} + the 5 replicated multiref
  copies {7383,7387,7392,7396,7400}. Do NOT chase more FW_float/FW_to/etc as
  "easy value-identity" — their inputs cross the 2-tp sharded barrier. See the
  CRITICAL FINDING section in PROGRESS.md for the dependency analysis and the
  two genuine blockers (rotary cs-cache 4691↔11853 has no bridging goal;
  attention is bespoke Tier D). Next real work = 2-tp `extract_dual` machinery.

- **Frontier discovery tooling:** parse both graphs (handle
  `ins := ((List.range N).map (fun r => BASE+r))` for the 12 attn_zigzag nodes —
  a naive regex misses these), build first/last-writer maps, resolve inputs
  through FW_multiref chains, then fixpoint the provable set. Reproduced in the
  session's /tmp/{parse,closure,frontier}.py scripts.

## UPDATE (2026-07-14, worker #4): 2-tp `extract_dual` ROTARY bridgehead — the recipe for ~910 2-tp goals

**The 2-tp reconstruction pattern is now BUILT and zero-sorry** (for the rotary op).
Use these three gears, in `IntermediateReconstruction.lean` (before
`all_intermediateGoals_list`):

1. `wrap_2tp_allGather initSM initPM g T p0 p1 tsShape shardShape (htp hgd hrep hts
   htsShape htpShapes hne : goal-structure) (hval : sm T = allGatherPrimDimN 0
   numRanks 0 [pm p0, pm p1]) (hshape : (sm T).shape = tsShape) (hp0shape hp1shape)`
   — the generic 2-tp (gatherDim=0, non-replicated) wrapper. This is the 2-tp
   analog of `wrap_1tp`: it discharges `InitGoalHolds` via
   `reconstructForGoal_of_not_replicated` + `reconstructWithDim_cons_cons_nonscalar`
   (the `if sh=[1] then allReduce else allGather` dispatch — supply `hne : shardShape ≠ [1]`,
   AGENTS.md rule 18). **This is op-agnostic — reuse it for EVERY 2-tp goal.**

2. Per-op algebraic commute lemma, e.g. `rotary_fst_gather_commute` /
   `rotary_snd_gather_commute`, built on the op's `_allGather0_commute_2`
   (here `fw_rotary_embedding_allGather0_commute_2`, Denote.lean:22937). For a new
   op grep `_allGather0_commute_2` in `denote/` — most sharded ops already have one
   (proven on the goal_3 cut graphs). Shape: `op(allGather[x0,x1],…) = allGather[op x0,…]`.

3. `recon_rotary_2tp_fst` / `recon_rotary_2tp_snd` — the **parametrized per-goal
   gear**. Abstracts over all tids/node-indices. Given: goal structure, the SM/PM
   node reductions (`hsmNode`/`hpm0`/`hpm1` — mechanical `native_decide` lemmas,
   template `sm_rotary_4800_node` / `pm_rotary_7805_node`), cs/pos/q/k input recons,
   and the 6 PM shard shapes → produces `InitGoalHolds`. The concrete goals
   `recon_intermediateGoal_4800_of_inputs` / `_4801_of_inputs` are each a SINGLE
   application. **To make an op-generic version, copy `recon_rotary_2tp_fst` and
   swap the `rotary_fst_gather_commute` call + the two `fw_rotary_embedding_fst_shape`
   uses for the target op's commute + shape lemmas.**

### CRITICAL: full-graph vs cut-graph reconstruction (spec correction)

`Pattern_1.prove_goal_1`'s `extract_dual` works on CUT graphs where intermediate
values are boundary init-leaves resolved by `hInit`. Full-graph intermediateGoal
reconstruction must RE-DERIVE each tid from init weights by chaining prior nodes.
So the 2-tp gears above take the sharded INPUT reconstructions as HYPOTHESES
(`hq`/`hk`/`hpos`) — they cannot be conjured from `hInit`. Every rotary 2-tp goal's
q/k inputs are post-attention residual-stream values requiring 2×
`FW_attn_sliding_window` + 2× `FW_all2all_moe_gmm` reconstruction (no template).

### Recommended next attack (to actually CLOSE the 20 rotary 2-tp goals)

Build the `FW_attn_sliding_window` + `FW_all2all_moe_gmm` 2-tp reconstruction
template (produces `hq`/`hk` for the rotary gears). That single template unblocks
all 20 rotary goals mechanically, and the `wrap_2tp_allGather` + parametrized-gear
pattern then generalizes to FW_view/reshape/add/mul/… 2-tp goals directly.

## Worker #9 addendum — ring-attn restatement + reshape blocker

- **Use the ring-attn assembly for anything at/after attention.** The plain
  `denoteGraph` attention goals (4696+) are FALSE (worker #8). The value-faithful
  path is `denoteGraph_ringAttn`. `all_intermediateGoals_proven_hold_ringAttn_with_attn`
  is the current top assembly (13 goals: 12 upstream + `intermediateGoal_4696`).
- **Transfer gear** for any goal whose SM/PM producers are all written BEFORE the
  first ring-attn node (sm[9]/pm[49]): `recon_ringAttn_of_plain` — turns a plain
  proof into its ring-attn counterpart with a one-line rewrite. Backed by
  `sm_ring_eq`(k=9)/`pm_ring_eq`(k=49) (`denoteGraph_ringAttn = denoteGraph` on
  those prefixes) + `InitGoalHolds_transfer`.
- **Attention recipe** (see `recon_intermediateGoal_4696_ringAttn`): reduce SM/PM
  attn nodes via `foldl_prefix_eq_full_ringAttn'` + `applyNodeRingAttn_sliding_window_out`;
  reconstruct Q/K/V fulls from their two chunks with `allGather0_reconstruct_chunks_3d`;
  discharge cu_seqlens with `recon_weight`; apply gear
  `applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair`; wrap with
  `wrap_2tp_allGather_gen`. Global attn node literals == Pattern_3 cut-graph
  `nSM/nR0/nR1` byte-for-byte (`native_decide` buddy facts).
- **CASCADE BLOCKER — RESOLVED by Worker #11 (2026-07-15):** the GLOBAL
  `GeneratedYOCOMoE` graph was regenerated from the yoco_moe_a04b pkls with the
  params-aware Verdict emitter. All 432 `FW_reshape` nodes now carry their target
  output shape on `params` (e.g. `sm[10]` 4696→4697 `params := [4096, 1024]`), so
  `Denote.evalOp` builds a faithful `fw_view` instead of identity. The reshape
  goals' shape obligations are now SATISFIABLE (`SM 4697` has shape `[4096,1024]`,
  matching `intermediateGoal_4697.tsShape`; previously `[4096,16,64]` → structurally
  false). Full repo builds green (8560 jobs, 0 errors, 0 sorry); Pattern_1/2/4/5 are
  unaffected (their cut graphs use shape-preserving reshapes and the empty-params
  identity fallback is preserved). The manual `initGoal_4691` fix (b6e3506f, source
  leaf 4691 not multiref-copy 11853) and the topk_routing `[8]→[8,1]` explicit
  num_experts param (semantically identical: `params.getD 1 1 = 1` either way) were
  reconciled during regen.
- **NEW FRONTIER (next worker) — reshape commute PROVEN, cascade continues:**
  Worker #11 landed the **row-preserving reshape / dim-0 allGather commute** lemma
  `fw_view_allGather0_reshape_16_64_2` (axiom-clean: propext/Classical.choice/
  Quot.sound) plus the ring-denotation reshape reducer `ringAttn_reshape_reduce`
  (kernel-clean, no native_decide in-body) in
  `denote/yoco_goals/IntermediateReconstruction.lean`. Using them,
  **`recon_intermediateGoal_4697_ringAttn` is now proven UNCONDITIONAL over
  `denoteGraph_ringAttn`** (SM 4697 = allGather0[PM 7439, PM 7440]), chaining
  through Worker #9/#10's `recon_intermediateGoal_4696_ringAttn`. This is the first
  cascade goal unblocked by the params-aware regen. Baseline axioms = the 4696
  footprint (kernel triple + native_decide `Lean.ofReduceBool`), no new user axioms.
  The general reshape/allGather commute (`Denote.lean:22263`
  `fw_reshape_allGather0_commute_2`) still does NOT apply (it fails when the reshape
  crosses the shard boundary); the new lemma is the row-preserving special case.
  - **Remaining frontier:** the commute lemma is specialized to the
    `[2048,16,64]→[2048,1024]` shape. The next reshape goals in the residual stream
    (`4698` onward: residual-add → MoE → layer-1) need (a) the residual-add / MoE
    reconstruction gears, and (b) possibly further shape specializations of the
    reshape commute lemma for other tensor geometries. `recon_intermediateGoal_4697`
    is the template: `ringAttn_reshape_reduce` + a shape-matched commute lemma +
    `wrap_2tp_allGather_gen`. The attention gear `recon_attn_sliding_window_2tp_layer`
    plus this reshape template together unlock the layer-N attention→reshape prefix;
    the residual/MoE recon is the next missing piece for full per-layer cascade.

