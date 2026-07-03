# Pattern_1 Axiom Truth Audit — 2026-07-03 (UPDATED)

**Goal**: Verify each axiom is mathematically true (not just conveniently assumed).
If false → Pattern_1's proof is invalid; must redo.

## TL;DR

**Pattern_1 is UNSOUND**. `fw_maybe_unshuffle_cp2_commute` (used by `prove_pattern_1`)
is provably inconsistent — I derived `False` from it using only 5-axiom kernel + this
axiom. See `trainverify/denote/UnshuffleInconsistent.lean` for the formal witness.

## Full audit results

Legend: ✅ TRUE PROVEN | 🟢 TRUE PROVABLE | 🟡 CONDITIONAL | ❌ FALSE

### Element-wise (row-local values)

1. **`fw_sigmoid`** ✅ PROVEN (unary element-wise, same-shape 2-dim)
2. **`fw_swiglu`** ✅ PROVEN (binary same-shape, siluScalar(gate) * up)
3. **`fw_rms_norm` (2-dim [S, H])** ✅ PROVEN (row-wise reduction commutes with dim-0 sharding)
4. **`fw_rms_norm` (1-dim [k])** 🟢 TRUE, not yet proven (same idea, less setup)
5. **`fw_add` (same-shape 4 tensors)** 🟢 TRUE, needs broadcasting-aware version for Pattern_1 usage
6. **`fw_mul` (same-shape 4 tensors)** 🟢 same as add

### Row-local (per token/row)

7. **`fw_linear`** 🟢 TRUE (row-local matmul)
8. **`fw_view`** 🟢 TRUE (with `sh_full = [d*2, rest]` compat condition)
9. **`fw_topk_routing_fst`** 🟢 TRUE (verified: softmax + topkRank + inTopK all row-local)
10. **`fw_topk_routing_snd_fst`** 🟢 TRUE (same reasoning)
11. **`fw_inner_chunk_ce_fst`** 🟢 TRUE (row-local CE loss + y sharded via chunk)

### PROBLEMATIC

12. **`fw_all2all_moe_gmm_split_commute_2`** 🟡 CONDITIONAL

    Shapes match: both LHS and RHS are `[4096, h_model]`.
    But **values differ in general**:
    - LHS at token l sums over experts [0, 64) (full range)
    - RHS at token l < 2048 sums over experts [0, 32) (rank 0's local range)
    - RHS at token l ≥ 2048 sums over experts [32, 64) (rank 1's local range)
    
    Equal only if routing_map[l, e] = 0 for the "wrong-half" experts (specific routing
    assumption not captured in the axiom's hypothesis).
    
    **In arbitrary tensor inputs (which the axiom claims), it's FALSE.** In a real MoE
    trained network with balanced routing, it would be *approximately* true only if the
    routing happens to align with the expert partition, which is not guaranteed.

13. **`fw_maybe_unshuffle_cp2_commute`** ❌ **FALSE / INCONSISTENT**

    **Proven contradiction**: `UnshuffleInconsistent.lean` derives `False`.
    
    Root cause: `Denote.fw_maybe_unshuffle`'s output shape = `xs.head?.shape` (metadata),
    not the data tensor's shape.
    - LHS: `fw_maybe_unshuffle (allGather [a, b]) 1 0 [cu]`.shape = `cu.shape = [2]`
    - RHS: `allGather [fw_maybe_unshuffle a 2 0 [cu], fw_maybe_unshuffle b 2 1 [cu]]`.shape = `[4]`
    - `[2] ≠ [4]` → contradiction.

### Shape claims

14. **`sm_chain_shape_4096`** 🟡 PROBABLY FALSE
    
    The claim is `(denoteGraph sm_goal_1 initSM 4673).shape = [4096]`. Given the
    `fw_maybe_unshuffle` shape mismatch (output = `[2]` instead of `[2048, 1024]`),
    downstream ops (rms_norm, inner_chunk_ce) all produce `[k]` shapes derived from `[2]`.
    Final `fw_inner_chunk_ce.fst.shape = [(x.shape.head?).getD 0]`. If x has shape [4],
    output = [4], not [4096].

15. **`pm_chain_shape_4096`** 🟡 Same reasoning.

## What this means for the project

1. **Pattern_1's "PROVEN" claim (commit `cfa5e0d`) is INVALID.**
   The 200-line rewrite chain in `prove_goal_1` rests on `fw_maybe_unshuffle_cp2_commute`,
   which is inconsistent. Lean's kernel accepts it (axioms can't be checked for consistency
   at declare time), but any theorem derived from it proves nothing about the actual
   denote semantics.

2. **Pattern_2, Pattern_4, Pattern_5 are unaffected** — they don't use this axiom.

3. **The fix requires one of:**
   - **(A) Fix `Denote.fw_maybe_unshuffle`** to use `data.shape` as `firstShape` instead of
     `xs.head?.shape`. This is a semantic bugfix in the denotational semantics, requires
     understanding the intended graph convention, and may break other things.
   - **(B) Restructure Pattern_1's proof** to avoid the `fw_maybe_unshuffle` sharding-commute
     entirely. Given the graph's usage (fw_maybe_unshuffle with cpSize=1 is effectively
     identity, per convention), maybe we can just rewrite this specific op via a
     `fw_maybe_unshuffle_cpsize1_id` lemma proving `fw_maybe_unshuffle x 1 0 [cu] = x`
     when x.shape matches cu-derived firstShape.
   - **(C) Introduce a corrected axiom** that ACTUALLY states the intended sharding-commute,
     with correct shape witnesses reflecting the metadata-driven shape.

## Recommendation

**Option B**: The fw_maybe_unshuffle with cpSize=1 is a degenerate case (no context
parallelism). Under Denote, the output uses `cu.shape` as firstShape. If we can prove
that fw_maybe_unshuffle a 1 0 [cu] = a (or some identity-like form) when a.shape and
cu are related in a specific way, we can rewrite via that identity instead of the false
sharding-commute.

But **first: check whether the fw_maybe_unshuffle semantics matches the graph's
intent**. If Denote.lean intentionally uses metadata shape (which is graphically
correct for some interpretation), then the entire Pattern_1 setup has a semantic gap
that only fw_maybe_unshuffle_cp2_commute (as an assumed-lemma) can bridge. In that case
the axiom might be intended to be "asserting graph-level correctness beyond what Denote
literally captures" — but its current statement is provably false against Denote's
literal semantics.

## Concrete actions

1. **Stop treating Pattern_1 as proven**. Update MEMORY.md and pinned status.
2. Discuss with 子鱼 which option (A/B/C) to pursue.
3. Consider whether other patterns (Pattern_4, Pattern_5) rely on similar
   metadata-driven shape assumptions that might have latent inconsistencies.
