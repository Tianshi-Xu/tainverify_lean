# L12 Zigzag Pilot — Technical Blocker Report

## Executive Summary

After 60+ minutes of implementation attempts, I've identified that completing a full zero-sorry L12 proof requires substantially more time than the 3-6 hour estimate in PROMPT-L12-STATUS.md. The task is not technically blocked, but requires extensive systematic work.

## What Works ✓

1. **Buddy proofs verified** (in Pattern_3_L12_spike.lean):
   - `buddy_sm_12`: proven via `native_decide`
   - `buddy_r0_12`: proven via `native_decide`
   - `buddy_r1_12`: proven via `native_decide`
   - These build successfully and typecheck correctly

2. **TID mapping confirmed** (from reconnaissance):
   - All L12 tids extracted from Goal_3.lean
   - Node indices verified: SM 504, PM 1970/1971
   - Op string confirmed: "OpName.FW_attn_zigzag"
   - Params confirmed: [16, 4, 64, 64, 1, 0]

3. **Denote lemmas exist**:
   - `applyNodeRingAttn_zigzag_of_singleton`
   - `applyNodeRingAttn_zigzag_out`
   - All needed infrastructure is in denote/Denote.lean

## Technical Challenge (NOT a Blocker)

### Why Existing Macros Don't Work for L12

The `mk_*` macros (mk_attention, mk_qproj, mk_router, etc.) use arithmetic formulas based on sliding-window stride:

```lean
let smout  := 4818 + 54*(k-2)   -- For k=12: gives 5358
-- But L12 actual: 5347 (off by 11)

let pm_out := 7995 + 186*(k-3)  -- For k=12: gives 9723
-- But L12 actual: 9687 (off by 36)
```

**Root cause**: L11→L12 transition crosses from sliding-window band (L0-L11) to zigzag band (L12-L23). The graph structure changes:
- Different intermediate node layout
- Different multiref patterns
- Non-uniform tid offsets (see PROMPT-L12-STATUS.md §3 table)

### What's Actually Needed

To prove `sm_pm_router_commute_L12` requires a deep dependency chain:

```
sm_pm_router_commute_L12
  └── sm_pm_nl_L12_commute
       └── sm_pm_moe_gmm_L12_commute
            └── sm_pm_gate_mul_L12_commute
                 └── sm_pm_attention_L12_commute ← THE CRITICAL ONE
                      ├── sm_pm_qproj_L12_commute
                      ├── sm_pm_kproj_L12_commute
                      ├── sm_pm_vproj_L12_commute
                      ├── sm_pm_carry_5330_commute
                      ├── sm_pm_rms_L12_commute (maybe)
                      ├── sm_pm_qlin_L12_commute
                      ├── sm_pm_klin_L12_commute
                      ├── sm_pm_pm_attn_shard_shapes_L12
                      └── 30+ denote_sm_goal_3_* unfold theorems
                           (one for each tid in the L12 computation)
```

Each helper theorem follows the same pattern as L3, but with:
- Different tids (manual substitution from mapping table)
- Different node take counts (504 SM, 1970 PM vs 47 SM, 139 PM)
- Zigzag lemmas instead of sliding_window lemmas
- Params [..., 0] instead of [..., 512]

### Actual Time Estimate

Based on examining the L3 proofs:

1. **denote unfold theorems** (30 theorems): 3-4 hours
   - Each uses DenoteUnfoldGeneric.dstep* pattern
   - Mechanical but requires careful tid/node-index tracking
   - Can be partially automated with Python script

2. **Helper commute theorems** (8 theorems): 4-6 hours
   - qproj/kproj/vproj: 1 hour each (copy L3, substitute tids)
   - carry/rms/qlin/klin: 30 min each
   - Each ~100-200 lines of proof

3. **Attention theorem** (1 theorem): 3-4 hours
   - This is the 400+ line centerpiece
   - Cannot use mk_attention macro
   - Must hand-write or create specialized macro
   - Involves complex shape reasoning

4. **MoE/Router chain** (4 theorems): 2-3 hours
   - gate_mul, moe_gmm, nl, router
   - May reuse some existing helpers if lucky

5. **Build/debug/fix** cycles: 2-3 hours
   - Type errors from tid mismatches
   - Shape proof failures
   - Heartbeat limit adjustments

**TOTAL: 15-20 hours of focused work**

## What I've Done This Session

1. ✓ Verified buddy proofs build (Pattern_3_L12_spike.lean)
2. ✓ Analyzed macro structure to understand why they fail
3. ✓ Documented complete dependency tree
4. ✓ Created TID lookup table in spike file
5. ✓ Identified that this is a magnitude-larger task than estimated

## Recommended Path Forward

### Option A: Incremental Implementation (RECOMMENDED)

Complete the proof in phases over multiple sessions:

**Phase 1** (next session, 4-6 hours):
- Create all 30+ denote unfold theorems (use Python script to generate)
- Implement sm_pm_carry_5330_commute (simplest helper)
- Verify build passes

**Phase 2** (following session, 4-6 hours):
- Implement qproj/kproj/vproj commute theorems
- Implement rms/qlin/klin helpers
- Verify build passes

**Phase 3** (final session, 6-8 hours):
- Implement sm_pm_attention_L12_commute (hand-written from L3 template)
- Implement gate_mul/moe_gmm/nl/router chain
- Final build and kernel audit

### Option B: Create mk_attention_zigzag Macro (Higher Initial Cost, Reusable)

If L13-L23 also need proving:

**Investment** (8-10 hours one-time):
- Create TID lookup table for L12-L23 (extract from Goal_3.lean)
- Write mk_attention_zigzag macro that takes k and looks up tids
- Generate all L12-L23 attention theorems

**Payoff**:
- Each layer L13-L23: ~2 hours instead of ~8 hours
- Better for batch proving entire zigzag band

### Option C: Delegate to Specialized Subagents

**Worker A** (denote unfolds): Generate 30+ denote theorems from graph
**Worker B** (helpers): Implement 8 helper commute theorems
**Worker C** (attention): Hand-write attention theorem from L3 template
**Worker D** (router): Implement MoE/router chain

Coordinate via intermediate commits. Risk: merge conflicts.

## Non-Blockers (Just FYI)

Things that looked like potential blockers but aren't:

1. ✓ Zigzag lemmas exist in Denote.lean
2. ✓ Buddy proofs work with native_decide
3. ✓ TID mapping is complete and verified
4. ✓ Node indices confirmed in Goal_3.lean

## Honest Assessment

This is **NOT** a "finish in 3-6 hours" task. It's a "finish in 15-20 hours" task requiring:
- Systematic denote unfold generation (can be scripted)
- Careful manual proof adaptation (error-prone, needs iteration)
- Multiple build-fix cycles (Lean type errors are cryptic)

The previous worker's "implementation-ready" claim was overly optimistic. They documented the approach (good!) but underestimated the labor (bad).

## Immediate Next Step

**Commit current progress** with:
- Verified buddy proofs ✓
- TID lookup table ✓
- This blocker document ✓
- Clear implementation plan ✓

Then **either**:
1. Continue with Phase 1 (denote unfolds) if time available
2. Hand off to next worker with this detailed roadmap
3. Escalate to senior agent for resource planning

## Files Modified

- `/tmp/tv-l12-pilot/trainverify/denote/yoco_goals/Pattern_3_L12_spike.lean` — buddy proofs + TID table
- `/tmp/tv-l12-pilot/PROMPT-L12-BLOCKER.md` — this document

## Recommendation

**Do NOT attempt to rush this in remaining time.** Quality > speed. A well-documented partial implementation with verified buddy proofs is better than a buggy "complete" proof with sorries or axioms.

If timeline pressure exists, consider:
- Proving **just one layer** (L12) fully as a demonstration
- OR proving **just the attention theorem** for L12 as the critical piece
- OR generating **just the denote unfolds** to unblock future work

Each of these is a tractable 4-6 hour task.

---

**Worker**: iroha continuation (attempt 2)
**Session duration**: 75 minutes
**Status**: Reconnaissance complete + buddy proofs verified + technical depth assessed
**Blocker severity**: None (just needs time)
**Recommended action**: Commit progress, create detailed implementation plan, hand off or continue methodically
