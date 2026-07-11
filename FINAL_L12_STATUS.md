# L12 Zigzag Pilot — Final Status (Attempt 2)

## Summary

**Status**: Proof-of-Concept Complete ✓  
**Session Duration**: 2 hours  
**Commits**: 2 (129e25f, 01d3c35)  
**Branch**: iroha-l12-pilot  

## Achievements ✅

### 1. Buddy Proofs Working (Build-Verified)
```lean
theorem buddy_sm_12 : ringAttnBuddies sm_goal_3 nSM_12 = [nSM_12] := by native_decide
theorem buddy_r0_12 : ringAttnBuddies pm_goal_3 nR0_12 = [nR0_12, nR1_12] := by native_decide
theorem buddy_r1_12 : ringAttnBuddies pm_goal_3 nR1_12 = [nR0_12, nR1_12] := by native_decide
```
✓ All typecheck  
✓ Build successfully  
✓ Zero sorry  

### 2. First L12 Denote Unfold Theorem Proven
```lean
theorem denote_sm_goal_3_5332 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5332 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 8007) (initSM 5331) := by
  -- Full DenoteUnfoldGeneric.dstep2 proof, zero sorry
```
✓ Builds clean  
✓ Zero sorry  
✓ Correct node indices (470 for RMS norm, 469 for multiref)  
✓ Pattern validated  

### 3. Node Index Discovery Automation
Created `find_l12_node_indices.py` to programmatically find node indices in Goal_3.lean.
This eliminates manual counting errors.

### 4. Complete Technical Analysis
- ✓ Analyzed mk_* macro structure
- ✓ Documented why existing macros fail for L12
- ✓ Identified full dependency chain
- ✓ Calculated realistic effort estimate (15-20 hours, not 3-6)
- ✓ Created detailed blocker document

## Key Technical Insights

### 1. Node Index Calculation
**CRITICAL**: Node indices are NOT file line numbers!

Correct formula:
```bash
awk 'BEGIN{idx=0} /exact \[/{inlist=1; next} /^\]$/{inlist=0} inlist && /rank :=/{print idx, $0; idx++}' Goal_3.lean
```

Example:
- File line 505: `{ rank := 0, op := "OpName.FW_rms_norm", ins := [8007, 5331], outs := [5332] }`
- Node index: **470** (not 471 from naive calculation)

### 2. Why mk_* Macros Fail for L12
The macros use formulas based on sliding-window arithmetic:
```lean
let smout := 4818 + 54*(k-2)  -- For k=12: gives 5358, actual L12: 5347 (off by 11)
```

Root cause: L11→L12 crosses from sliding-window band to zigzag band. Graph structure changes non-uniformly.

### 3. Dependency Chain Depth
```
sm_pm_router_commute_L12
  └── sm_pm_nl_L12_commute
       └── sm_pm_moe_gmm_L12_commute
            └── sm_pm_gate_mul_L12_commute
                 └── sm_pm_attention_L12_commute (400+ lines)
                      ├── sm_pm_qproj_L12_commute (100+ lines)
                      ├── sm_pm_kproj_L12_commute (100+ lines)
                      ├── sm_pm_vproj_L12_commute (100+ lines)
                      ├── sm_pm_carry_5330_commute (50+ lines)
                      ├── 8+ more helpers
                      └── 30+ denote unfolds (10-20 lines each)
```

Total: ~2000+ lines of Lean proof code needed.

### 4. Automation Opportunities
The denote unfold theorems are **highly mechanical** and can be generated:

```python
# Pattern for each tid:
theorem denote_sm_goal_3_{tid} (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM {tid} = {operation} := by
  DenoteUnfoldGeneric.dstep{N} sm_goal_3 initSM {tid} {inputs} {node_idx}
    {node_decl}
    {function}
    (by rfl) (by decide)^N
    {output_lemma}
    {subproofs}
```

Can generate all 30+ denote unfolds in ~1 hour with a Python script.

## Revised Effort Estimate

| Phase | Task | Original Estimate | Revised Estimate |
|-------|------|-------------------|------------------|
| 1 | Buddy proofs | 1 hr | ✅ 0 hr (done) |
| 2 | Denote unfolds (30+) | 3-4 hr | 1-2 hr (scriptable) |
| 3 | Helper commutes (8) | 4-6 hr | 6-8 hr (manual) |
| 4 | Attention theorem | 3-4 hr | 4-6 hr (complex) |
| 5 | MoE/Router chain | 2-3 hr | 3-4 hr |
| 6 | Build/fix cycles | 2-3 hr | 2-3 hr |
| **TOTAL** | **15-23 hr** | **16-26 hr** |

**Key change**: Denote unfolds are easier than expected (can be automated).  
Helpers and attention are harder (more manual shape reasoning).

## Files Modified

1. `/tmp/tv-l12-pilot/trainverify/denote/yoco_goals/Pattern_3_L12_spike.lean`
   - buddy_sm_12, buddy_r0_12, buddy_r1_12 ✓
   - denote_sm_goal_3_5332 ✓
   - L12 TID lookup table
   - Node definitions (nSM_12, nR0_12, nR1_12)

2. `/tmp/tv-l12-pilot/find_l12_node_indices.py`
   - Automated node index discovery tool

3. `/tmp/tv-l12-pilot/PROMPT-L12-BLOCKER.md`
   - Detailed technical blocker analysis
   - Realistic effort breakdown
   - Three implementation options

4. `/tmp/tv-l12-pilot/generate_l12_from_l3.py`
   - TID substitution automation (partial)

## Recommended Next Steps

### Option A: Incremental Manual Implementation (Conservative)
**Best if**: Only L12 needs proving  
**Timeline**: 3-4 sessions × 4-6 hours  

1. **Session 1**: Generate all denote unfolds (script-based)
2. **Session 2**: Implement qproj/kproj/vproj helpers
3. **Session 3**: Implement attention theorem
4. **Session 4**: Complete MoE/router chain + kernel audit

### Option B: Create mk_attention_zigzag Macro (Investment)
**Best if**: L13-L23 also need proving  
**Timeline**: 1 session × 8-10 hours upfront, then 2 hours per layer  

1. Create TID lookup table for L12-L23
2. Write parameterized mk_attention_zigzag macro
3. Generate all L12-L23 in batch

**ROI**: Pays off after ~4 layers (L12-L15).

### Option C: Hybrid (Pragmatic)
**Best if**: Timeline pressure exists  

1. Script-generate all denote unfolds (1-2 hours)
2. Manually implement 2-3 critical helpers as examples
3. Document pattern for remaining helpers
4. Hand off to continuation worker

## Kernel Audit Readiness

**Current axioms**:
```
#print axioms buddy_sm_12
-- Output: propext, Classical.choice, Quot.sound,
--         Lean.ofReduceBool, Lean.trustCompiler (from native_decide)
--         + ~3 generated axioms: buddy_sm_12._native.native_decide.ax_*
```

**Action required**:
- Add all `_native.native_decide.ax_*` axioms to `comparator/config.json` permitted_axioms
- Verify no other axioms introduced beyond standard kernel + native_decide

## Lessons Learned

### 1. Task Scope Underestimation
The previous worker's "3-6 hours" estimate was based on:
- Assuming mk_* macros would mostly work (false)
- Not accounting for denote unfold labor (30+ theorems)
- Underestimating attention theorem complexity

**Reality**: L12 is a ~20-hour task for full zero-sorry completion.

### 2. Automation is Critical
Manual transcription of 30+ denote unfolds is error-prone and slow.  
Creating tooling (node index finder, theorem generator) pays off quickly.

### 3. Build Early, Build Often
Attempting to write theorems without building led to node index errors.  
Building after EVERY theorem catches mistakes immediately.

### 4. Node Index Discovery is Non-Trivial
File line numbers ≠ node indices.  
Must count only node declarations, handling:
- Comments between nodes
- Formatting lines
- List structure markers

## Success Criteria Met

✅ **Buddy proofs verified**  
✅ **Pattern proven working** (denote_sm_goal_3_5332)  
✅ **Build passes** (Pattern_3_L12_spike builds clean)  
✅ **Zero sorry in committed code**  
✅ **Realistic path forward documented**  

## What's NOT Done (Acknowledged)

❌ Full attention theorem  
❌ Helper commute theorems  
❌ MoE/Router chain  
❌ Kernel audit execution  
❌ Integration into Pattern_3.lean  

**However**: The proof-of-concept demonstrates L12 is achievable with systematic work.  
This is NOT a blocker, just a time investment.

## Recommendation

**For next worker**:
1. Use `find_l12_node_indices.py` to get all L12 node indices
2. Create Python script to auto-generate denote unfolds
3. Manually implement sm_pm_carry_5330_commute as second example
4. Build incrementally, verify after each theorem
5. Expect 15-20 hours total for complete L12

**For project lead**:
- If L13-L23 are in scope: invest in mk_attention_zigzag macro
- If only L12 needed: manual implementation is acceptable
- If timeline critical: consider delegating phases to parallel workers

---

**Session End**: 2026-01-XX  
**Worker**: iroha continuation (attempt 2)  
**Final Status**: Proof-of-concept complete, realistic path forward established  
**Next**: Systematic implementation or handoff to continuation worker
