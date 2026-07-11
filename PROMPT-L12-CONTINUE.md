# L12 zigzag pilot — CONTINUATION (attempt 2)

## Context

You are continuing an L12 zigzag-band proof in the trainverify Lean project.
A previous worker did reconnaissance (17min) and produced these artifacts on
branch `iroha-l12-pilot`, latest commit `fda59f3`:

- `PROMPT-L12-STATUS.md` — full tid mapping, sw→zz differences documented
- `FINAL_SUMMARY.md` — executive summary
- `L12_theorem_skeleton.lean` — skeleton at repo root (reference)
- `trainverify/denote/yoco_goals/Pattern_3_L12_spike.lean` — scratch module
  with 3 buddy proof skeletons using `native_decide`
- `extract_l12_tids.py` — TID extraction helper

**These are reconnaissance outputs, NOT a proof. The actual theorem
`sm_pm_router_commute_L12` does NOT exist yet.** Your job is to finish it.

## Verified facts (from previous reconnaissance)

- L12 SM attention: node index 504 in sm_goal_3, output tid 5347,
  ins=[5342,5343,5344,5345,5346], op="OpName.FW_attn_zigzag", params=[16,4,64,64,1,0]
- L12 PM r0: node index 1970, output 9687, ins=[9659,5343,5344,5345,5346]
- L12 PM r1: output 9688, ins=[9660,5343,5344,5345,5346]
- **Stride change**: sliding was SM=+54, PM=+186 per layer; zigzag is SM=+49,
  PM=+172. So `mk_router 12` won't just work — layer arithmetic differs.
- **Delta from k=3 (sliding base) to k=12 (zigzag base)** is non-uniform per
  tid role (see PROMPT-L12-STATUS.md §3 for full table). This means the
  existing `mk_*` macros using `+54*(k-3)` / `+186*(k-3)` formulas **do NOT
  extend to k=12 correctly**.

## Golden rule (子鱼's standing order)

Upstream fidelity first. **NO sorry. NO new axioms.** Kernel audit at the
end must return `[propext, Classical.choice, Quot.sound]` (plus
`Lean.ofReduceBool, Lean.trustCompiler` iff native_decide is used).

## Anti-quit clause (子鱼's iroha rule)

**DO NOT stop after 15-30 min claiming "reconnaissance complete" or
"implementation-ready".** The previous worker did that and got fired. You
inherit their reconnaissance. Your job is to **write proofs and make
`lake build` pass**, not to write more markdown. Estimated effort remaining:
3-6 hours of real work. Do the work.

If you get truly stuck (a real Lean error you cannot solve after ≥5 build
attempts on it), commit progress and write a specific technical blocker to
`PROMPT-L12-BLOCKER.md` — but only after real attempts, not preemptively.

## Task

### Concrete deliverable

`sm_pm_router_commute_L12` proven kernel-clean, in
`trainverify/denote/yoco_goals/Pattern_3.lean` (paste from spike after it
works). Plus every helper theorem it requires:

- `nSM_12`, `nR0_12`, `nR1_12` (already skeletoned in the spike file)
- `buddy_sm_12`, `buddy_r0_12`, `buddy_r1_12` (already skeletoned; **build
  and confirm they typecheck FIRST — the previous worker did not verify this**)
- `sm_pm_qproj_L12_commute`, `_kproj_L12`, `_vproj_L12` (try `mk_qproj 12`
  etc. first; may need forking due to stride change)
- `sm_pm_rms_L12`, `_qlin_L12`, `_klin_L12` (same — try existing macros)
- `sm_pm_carry_5330_commute` (if this is the L12 carry input tid; verify)
- `sm_pm_nl_L12_commute`
- `sm_pm_pm_attn_shard_shapes_L12` (via `mk_pm_attn_shard_shapes 12`?)
- `sm_pm_attention_L12_commute` — this is the one that MUST fork `mk_attention`
  because the op string and singleton-lemma names differ
- `sm_pm_gate_mul_L12_commute`, `sm_pm_moe_gmm_L12_commute`
- `sm_pm_router_commute_L12` — the top-level assembly (fork `mk_router`?)

### Approach

1. **Verify the spike file builds first**:
   ```
   cd /tmp/tv-l12-pilot/trainverify
   lake build denote.yoco_goals.Pattern_3_L12_spike
   ```
   If buddy proofs fail (native_decide might time out on cold build), fix
   BEFORE moving on. iroha already kicked off this build in the background
   as background PID unknown — you can also just re-run it.

2. **Try each existing macro with k=12** in the spike module:
   ```lean
   mk_rms 12
   mk_qlin 12
   mk_klin 12
   -- etc.
   ```
   Build after each. Note which ones fail. For failures, INSPECT the elab
   body — the tid formulas will be off due to the stride change. You may
   need to fork with a new elab (`mk_rms_zz` etc.) that uses the correct
   zigzag stride (49 SM, 172 PM), or just write out the L12 case by hand.

3. **Fork `mk_attention` → `mk_attention_zigzag`** (this is unavoidable
   because op-string differs):
   - Copy Pattern_3.lean lines 13455..~13860 verbatim
   - Substitute `"OpName.FW_attn_sliding_window"` → `"OpName.FW_attn_zigzag"`
   - Substitute `applyNodeRingAttn_sliding_window_of_singleton` → `_zigzag_of_singleton`
   - Substitute `applyNodeRingAttn_sliding_window_out` → `_zigzag_out`
   - Update tid arithmetic to use zigzag stride (49 SM, 172 PM) instead of (54, 186)
   - Update base offsets to L12 values from PROMPT-L12-STATUS.md
   - Rename generated theorem to `sm_pm_attention_L12_commute`

4. **Assemble `sm_pm_router_commute_L12`** — fork `mk_router` similarly if
   needed, or write out by hand mimicking L11 structure.

5. **Kernel audit**: append `#print axioms sm_pm_router_commute_L12` to the
   spike file. Verify output. Then paste the verified block into
   `denote/yoco_goals/Pattern_3.lean` AT THE END (after existing L0-L11
   material, before any final #check/#print), commit, push.

6. **Final build**: `lake build denote.yoco_goals.Pattern_3` MUST succeed.
   The full file is expected to take ~25-40 min to compile fresh; use the
   spike module for iteration, ONLY paste back to Pattern_3.lean at the end.

### Constraints

- Read `trainverify/AGENTS.md` if you haven't already. Rules #12, #19, #23,
  #26 apply here.
- **NO python bulk regex on Pattern_3.lean** (rule #26). Use targeted
  `patch` edits or write to scratch and cat-append.
- `set_option ... in` needs line comments not docstring (rule #23).
- If `native_decide` is slow on cold build, that's fine — commit and let
  it be.
- If a `mk_*` macro's elab call fails, DIAGNOSE the specific error, don't
  just abandon and hand-write everything. The macros save a LOT of code.

### Reporting

When you actually finish (theorem proven + kernel-clean), UPDATE
`PROMPT-L12-STATUS.md` with:
- Actual final SHAs
- `#print axioms sm_pm_router_commute_L12` output
- Which mk_* macros worked as-is vs needed forking
- Total build time

Commit + push to `iroha-l12-pilot`. Then stop.

If you hit a REAL blocker (not premature quit), commit progress and write
`PROMPT-L12-BLOCKER.md` with the exact Lean error, what you tried, and
your best hypothesis.

Godspeed. This time actually finish. — iroha
