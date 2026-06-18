You are extending a Python code generator that emits Lean 4 proof files. Work ONLY in:
/home/argustest/.openclaw/workspace/tainverify_lean/trainverify

GOAL: Make `bridge_emitter/emit2.py <N>` successfully generate + compile `GoalNBridge.lean`
for the MULTI-OUTPUT backward-pass goals (BW_linear / BW_matmul / BW_add / BW_layernorm).
The SINGLE-output BW ops already work. Read the full spec FIRST:
  bridge_emitter/BW_MULTI_SPEC.md

HARD RULES (violating any = failure):
- NEVER edit denote/Denote.lean, denote/gpt_ly4_regen/Denote.lean, or
  denote/gpt_ly4_regen/GeneratedData.lean. Verify they stay 0-diff with:
    git -C /home/argustest/.openclaw/workspace/tainverify_lean/trainverify status --short -- denote/Denote.lean denote/gpt_ly4_regen/GeneratedData.lean
  (must print nothing). Only edit bridge_emitter/*.py and the GoalNBridge.lean outputs.
- Do NOT touch any auth keys, env vars, or config. Do NOT run git commit / push.
- Do NOT wire anything into MainTheorem.lean.

WHAT EXISTS ALREADY (scaffolding in bridge_emitter/renderer_uni.py):
- `BW_MULTI` dict (op -> per-output applyNode lemma + projection ".1"/".2.1" + n_sidecond).
- `is_bw_multi(op)` helper.
- Single-output BW already handled in `_pointwise_expr` (the `op.startswith("BW_")` branch)
  and `_rhs_ins(node)`. Mirror these for multi-output.
- The existing `is_multirefN_nth` / `render_multirefN_nth` family is the CLOSEST analog
  (multi-output node, goal frames the n-th output) — study it and mirror its approach.

KEY FACTS (also in spec):
- The goal frames ONE output of the tuple. Which one = position of `lineage.ts` in the SM
  node's `outs` list (and `topo.final_tps` for PM). Use node.outs.index(framed_tid).
- applyNode lemmas (already in Denote.lean, reference them, supply ≠ side-conds as `(by decide)`):
  BW_linear: applyNode_bw_linear_fst_out (RHS (bw_linear g x w).1, 1 sidecond),
             applyNode_bw_linear_snd_out (.2, 1 sidecond)
  BW_matmul: applyNode_bw_matmul_fst_out (.1), applyNode_bw_matmul_snd_out (.2), 1 sidecond each
  BW_layernorm: applyNode_bw_layernorm_dx_out (.1, 0 sidecond),
                applyNode_bw_layernorm_dw_out (.2.1, 1 sidecond),
                applyNode_bw_layernorm_db_out (.2.2, 2 sidecond)
  BW_add 3-arg: applyNode_bw_add2_fst_out (.1, 1 sidecond) is generic;
    BW_add SECOND output has only `_gNNN` versions -> you must emit a PRIVATE goal-agnostic
    `_loc` copy named applyNode_bw_add2_snd_out_loc (mirror the existing OP_LOCAL_LEMMA
    mechanism for FW_div/FW_softmax; copy the body of applyNode_bw_add2_snd_out_g110 from
    Denote.lean, rename, drop the _gNNN suffix; it uses the generic evalOp_bw_add2 lemma).
- PM graph: ChunkPrim -> per-rank BW_op (multi-out) -> collective on the framed output.
  Reuse existing collective handling; only the per-rank BW node + SM node need the new
  multi-output applyNode lemma + projection.

VALIDATION LOOP (do this for real, iterate until clean):
1. Pick goal_239 first (BW_linear, single-tp, frames .1). To run emit2 you need its prereq
   bridges' OLEANS built. Simplest: instead of full emit, iterate using --no-compile to get
   the .lean, then `lake env lean denote/gpt_ly4_regen/Goal239Bridge.lean` and read errors.
   IGNORE `Unknown identifier goal_K_intermediate` errors (those are unbuilt prereqs =
   ordering, NOT your bug). FIX any `rewrite failed` / `unsolved goals` inside the
   sm_frame_/pm_frame_/pm_full_/denote_pm_ theorems — those are real.
   Build command for emit (writes .lean, compiles standalone):
     cd /home/argustest/.openclaw/workspace/tainverify_lean/trainverify
     python3 bridge_emitter/emit2.py 239 --no-compile 2>&1 | tail
     lake env lean denote/gpt_ly4_regen/Goal239Bridge.lean 2>&1 | grep -nE 'error|sorry' | head
2. Then test these representative goals (cover all cases), same loop:
   - goal_211 (BW_linear frames .2)         -> snd path
   - goal_235 (BW_matmul frames .1), goal_231 (BW_matmul .2)
   - goal_251 (BW_layernorm .1), goal_252 (.2.1=dw), goal_253 (.2.2=db)
   - goal_302 (BW_add .1), goal_250 (BW_add .2 -> tests the _loc snd lemma; trickiest)
3. A goal is DONE when `lake env lean GoalNBridge.lean` has NO `error` and NO `sorry`
   (except the allowed goal_K_intermediate ordering ones). When you finish a representative
   set with only-ordering errors left, you're done — report which goals you validated and
   what edits you made to renderer_uni.py.

Be surgical and keep the existing single-output + FW behavior intact. Write a short summary
to bridge_emitter/BW_MULTI_RESULT.md when done (what you changed, which goals validated,
any remaining issues).
