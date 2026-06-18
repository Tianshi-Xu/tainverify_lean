# Multi-output Backward-pass (BW) op renderer extension — SPEC

## Context
The bridge emitter (`bridge_emitter/renderer_uni.py`) auto-generates `GoalNBridge.lean`
files. SINGLE-output BW ops (BW_sum/gelu/view/transpose/contiguous/div/softmax/multiref)
are DONE and VALIDATED (goal_238 frames compiled clean). This spec covers the remaining
**multi-output BW ops**: `BW_linear`, `BW_matmul`, `BW_add` (3-arg), `BW_layernorm`.

Iron rule: NEVER edit `denote/Denote.lean`, `denote/gpt_ly4_regen/Denote.lean`,
or `GeneratedData.lean`. They must stay 0-diff. Only edit `bridge_emitter/*.py`.

## The structure
A multi-output BW op node produces a TUPLE of outputs, e.g.
`BW_linear ins=[gTid,xTid,wTid] outs=[dxTid, dwTid]` → `(bw_linear g x w).1` and `.2`.
The goal frames ONE of these outputs (which one = `lineage.ts` for SM; `topo.final_tps`
for PM). `ts` may be the 1st, 2nd, or 3rd output (see table below) — NOT always first.

This is structurally IDENTICAL to the existing `is_multirefN_nth` / `render_multirefN_nth`
family in renderer_uni.py (a multi-output node where the goal picks the n-th output).
Mirror that family's approach.

## Exact applyNode lemmas (already in Denote.lean — reference, do not redefine)
All take a `dxTid ≠ dwTid`-style side condition (supply via `(by decide)` or `(by native_decide)`).

BW_linear (outs=[dx,dw]):
  applyNode_bw_linear_fst_out (g s rank gTid xTid wTid dxTid dwTid) (_ : dxTid ≠ dwTid)
      ... dxTid = (bw_linear (s gTid) (s xTid) (s wTid)).1
  applyNode_bw_linear_snd_out (... ) (hne : dxTid ≠ dwTid)
      ... dwTid = (bw_linear (s gTid) (s xTid) (s wTid)).2

BW_matmul (outs=[dx,dy]):
  applyNode_bw_matmul_fst_out (gr s rank gTid xTid yTid dxTid dyTid) (_ : dxTid ≠ dyTid)
      ... dxTid = (bw_matmul (s gTid) (s xTid) (s yTid)).1
  applyNode_bw_matmul_snd_out (...) (hne : dxTid ≠ dyTid)
      ... dyTid = (bw_matmul (s gTid) (s xTid) (s yTid)).2

BW_add (3-arg, outs=[dx,dy]):  evalOp = (bw_add2 g x y) → [dx,dy]
  applyNode_bw_add2_fst_out (graph s rank gTid xTid yTid dxTid dyTid) (hne : dxTid ≠ dyTid)
      ... dxTid = (bw_add2 (s gTid) (s xTid) (s yTid)).1
  *** SECOND output has ONLY `_gNNN`-suffixed versions (applyNode_bw_add2_snd_out_g110 etc.) ***
      → must emit a PRIVATE goal-agnostic `_loc` copy (mirror OP_LOCAL_LEMMA mechanism).
      The gNNN body pattern (copy, rename, drop suffix):
        evalOp_bw_add2 numParts rank g x y = [(bw_add2 g x y).1, (bw_add2 g x y).2]  (exists, generic)
        unfold applyNode; rw [map=…, evalOp_bw_add2]; then storeSet picks dyTid (the .2);
        need dxTid ≠ dyTid to resolve storeSet. See existing applyNode_bw_add2_snd_out_g110.

BW_layernorm (outs=[dx,dw,db]):  evalOp = (bw_layernorm g x w b) → [dx,dw,db]
  applyNode_bw_layernorm_dx_out (g s rank gTid xTid wTid bTid dxTid dwTid dbTid)  -- NO side cond
      ... dxTid = (bw_layernorm (s gTid)(s xTid)(s wTid)(s bTid)).1
  applyNode_bw_layernorm_dw_out (...) (hne : dxTid ≠ dwTid)
      ... dwTid = (...).2.1
  applyNode_bw_layernorm_db_out (...) (hne1 : dxTid ≠ dbTid)(hne2 : dwTid ≠ dbTid)
      ... dbTid = (...).2.2
  (CONFIRM exact RHS tuple-projection shape by reading the lemma statements at
   Denote.lean lines ~7504/7517/7588.)

## Which output each goal frames (ts position among sm outs)
goal: smop outs ts -> position (1=fst .1, 2=snd, 3=third)
206 BW_add [994,836] 836 -> 2
208 BW_layernorm [1021,840,841] 840 -> 2
209 BW_layernorm [1021,840,841] 841 -> 3
210 BW_linear [842,843] 842 -> 1
211 BW_linear [842,843] 843 -> 2
213 BW_linear [845,846] 845 -> 1
214 BW_linear [845,846] 846 -> 2
215 BW_add [1025,847] 847 -> 2
217 BW_layernorm [1033,851,852] 851 -> 2
218 BW_layernorm [1033,851,852] 852 -> 3
220 BW_linear [1048,857] 857 -> 2
222 BW_linear [1052,859] 859 -> 2
224 BW_linear [1056,861] 861 -> 2
227 BW_matmul [864,869] 864 -> 1
231 BW_matmul [872,868] 868 -> 2
232 BW_matmul [864,869] 869 -> 2
235 BW_matmul [872,868] 872 -> 1
239 BW_linear [876,877] 876 -> 1
240 BW_linear [876,877] 877 -> 2
241 BW_add [1037,878] 878 -> 2
243 BW_layernorm [1064,882,883] 882 -> 2
244 BW_layernorm [1064,882,883] 883 -> 3
245 BW_linear [884,885] 884 -> 1
246 BW_linear [884,885] 885 -> 2
248 BW_linear [887,888] 887 -> 1
249 BW_linear [887,888] 888 -> 2
250 BW_add [1068,889] 889 -> 2
251 BW_layernorm [890,891,892] 890 -> 1
252 BW_layernorm [890,891,892] 891 -> 2
253 BW_layernorm [890,891,892] 892 -> 3
254 BW_linear [893,894] 893 -> 1
255 BW_linear [893,894] 894 -> 2
296 BW_layernorm [1021,840,841] 1021 -> 1
298 BW_add [1025,847] 1025 -> 1
300 BW_layernorm [1033,851,852] 1033 -> 1
302 BW_add [1037,878] 1037 -> 1
304 BW_linear [1048,857] 1048 -> 1
306 BW_linear [1052,859] 1052 -> 1
308 BW_linear [1056,861] 1056 -> 1
310 BW_layernorm [1064,882,883] 1064 -> 1
312 BW_add [1068,889] 1068 -> 1

NOTE the symmetry: e.g. 296/208/209 all share SM outs [1021,840,841] — they are the
.1/.2/.3 projections of the SAME layernorm node (296=dx, 208=dw, 209=db). The PM graph
also produces all three; each goal frames its own projection.

## PM-side structure
PM graph: ChunkPrim (shard inputs) → per-rank BW_op (4 ranks, each multi-out) →
collective (AllGather / AllReduce / CROSS_DP_WRED) on the selected output across ranks.
The PM frames the same n-th output, gathered. Reuse existing collective handling.

## Validation protocol (per goal)
1. `python3 bridge_emitter/emit2.py <N> --no-compile` → writes GoalNBridge.lean (probe needs
   prereq oleans built first — test on a goal whose prereqs are already built, OR build
   prereqs in topo order).
2. `lake env lean denote/gpt_ly4_regen/GoalNBridge.lean` → EXIT 0, no `error`, no `sorry`.
3. The ONLY acceptable transient error is `Unknown identifier goal_K_intermediate` for an
   unbuilt prereq K (ordering) — those resolve once K builds. Any BW-frame `rewrite failed`
   or `unsolved goals` in the sm_frame/pm_frame/pm_full/denote_pm theorems is a REAL bug to fix.
4. `#print axioms goal_N_intermediate` must show NO `sorryAx`; whitelist =
   propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound + the
   applyNode_* / fw_/bw_ domain axioms.

## Good first target
goal_239 (BW_linear, single-tp, frames .1=dx). Build its prereqs first (or pick a goal
whose prereqs are all already-built FW goals). goal_251 (BW_layernorm frames .1) tests the
3-output dx path. goal_211 (BW_linear frames .2) tests the snd path. goal_250 (BW_add
frames .2) tests the gNNN-only snd _loc lemma — the trickiest.

## Mechanism to mirror (in renderer_uni.py)
- `is_multirefN_nth(ir, topo)` + `render_multirefN_nth(...)` — the existing multi-output
  family. Add analogous `is_bw_multi(ir, topo)` + `render_bw_multi(...)`, dispatched in
  `render_universal` BEFORE `_check_supported`. OR extend POINTWISE-path to handle
  multi-output BW by selecting the right lemma + output projection + ≠ side-conditions.
- Output-projection RHS: `.1`, `.2.1`, `.2.2` etc. — read exact shape from the lemma stmts.
- For the per-rank PM nodes and the SM node, the applyNode lemma needs the `outs=[dx,dw(,db)]`
  literal (both/all outputs) even though only one is framed; the node literal already emits
  full outs. The ≠ side conditions are `(by decide)`.
