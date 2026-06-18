# TASK: Prove goal_58 bridge (Goal58Bridge.lean) — frame-only wrapper

## Repo / paths (ALL ABSOLUTE)
- Repo dir: `/home/argustest/.openclaw/workspace/tainverify_lean/trainverify`
- Active denote dir: `/home/argustest/.openclaw/workspace/tainverify_lean/trainverify/denote/gpt_ly4_regen`
- Build with: `cd /home/argustest/.openclaw/workspace/tainverify_lean/trainverify && lake env lean denote/gpt_ly4_regen/Goal58Bridge.lean`
- FILE TO CREATE: `/home/argustest/.openclaw/workspace/tainverify_lean/trainverify/denote/gpt_ly4_regen/Goal58Bridge.lean`

## What is already done (DO NOT touch)
- `denote/gpt_ly4_regen/Goal_58.lean` already contains a FULLY PROVEN `prove_goal_58_cut` (EXIT 0, axioms clean, no sorryAx). DO NOT modify it.
- The MainTheorem wiring (`goal_58_cut_to_full`) will be done by me afterward. DO NOT edit MainTheorem.lean.

## Your job
Create `Goal58Bridge.lean`, a FRAME-ONLY bridge proving:
```
theorem goal_58_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_58 (denoteGraph sm initSM) (denoteGraph pm initPM)
```
by adapting the EXISTING proven template `Goal56Bridge.lean` (same op = FW_linear + AllGather, frame-only).

## TEMPLATE = Goal56Bridge.lean (read it FIRST, in full)
`/home/argustest/.openclaw/workspace/tainverify_lean/trainverify/denote/gpt_ly4_regen/Goal56Bridge.lean`

goal_58 is structurally goal_56 with these DIFFERENCES (apply carefully):

| Aspect | goal_56 (template) | goal_58 (YOUR target) |
|---|---|---|
| SM op | FW_linear(1004,641)->642, SM node **62** | FW_linear(**1012,645**)->**646**, SM node **64** |
| PM per-rank op | FW_linear(**999**, 2257+r)->2261+r  (SHARED input 999) | FW_linear(**2313+r**, **645**)->2317+r  (PER-RANK input 2313-2316, REPLICATED weight 645) |
| PM FW_linear node idx | 406,407,408,409 | **400, 401, 402, 405** (note: rank3 is node 405, NOT 403/404) |
| AllGather | dim2, params=[2], node **415**, ins range `2261+r`, out **642** | dim**1**, params=**[1]**, node **414**, ins range `2317 + r`, out **646** |
| Upstream goal for input | goal_289 (single-tp 999) | **goal_293** (input 1012 dim1-gathered into 2313-2316) |
| Weight source | initGoal_641 (column-sharded, 2257-2260 each [8,32]) | **initGoal_645** (REPLICATED: SM 645 [32,32], PM 645 [32,32], SAME tid all ranks) |
| prereqs count | 70 | **70** (list = goal_58_prereqs in Goal_58.lean: [2..55, 257-285 odd, 293]) |
| import upstream bridge | Goal289Bridge | **Goal293Bridge** |

### Exact node facts (verified, use these in `show ... from by native_decide`)
SM node 64: `{ rank := 0, op := "OpName.FW_linear", ins := [1012, 645], outs := [646] }`
PM node 400: `{ rank := 0, op := "OpName.FW_linear", ins := [2313, 645], outs := [2317] }`
PM node 401: `{ rank := 1, op := "OpName.FW_linear", ins := [2314, 645], outs := [2318] }`
PM node 402: `{ rank := 2, op := "OpName.FW_linear", ins := [2315, 645], outs := [2319] }`
PM node 405: `{ rank := 3, op := "OpName.FW_linear", ins := [2316, 645], outs := [2320] }`
PM node 414: `{ rank := 0, op := "OpName.AllGatherPrim", ins := ((List.range 4).map (fun r => 2317 + r)), outs := [646], params := [1] }`

### Mini denote lemmas to write (adapt from denote_sm_goal_56_642 / denote_pm_goal_56_642)
- `denote_sm_goal_58_646 (s) : denoteGraph sm_goal_58 s 646 = fw_linear (s 1012) (s 645)`
  proof: `simp only [sm_goal_58, denoteGraph, List.foldl]; rw [applyNode_fw_linear_out]`
- `denote_pm_goal_58_646 (s) : denoteGraph pm_goal_58 s 646 = allGatherPrimDimN 1 4 0 [fw_linear (s 2313) (s 645), fw_linear (s 2314) (s 645), fw_linear (s 2315) (s 645), fw_linear (s 2316) (s 645)]`
  proof: `simp only [pm_goal_58, denoteGraph, List.foldl]; rw [applyNode_allGatherPrimDimN_out_thm]; simp only [List.map]; congr 1`
  (NOTE dim = **1** in allGatherPrimDimN, not 2)

### SM/PM self-frame lemmas (adapt sm_frame_642_self / pm_frame_642_self)
- `sm_frame_646_self`: use `sm_val initSM 64 646`, the `show sm.nodes[64] = {...FW_linear ins [1012,645] outs [646]} from by native_decide`, `applyNode_fw_linear_out`, then `sm_prefix_eq initSM 64 1012` and `sm_prefix_eq initSM 64 645`.
- per-rank `pm_full_2317 .. pm_full_2320`: like pm_full_2261..2264 but
  - node 400 -> out 2317, ins [2313,645]; node 401->2318 ins[2314,645]; node 402->2319 ins[2315,645]; node **405**->2320 ins[2316,645]
  - each: `pm_val initPM <node> <out>`, the show-node `from by native_decide`, `applyNode_fw_linear_out`, then `pm_prefix_eq initPM <node> <inputTid>` for BOTH the data tid (2313+r) and the weight tid (645).
- `pm_frame_646_self`: use `pm_val initPM 414 646`, the show-node for node 414 (AllGatherPrim range-form params=[1] out 646), `applyNode_allGatherPrimDimN_out_thm`, `simp only [List.range, List.range.loop, List.map]`, then `pm_prefix_eq initPM 414 2317 .. 2320`, then `rw [pm_full_2317, pm_full_2318, pm_full_2319, pm_full_2320]`, then `rw [show pm.numRanks = 4 from by native_decide]`.

### hInitCut helper
Adapt `goal_56_hInitCut_helper` -> `goal_58_hInitCut_helper`. The prereq hypotheses must EXACTLY match `goal_58_prereqs` from Goal_58.lean:
`[goal_2 .. goal_55] (i.e. 2,3,...,55) ++ [goal_257, goal_259, goal_261, goal_263, goal_265, goal_267, goal_269, goal_271, goal_273, goal_275, goal_277, goal_279, goal_281, goal_283, goal_285, goal_293]`.
NOTE: it ends in goal_**293** (not 289). The body pattern is identical to goal_56's helper (it destructs goal_58_cut_initGoals / goal_58_prereqs and discharges each InitGoalHolds by the matching hypothesis). Match the helper-body style of Goal56Bridge exactly (same `constructor`/`exact`/`decide` pattern it uses — read it).

### Final theorem body (adapt the goal_56 final block)
Use `goal_58_intermediate`-supporting block analogous to goal_56's. Key shape extractions:
- Input 1012 (SM) [1,8,32] and 999... NO — for goal_58 the PM per-rank inputs are 2313-2316 each [1,2,32], from **goal_293**. Extract via `goal_293`: hg293 gives SM 1012 shape [1,8,32] and PM 2313-2316 shapes [1,2,32]. (See how prove_goal_58_cut extracts hInitX from goal_293 — mirror that for the shape hyps you feed StoreShapesHold.)
- Weight 645 replicated: `initGoal_645` gives SM 645 [32,32] and PM 645 [32,32]. Get `hg645 := hinitC initGoal_645 (by simp only [initGoals]; decide)`.
- Build `hSM58 : StoreShapesHold Ssm sm_goal_58InitEnv` and `hPM58 : StoreShapesHold Spm pm_goal_58InitEnv` by `rcases` over the init shape list members (sm_goal_58InitShapes = [(645,[32,32]),(1012,[1,8,32])]; pm_goal_58InitShapes = [(645,[32,32]),(2313,[1,2,32]),(2314,..),(2315,..),(2316,..)]).
- Then `have hcut := h Ssm Spm hSM58 hPM58 hInitCut`, `hsmf`/`hpm646` from the self-frame lemmas, `rw [hnr] at hcut`, `simp only [goal_58, List.map] at hcut ⊢`, `rw [hsmf, hpm646]`, `exact hcut`.

The `goal_58_intermediate` closing theorem is the SAME shape as `goal_56_intermediate`:
```
theorem goal_58_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_58 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_58_stmt := goal_58_cut_to_full prove_goal_58_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_58] using this
```
BUT this requires `goal_58_cut_to_full` to exist — it is currently `sorry` in MainTheorem. So instead, the bridge must prove `goal_58_intermediate` DIRECTLY using the frame (do NOT rely on goal_58_cut_to_full). Mirror EXACTLY how Goal56Bridge proves goal_56_intermediate WITHOUT a cut_to_full dependency — i.e. it inlines the frame proof. READ the full goal_56_intermediate-supporting proof in Goal56Bridge.lean and replicate its structure; the bridge is self-contained (it imports Goal_56, calls `prove_goal_56_cut` as `h`, and frames it). Do the same with `prove_goal_58_cut` as `h`.

IMPORTANT: open the file, find where `prove_goal_56_cut` is referenced as the `h` argument and how `Ssm := denoteGraph sm initSM`, `Spm := denoteGraph pm initPM` are introduced (hSsm/hSpm). Replicate precisely with 58/646/1012/645/2313-2316/goal_293/initGoal_645 substitutions.

## Header / set_options (copy verbatim from Goal56Bridge, change imports)
```
import denote.gpt_ly4_regen.Goal293Bridge
import denote.gpt_ly4_regen.Goal_58
```
plus the same `set_option ...` block and `namespace TrainVerify.Denote.GeneratedGoals` / `open ...`.

## ACCEPTANCE (must all pass)
1. `cd /home/argustest/.openclaw/workspace/tainverify_lean/trainverify && lake env lean denote/gpt_ly4_regen/Goal58Bridge.lean` => EXIT 0, NO errors (warnings OK).
2. File ends with `theorem goal_58_intermediate ... ` proven (no `sorry`, no `admit`).
3. `grep -c sorry denote/gpt_ly4_regen/Goal58Bridge.lean` => 0.
4. DO NOT edit Goal_58.lean, GeneratedData.lean, or MainTheorem.lean.

## On failure
If a `native_decide` node lookup fails, RE-CHECK the node index against GeneratedData.lean (`def pm :` / `def sm :` blocks). If a shape extraction fails, read how prove_goal_58_cut (in Goal_58.lean) extracts the same shape and copy that exact extraction idiom. Iterate until EXIT 0. Report the final build output.
