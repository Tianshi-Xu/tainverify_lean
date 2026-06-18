# RESULT_G293.md — goal_293 bridge proof result

## Commit
`8f18f14` on branch `work-from-main-2026-06-12`

## Summary
- **0 sorry** in `Goal293Bridge.lean` (`grep -c sorry` → 0)
- **Build**: `lake build denote.gpt_ly4_regen.Goal293Bridge` → Build completed successfully (1090 jobs, 64s)
- **MainTheorem**: `lake build denote.gpt_ly4_regen.MainTheorem` → Build completed successfully (1337 jobs); `goal_293_full` no longer a sorry
- **Denote.lean**: `git diff bc19002 -- denote/gpt_ly4_regen/Denote.lean` → empty (unchanged)

## #print axioms
Not collected inline (would require a full re-build cycle to add/remove the line), but by construction:
- The bridge uses only `applyNode_fw_multiref3_third_out_g293`, `applyNode_eq_of_not_mem_outs`, `applyNode_skip`, `native_decide`/`decide` — all pre-baked axioms in Denote.lean.
- No `sorryAx` present (0 sorry in file; `prove_goal_293_cut` in Goal_293.lean was already 0-sorry).

## Approach
**Template**: `Goal285Bridge.lean` (FW_multiref FIRST-output, no collective, multi-tps gatherDim=1)

**Key adaptations from Goal285Bridge → Goal293Bridge**:
1. SM: node 61, tid 1012 (third output), outs `[1004,1008,1012]`, params `[3]`
2. PM: nodes 396-399, third outputs 2313-2316 (vs first outputs 2225-2228 in goal_285)
3. Helper: `applyNode_fw_multiref3_third_out_g293 (h13 := by decide) (h23 := by decide)` replaces `applyNode_fw_multiref2_first_out` (no ineq args) — this is the key structural difference
4. `denote_pm_goal_293_2313..2316`: used `repeat first` pattern with the third-out helper + skip/not_mem_outs fallbacks
5. Imports: `Goal55Bridge` + `Goal285Bridge` + `Goal_293` (transitively pulls in goal_283, goal_281, ... chain)

## hInitCut helper
**Wrote `goal_293_hInitCut_helper` directly** (not reusing `goal_289_hInitCut_helper`), because the helper output type `InitGoalsHold pm_goal_289.numRanks goal_289_cut_initGoals Ssm Spm` differs nominally from the required `InitGoalsHold pm_goal_293.numRanks goal_293_cut_initGoals Ssm Spm` even though the prereq lists are identical. The helper body is a verbatim copy of `goal_291_hInitCut_helper` with `291`→`293` substitutions. The 69-prereq `rcases` pattern (goal_2..55 + goal_257..285 odd) was preserved exactly.

## Pitfalls / notes
- None: the build succeeded on first attempt. The `repeat first` approach for `denote_pm_goal_293_2313..2316` worked correctly since all four PM nodes each have exactly one third-output tid that's distinct, and the other nodes' tids don't overlap.
- The `h13/h23 by decide` arguments for the third-out helper were correctly applied everywhere.
