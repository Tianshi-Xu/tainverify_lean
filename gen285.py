#!/usr/bin/env python3
SM_NODE=59; SM_OUT=989; SM_OUT_OTHER=993; SM_IN=637
MR_NODES=[388,389,390,391]; MR_RANK_IN=[2201,2202,2203,2204]
# each node outs [first, second]
MR_OUTS=[(2225,2605),(2226,2606),(2227,2607),(2228,2608)]
FIRST_OUTS=[2225,2226,2227,2228]
PREREQS=list(range(2,55))+[257,259,261,263,265,267,269,271,273,275,277,279,281,283]
GIN=54   # goal_54 provides 637 + tps 2201-2204
out=[]
def w(s=""): out.append(s)

w("/- goal_285 bridge (prereqs=[2..54,257-283 odd]=67). FW_multiref params=[2] FIRST-output,")
w("   no collective, multi-tps gatherDim=1. SM=FW_multiref(637)->[989,993] node 59 take first 989=637.")
w("   PM=4xFW_multiref(2201+r)->[2225+?,2605+?] node 388-391 take first out 2225-2228 = each rank input 2201-2204.")
w("   637=goal_54 output [1,8,32] dim1-sharded tps 2201-2204 [1,2,32]. No AllToAll/AllGather.")
w("   Core semantics (multiref first-out copy) in prove_goal_285_cut. Bridge = frame only.")
w("   Template = Goal269Bridge (multiref no-collective) but FIRST output via generic")
w("   applyNode_fw_multiref2_first_out (no hne needed). Multiref nodes 388-391 adjacent. -/")
w("import denote.gpt_ly4_regen.Goal54Bridge")
w("import denote.gpt_ly4_regen.Goal283Bridge")
w("import denote.gpt_ly4_regen.Goal_285")
w()
for o in ["maxRecDepth 100000","maxHeartbeats 4000000","linter.style.nativeDecide false",
"linter.unusedSimpArgs false","linter.style.commandStart false","linter.unusedTactic false",
"linter.unreachableTactic false","linter.unusedVariables false","linter.style.show false",
"linter.style.setOption false","linter.unnecessarySeqFocus false","linter.flexible false"]:
    w("set_option "+o)
w()
w("namespace TrainVerify.Denote.GeneratedGoals")
w("open TrainVerify.Denote TrainVerify.Denote.Generated")
w()
# SM mini
w(f"theorem denote_sm_goal_285_{SM_OUT} (s : Store) :")
w(f"    denoteGraph sm_goal_285 s {SM_OUT} = s {SM_IN} := by")
w("  simp only [sm_goal_285, denoteGraph, List.foldl]")
w("  rw [applyNode_fw_multiref2_first_out]")
w()
# SM frame
w(f"theorem sm_frame_{SM_OUT}_self (initSM : Store) :")
w(f"    denoteGraph sm initSM {SM_OUT} = denoteGraph sm_goal_285 (denoteGraph sm initSM) {SM_OUT} := by")
w(f"  rw [denote_sm_goal_285_{SM_OUT}]")
w(f"  rw [sm_val initSM {SM_NODE} {SM_OUT} (by native_decide) (by native_decide)]")
w(f"  rw [show sm.nodes[{SM_NODE}]'(by native_decide)")
w(f'      = {{ rank := 0, op := "OpName.FW_multiref", ins := [{SM_IN}], outs := [{SM_OUT}, {SM_OUT_OTHER}], params := [2] }}')
w("      from by native_decide]")
w("  rw [applyNode_fw_multiref2_first_out]")
w(f"  rw [sm_prefix_eq initSM {SM_NODE} {SM_IN} (by native_decide)]")
w()
# pm_full first outs
for r in range(4):
    node=MR_NODES[r]; t1,t2=MR_OUTS[r]; xin=MR_RANK_IN[r]
    w(f"theorem pm_full_{t1} (initPM : Store) :")
    w(f"    denoteGraph pm initPM {t1} = denoteGraph pm initPM {xin} := by")
    w(f"  rw [pm_val initPM {node} {t1} (by native_decide) (by native_decide)]")
    w(f"  rw [show pm.nodes[{node}]'(by native_decide)")
    w(f'      = {{ rank := {r}, op := "OpName.FW_multiref", ins := [{xin}], outs := [{t1}, {t2}], params := [2] }}')
    w("      from by native_decide]")
    w("  rw [applyNode_fw_multiref2_first_out]")
    w(f"  rw [pm_prefix_eq initPM {node} {xin} (by native_decide)]")
    w()
# mini-graph denote_pm first outs (robust repeat-first pattern)
for r in range(4):
    t1=FIRST_OUTS[r]; xin=MR_RANK_IN[r]
    w(f"theorem denote_pm_goal_285_{t1} (s : Store) :")
    w(f"    denoteGraph pm_goal_285 s {t1} = s {xin} := by")
    w("  simp only [pm_goal_285, denoteGraph, List.foldl]")
    w("  repeat first")
    w("    | rw [applyNode_fw_multiref2_first_out]")
    w("    | rw [applyNode_skip _ _ _ "+str(t1)+" (by decide)]")
    w("    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]")
    w()
# pm_frame self
for r in range(4):
    t1=FIRST_OUTS[r]
    w(f"theorem pm_frame_{t1}_self (initPM : Store) :")
    w(f"    denoteGraph pm initPM {t1} = denoteGraph pm_goal_285 (denoteGraph pm initPM) {t1} := by")
    w(f"  rw [denote_pm_goal_285_{t1}]")
    w(f"  exact pm_full_{t1} initPM")
    w()
# helper hInitCut
w("lemma goal_285_hInitCut_helper (Ssm Spm : Store)")
w("    (hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm)")
for g in PREREQS:
    w(f"    (hg{g} : InitGoalHolds pm.numRanks goal_{g} Ssm Spm)")
w("    : InitGoalsHold pm_goal_285.numRanks goal_285_cut_initGoals Ssm Spm := by")
w("  have hnr : pm_goal_285.numRanks = pm.numRanks := by native_decide")
w("  rw [hnr]; intro g hg")
w("  simp only [goal_285_cut_initGoals, goal_285_prereqs, List.mem_append] at hg")
w("  rcases hg with hg | hg")
w("  \u00b7 exact hinitC g hg")
w("  \u00b7 simp only [List.mem_cons, List.not_mem_nil, or_false] at hg")
w("    rcases hg with "+" | ".join(["rfl"]*len(PREREQS)))
for g in PREREQS:
    w(f"    \u00b7 exact hg{g}")
w()
# main
w("theorem goal_285_cut_to_full (h : goal_285_stmt_cut) : goal_285_stmt := by")
w("  intro initSM initPM hSM hPM hInit")
w("  set Ssm := denoteGraph sm initSM with hSsm")
w("  set Spm := denoteGraph pm initPM with hSpm")
for g in PREREQS:
    w(f"  have hg{g} := goal_{g}_intermediate initSM initPM hSM hPM hInit")
w("  have hinitC := initGoals_preserved initSM initPM hInit")
w("  have hnr : pm_goal_285.numRanks = pm.numRanks := by native_decide")
w("  have hInitCut : InitGoalsHold pm_goal_285.numRanks goal_285_cut_initGoals Ssm Spm :=")
w("    goal_285_hInitCut_helper Ssm Spm hinitC "+" ".join([f"hg{g}" for g in PREREQS]))
# shapes: 637 = goal_54.ts [1,8,32]; tps 2201-2204 each [1,2,32]
w(f"  have h637_smsh : (Ssm {SM_IN}).shape = [1, 8, 32] := by")
w(f"    have h := hg{GIN}.1; simp only [goal_{GIN}] at h; exact h")
w(f"  have hpmsh : (Spm {MR_RANK_IN[0]}).shape = [1,2,32] \u2227 (Spm {MR_RANK_IN[1]}).shape = [1,2,32] \u2227")
w(f"               (Spm {MR_RANK_IN[2]}).shape = [1,2,32] \u2227 (Spm {MR_RANK_IN[3]}).shape = [1,2,32] := by")
w(f"    have h := hg{GIN}.2.1")
w(f"    simp only [goal_{GIN}, List.map, List.cons.injEq, and_true] at h")
w("    exact \u27e8h.1, h.2.1, h.2.2.1, h.2.2.2\u27e9")
w("  obtain \u27e8h2201sh, h2202sh, h2203sh, h2204sh\u27e9 := hpmsh")
w("  have hSM285 : StoreShapesHold Ssm sm_goal_285InitEnv := by")
w("    intro tid sh hsh")
w("    rw [sm_goal_285InitEnv] at hsh")
w("    have hmem := mem_of_shapeEnvOfList_eq_some hsh")
w("    simp only [sm_goal_285InitShapes, List.mem_cons, List.not_mem_nil, or_false,")
w("               Prod.mk.injEq] at hmem")
w("    rcases hmem with \u27e8rfl, rfl\u27e9")
w("    \u00b7 exact h637_smsh")
w("  have hPM285 : StoreShapesHold Spm pm_goal_285InitEnv := by")
w("    intro tid sh hsh")
w("    rw [pm_goal_285InitEnv] at hsh")
w("    have hmem := mem_of_shapeEnvOfList_eq_some hsh")
w("    simp only [pm_goal_285InitShapes, List.mem_cons, List.not_mem_nil, or_false,")
w("               Prod.mk.injEq] at hmem")
w("    rcases hmem with \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9")
w("    \u00b7 exact h2201sh")
w("    \u00b7 exact h2202sh")
w("    \u00b7 exact h2203sh")
w("    \u00b7 exact h2204sh")
w("  have hcut := h Ssm Spm hSM285 hPM285 hInitCut")
w(f"  have hsmf : Ssm {SM_OUT} = denoteGraph sm_goal_285 Ssm {SM_OUT} := by")
w(f"    rw [hSsm]; exact sm_frame_{SM_OUT}_self initSM")
for o in FIRST_OUTS:
    w(f"  have hpm{o} : Spm {o} = denoteGraph pm_goal_285 Spm {o} := by")
    w(f"    rw [hSpm]; exact pm_frame_{o}_self initPM")
w("  rw [hnr] at hcut")
w("  simp only [goal_285, List.map] at hcut \u22a2")
w("  rw [hsmf, "+", ".join([f"hpm{o}" for o in FIRST_OUTS])+"]")
w("  exact hcut")
w()
w("theorem goal_285_intermediate (initSM initPM : Store)")
w("    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)")
w("    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :")
w("    InitGoalHolds pm.numRanks goal_285 (denoteGraph sm initSM) (denoteGraph pm initPM) := by")
w("  have hfull : goal_285_stmt := goal_285_cut_to_full prove_goal_285_cut")
w("  have := hfull initSM initPM hSM hPM hInit")
w("  simpa [InitGoalHolds, goal_285] using this")
w()
w("end TrainVerify.Denote.GeneratedGoals")

with open("trainverify/denote/gpt_ly4_regen/Goal285Bridge.lean","w") as f:
    f.write("\n".join(out)+"\n")
print("Generated Goal285Bridge.lean:", len(out), "lines, prereqs:", len(PREREQS))
