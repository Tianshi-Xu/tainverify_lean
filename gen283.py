#!/usr/bin/env python3
SM_NODE=53; SM_OUT=981; SM_OUT_OTHER=977; SM_IN=628
MULTIREF_NODES=[346,347,348,349]; MULTIREF_RANK_IN=[2057,2058,2059,2060]
MULTIREF_OUTS=[(3557,3559),(3565,3567),(3573,3575),(3581,3583)]
A2A_NODES=[351,353,355,357]; A2A_OUTS=[2193,2194,2195,2196]
A2A_INS=[3559,3567,3575,3583]; IDIM,ODIM=2,1; PARAMS="[2, 1]"
PREREQS=list(range(2,50))+[257,259,261,263,265,267,269,271,273,275,277,279]
GI=49
out=[]
def w(s=""): out.append(s)

w("/- goal_283 bridge (prereqs=[2..49,257-279 odd]=60, same as goal_281). Reuse Goal281Bridge")
w("   FW_multiref params=[2] + AllToAll template, but take SECOND output 981.")
w("   SM=FW_multiref(628)->[977,981] node 53, second out 981=628 (applyNode_fw_multiref2_second_out_g283, needs hne).")
w("   PM=4xFW_multiref node 346-349 second outs 3559/3567/3575/3583=2057-2060,")
w("      4xAllToAllPrim(ins=[3559,3567,3575,3583],idim=2 odim=1)->2193-2196 node 351/353/355/357.")
w("   628=goal_49 [1,8,32] dim2-sharded tps 2057-2060 [1,8,8]. Bridge = frame only. -/")
w("import denote.gpt_ly4_regen.Goal49Bridge")
w("import denote.gpt_ly4_regen.Goal273Bridge")
w("import denote.gpt_ly4_regen.Goal275Bridge")
w("import denote.gpt_ly4_regen.Goal277Bridge")
w("import denote.gpt_ly4_regen.Goal279Bridge")
w("import denote.gpt_ly4_regen.Goal_283")
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
w(f"theorem denote_sm_goal_283_{SM_OUT} (s : Store) :")
w(f"    denoteGraph sm_goal_283 s {SM_OUT} = s {SM_IN} := by")
w("  simp only [sm_goal_283, denoteGraph, List.foldl]")
w(f"  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ {SM_IN} {SM_OUT_OTHER} {SM_OUT} (by decide)]")
w()
# SM frame
w(f"theorem sm_frame_{SM_OUT}_self (initSM : Store) :")
w(f"    denoteGraph sm initSM {SM_OUT} = denoteGraph sm_goal_283 (denoteGraph sm initSM) {SM_OUT} := by")
w(f"  rw [denote_sm_goal_283_{SM_OUT}]")
w(f"  rw [sm_val initSM {SM_NODE} {SM_OUT} (by native_decide) (by native_decide)]")
w(f"  rw [show sm.nodes[{SM_NODE}]'(by native_decide)")
w(f'      = {{ rank := 0, op := "OpName.FW_multiref", ins := [{SM_IN}], outs := [{SM_OUT_OTHER}, {SM_OUT}], params := [2] }}')
w("      from by native_decide]")
w(f"  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ {SM_IN} {SM_OUT_OTHER} {SM_OUT} (by decide)]")
w(f"  rw [sm_prefix_eq initSM {SM_NODE} {SM_IN} (by native_decide)]")
w()
# pm_full multiref second outs
for r in range(4):
    node=MULTIREF_NODES[r]; t1,t2=MULTIREF_OUTS[r]; xin=MULTIREF_RANK_IN[r]
    w(f"theorem pm_full_{t2} (initPM : Store) :")
    w(f"    denoteGraph pm initPM {t2} = denoteGraph pm initPM {xin} := by")
    w(f"  rw [pm_val initPM {node} {t2} (by native_decide) (by native_decide)]")
    w(f"  rw [show pm.nodes[{node}]'(by native_decide)")
    w(f'      = {{ rank := {r}, op := "OpName.FW_multiref", ins := [{xin}], outs := [{t1}, {t2}], params := [2] }}')
    w("      from by native_decide]")
    w(f"  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ {xin} {t1} {t2} (by decide)]")
    w(f"  rw [pm_prefix_eq initPM {node} {xin} (by native_decide)]")
    w()
# pm_full AllToAll outs
ains="\n           ".join([f"[denoteGraph pm initPM {A2A_INS[0]}, denoteGraph pm initPM {A2A_INS[1]},",
                         f"denoteGraph pm initPM {A2A_INS[2]}, denoteGraph pm initPM {A2A_INS[3]}]"])
for r in range(4):
    node=A2A_NODES[r]; o=A2A_OUTS[r]
    w(f"theorem pm_full_{o} (initPM : Store) :")
    w(f"    denoteGraph pm initPM {o}")
    w(f"      = allToAllPrimWithDims pm.numRanks {r}")
    w(f"          {ains} {IDIM} {ODIM} := by")
    w(f"  rw [pm_val initPM {node} {o} (by native_decide) (by native_decide)]")
    w(f"  rw [show pm.nodes[{node}]'(by native_decide)")
    w(f'      = {{ rank := {r}, op := "OpName.AllToAllPrim",')
    w(f"          ins := [{A2A_INS[0]}, {A2A_INS[1]}, {A2A_INS[2]}, {A2A_INS[3]}], outs := [{o}], params := {PARAMS} }}")
    w("      from by native_decide]")
    w("  rw [applyNode_allToAllPrimWithDims_out]")
    w("  simp only [List.map]")
    w(f"  rw [pm_prefix_eq initPM {node} {A2A_INS[0]} (by native_decide),")
    w(f"      pm_prefix_eq initPM {node} {A2A_INS[1]} (by native_decide),")
    w(f"      pm_prefix_eq initPM {node} {A2A_INS[2]} (by native_decide),")
    w(f"      pm_prefix_eq initPM {node} {A2A_INS[3]} (by native_decide)]")
    w()
# mini-graph AllToAll outs
asin="[s {0}, s {1}, s {2}, s {3}]".format(*MULTIREF_RANK_IN)
for r in range(4):
    o=A2A_OUTS[r]
    w(f"theorem denote_pm_goal_283_{o} (s : Store) :")
    w(f"    denoteGraph pm_goal_283 s {o}")
    w(f"      = allToAllPrimWithDims 4 {r} {asin} {IDIM} {ODIM} := by")
    w("  simp only [pm_goal_283, denoteGraph, List.foldl]")
    w("  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]")
    w("  rw [applyNode_allToAllPrimWithDims_out]")
    w("  simp only [List.map]")
    w("  repeat first")
    for k in range(4):
        w(f"    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ {MULTIREF_RANK_IN[k]} {MULTIREF_OUTS[k][0]} {MULTIREF_OUTS[k][1]} (by decide)]")
    w("    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]")
    w()
# pm_frame self
srw=", ".join([f"pm_full_{t2}" for (_,t2) in MULTIREF_OUTS])
for r in range(4):
    o=A2A_OUTS[r]
    w(f"theorem pm_frame_{o}_self (initPM : Store) :")
    w(f"    denoteGraph pm initPM {o} = denoteGraph pm_goal_283 (denoteGraph pm initPM) {o} := by")
    w(f"  rw [denote_pm_goal_283_{o}]")
    w(f"  rw [pm_full_{o}]")
    w(f"  rw [{srw}]")
    w("  rw [show pm.numRanks = 4 from by native_decide]")
    w()
# helper hInitCut
w("lemma goal_283_hInitCut_helper (Ssm Spm : Store)")
w("    (hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm)")
for g in PREREQS:
    w(f"    (hg{g} : InitGoalHolds pm.numRanks goal_{g} Ssm Spm)")
w("    : InitGoalsHold pm_goal_283.numRanks goal_283_cut_initGoals Ssm Spm := by")
w("  have hnr : pm_goal_283.numRanks = pm.numRanks := by native_decide")
w("  rw [hnr]; intro g hg")
w("  simp only [goal_283_cut_initGoals, goal_283_prereqs, List.mem_append] at hg")
w("  rcases hg with hg | hg")
w("  \u00b7 exact hinitC g hg")
w("  \u00b7 simp only [List.mem_cons, List.not_mem_nil, or_false] at hg")
w("    rcases hg with "+" | ".join(["rfl"]*len(PREREQS)))
for g in PREREQS:
    w(f"    \u00b7 exact hg{g}")
w()
# main
w("theorem goal_283_cut_to_full (h : goal_283_stmt_cut) : goal_283_stmt := by")
w("  intro initSM initPM hSM hPM hInit")
w("  set Ssm := denoteGraph sm initSM with hSsm")
w("  set Spm := denoteGraph pm initPM with hSpm")
for g in PREREQS:
    w(f"  have hg{g} := goal_{g}_intermediate initSM initPM hSM hPM hInit")
w("  have hinitC := initGoals_preserved initSM initPM hInit")
w("  have hnr : pm_goal_283.numRanks = pm.numRanks := by native_decide")
w("  have hInitCut : InitGoalsHold pm_goal_283.numRanks goal_283_cut_initGoals Ssm Spm :=")
w("    goal_283_hInitCut_helper Ssm Spm hinitC "+" ".join([f"hg{g}" for g in PREREQS]))
w(f"  have h628_smsh : (Ssm {SM_IN}).shape = [1, 8, 32] := by")
w(f"    have h := hg{GI}.1; simp only [goal_{GI}] at h; exact h")
w(f"  have hpmsh49 : (Spm {MULTIREF_RANK_IN[0]}).shape = [1,8,8] \u2227 (Spm {MULTIREF_RANK_IN[1]}).shape = [1,8,8] \u2227")
w(f"                 (Spm {MULTIREF_RANK_IN[2]}).shape = [1,8,8] \u2227 (Spm {MULTIREF_RANK_IN[3]}).shape = [1,8,8] := by")
w(f"    have h := hg{GI}.2.1")
w(f"    simp only [goal_{GI}, List.map, List.cons.injEq, and_true] at h")
w("    exact \u27e8h.1, h.2.1, h.2.2.1, h.2.2.2\u27e9")
w("  obtain \u27e8h2057sh, h2058sh, h2059sh, h2060sh\u27e9 := hpmsh49")
w("  have hSM283 : StoreShapesHold Ssm sm_goal_283InitEnv := by")
w("    intro tid sh hsh")
w("    rw [sm_goal_283InitEnv] at hsh")
w("    have hmem := mem_of_shapeEnvOfList_eq_some hsh")
w("    simp only [sm_goal_283InitShapes, List.mem_cons, List.not_mem_nil, or_false,")
w("               Prod.mk.injEq] at hmem")
w("    rcases hmem with \u27e8rfl, rfl\u27e9")
w("    \u00b7 exact h628_smsh")
w("  have hPM283 : StoreShapesHold Spm pm_goal_283InitEnv := by")
w("    intro tid sh hsh")
w("    rw [pm_goal_283InitEnv] at hsh")
w("    have hmem := mem_of_shapeEnvOfList_eq_some hsh")
w("    simp only [pm_goal_283InitShapes, List.mem_cons, List.not_mem_nil, or_false,")
w("               Prod.mk.injEq] at hmem")
w("    rcases hmem with \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9")
w("    \u00b7 exact h2057sh")
w("    \u00b7 exact h2058sh")
w("    \u00b7 exact h2059sh")
w("    \u00b7 exact h2060sh")
w("  have hcut := h Ssm Spm hSM283 hPM283 hInitCut")
w(f"  have hsmf : Ssm {SM_OUT} = denoteGraph sm_goal_283 Ssm {SM_OUT} := by")
w(f"    rw [hSsm]; exact sm_frame_{SM_OUT}_self initSM")
for o in A2A_OUTS:
    w(f"  have hpm{o} : Spm {o} = denoteGraph pm_goal_283 Spm {o} := by")
    w(f"    rw [hSpm]; exact pm_frame_{o}_self initPM")
w("  rw [hnr] at hcut")
w("  simp only [goal_283, List.map] at hcut \u22a2")
w("  rw [hsmf, "+", ".join([f"hpm{o}" for o in A2A_OUTS])+"]")
w("  exact hcut")
w()
w("theorem goal_283_intermediate (initSM initPM : Store)")
w("    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)")
w("    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :")
w("    InitGoalHolds pm.numRanks goal_283 (denoteGraph sm initSM) (denoteGraph pm initPM) := by")
w("  have hfull : goal_283_stmt := goal_283_cut_to_full prove_goal_283_cut")
w("  have := hfull initSM initPM hSM hPM hInit")
w("  simpa [InitGoalHolds, goal_283] using this")
w()
w("end TrainVerify.Denote.GeneratedGoals")

with open("trainverify/denote/gpt_ly4_regen/Goal283Bridge.lean","w") as f:
    f.write("\n".join(out)+"\n")
print("Generated Goal283Bridge.lean:", len(out), "lines, prereqs:", len(PREREQS))
