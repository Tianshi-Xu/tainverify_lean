#!/usr/bin/env python3
SM_NODE=58; SM_OUT=637; SM_INS=[981,636]
A2A_NODES=[380,381,382,383]; A2A_OUTS=[2197,2198,2199,2200]; A2A_INS_BASE=2169
ADD_NODES=[384,385,386,387]; ADD_OUTS=[2201,2202,2203,2204]; ADD_PREREQ_INS=[2193,2194,2195,2196]
IDIM,ODIM=2,1; PARAMS="[2, 1]"
PREREQS=list(range(2,54))+[257,259,261,263,265,267,269,271,273,275,277,279,281,283]
GIN_981=283; GIN_636=53
out=[]
def w(s=""): out.append(s)

w("/- goal_54 bridge (prereqs=[2..53,257-283 odd]=66). FW_add over AllToAll-reshard dim2->1,")
w("   multi-tps gatherDim=1. SM=FW_add(981,636)->637 node 58 [1,8,32].")
w("   PM=4xAllToAllPrim(2169-2172,idim=2 odim=1)->2197-2200 node 380-383 params=[2,1],")
w("      4xFW_add(2193+r,2197+r)->2201-2204 node 384-387 dim1-sharded [1,2,32].")
w("   636=goal_53 (FW_linear column-parallel gatherDim=2 tps 2169-2172 [1,8,8]).")
w("   981=goal_283 (FW_multiref second-out gatherDim=1 tps 2193-2196 [1,2,32]).")
w("   AllToAll reshards dim2-sharded 636 into dim1-chunks, each rank FW_add with 2193-2196.")
w("   Core semantics in prove_goal_54_cut. Bridge = frame only. Template = Goal29Bridge")
w("   (FW_add+AllToAll) with AllToAll dir dim1->2 (params=[1,2]) swapped to dim2->1 (params=[2,1]). -/")
w("import denote.gpt_ly4_regen.Goal53Bridge")
w("import denote.gpt_ly4_regen.Goal283Bridge")
w("import denote.gpt_ly4_regen.Goal_54")
w()
for o in ["maxRecDepth 100000","maxHeartbeats 0","linter.style.nativeDecide false",
"linter.unusedSimpArgs false","linter.style.commandStart false","linter.unusedTactic false",
"linter.unreachableTactic false","linter.unusedVariables false","linter.style.show false",
"linter.style.setOption false","linter.unnecessarySeqFocus false","linter.flexible false"]:
    w("set_option "+o)
w()
w("namespace TrainVerify.Denote.GeneratedGoals")
w("open TrainVerify.Denote TrainVerify.Denote.Generated")
w()
# SM mini
w(f"theorem denote_sm_goal_54_{SM_OUT} (s : Store) :")
w(f"    denoteGraph sm_goal_54 s {SM_OUT} = elemwiseAdd (s {SM_INS[0]}) (s {SM_INS[1]}) := by")
w("  simp only [sm_goal_54, denoteGraph, List.foldl]")
w("  rw [applyNode_fw_add2_out]")
w()
# SM frame
w(f"theorem sm_frame_{SM_OUT}_self (initSM : Store) :")
w(f"    denoteGraph sm initSM {SM_OUT} = denoteGraph sm_goal_54 (denoteGraph sm initSM) {SM_OUT} := by")
w(f"  rw [denote_sm_goal_54_{SM_OUT}]")
w(f"  rw [sm_val initSM {SM_NODE} {SM_OUT} (by native_decide) (by native_decide)]")
w(f"  rw [show sm.nodes[{SM_NODE}]'(by native_decide)")
w(f'      = {{ rank := 0, op := "OpName.FW_add", ins := [{SM_INS[0]}, {SM_INS[1]}], outs := [{SM_OUT}] }}')
w("      from by native_decide]")
w("  rw [applyNode_fw_add2_out]")
w(f"  rw [sm_prefix_eq initSM {SM_NODE} {SM_INS[0]} (by native_decide),")
w(f"      sm_prefix_eq initSM {SM_NODE} {SM_INS[1]} (by native_decide)]")
w()
# pm_full AllToAll outs
ains="\n           ".join([f"[denoteGraph pm initPM {A2A_INS_BASE}, denoteGraph pm initPM {A2A_INS_BASE+1},",
                         f"denoteGraph pm initPM {A2A_INS_BASE+2}, denoteGraph pm initPM {A2A_INS_BASE+3}]"])
for r in range(4):
    node=A2A_NODES[r]; o=A2A_OUTS[r]
    w(f"theorem pm_full_{o} (initPM : Store) :")
    w(f"    denoteGraph pm initPM {o}")
    w(f"      = allToAllPrimWithDims pm.numRanks {r}")
    w(f"          {ains} {IDIM} {ODIM} := by")
    w(f"  rw [pm_val initPM {node} {o} (by native_decide) (by native_decide)]")
    w(f"  rw [show pm.nodes[{node}]'(by native_decide)")
    w(f'      = {{ rank := {r}, op := "OpName.AllToAllPrim",')
    w(f"          ins := ((List.range 4).map (fun r => {A2A_INS_BASE} + r)), outs := [{o}], params := {PARAMS} }}")
    w("      from by native_decide]")
    w("  rw [applyNode_allToAllPrimWithDims_out]")
    w("  simp only [List.range, List.range.loop, List.map]")
    w(f"  rw [pm_prefix_eq initPM {node} {A2A_INS_BASE} (by native_decide),")
    w(f"      pm_prefix_eq initPM {node} {A2A_INS_BASE+1} (by native_decide),")
    w(f"      pm_prefix_eq initPM {node} {A2A_INS_BASE+2} (by native_decide),")
    w(f"      pm_prefix_eq initPM {node} {A2A_INS_BASE+3} (by native_decide)]")
    w()
# pm_full FW_add outs
for r in range(4):
    node=ADD_NODES[r]; o=ADD_OUTS[r]; pin=ADD_PREREQ_INS[r]; ao=A2A_OUTS[r]
    w(f"theorem pm_full_{o} (initPM : Store) :")
    w(f"    denoteGraph pm initPM {o}")
    w(f"      = elemwiseAdd (denoteGraph pm initPM {pin})")
    w(f"          (allToAllPrimWithDims pm.numRanks {r}")
    w(f"            {ains} {IDIM} {ODIM}) := by")
    w(f"  rw [pm_val initPM {node} {o} (by native_decide) (by native_decide)]")
    w(f"  rw [show pm.nodes[{node}]'(by native_decide)")
    w(f'      = {{ rank := {r}, op := "OpName.FW_add", ins := [{pin}, {ao}], outs := [{o}] }}')
    w("      from by native_decide]")
    w("  rw [applyNode_fw_add2_out]")
    w(f"  rw [pm_prefix_eq initPM {node} {pin} (by native_decide),")
    w(f"      pm_prefix_eq initPM {node} {ao} (by native_decide)]")
    w(f"  rw [pm_full_{ao}]")
    w()
# denote_pm_goal_54 mini FW_add outs
asin="[s {0}, s {1}, s {2}, s {3}]".format(A2A_INS_BASE,A2A_INS_BASE+1,A2A_INS_BASE+2,A2A_INS_BASE+3)
for r in range(4):
    o=ADD_OUTS[r]; pin=ADD_PREREQ_INS[r]
    w(f"theorem denote_pm_goal_54_{o} (s : Store) :")
    w(f"    denoteGraph pm_goal_54 s {o}")
    w(f"      = elemwiseAdd (s {pin})")
    w(f"          (allToAllPrimWithDims 4 {r} {asin} {IDIM} {ODIM}) := by")
    w("  simp only [pm_goal_54, denoteGraph, List.foldl]")
    w("  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]")
    w("  rw [applyNode_fw_add2_out]")
    w("  congr 1")
    w("  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]")
    w()
# pm_frame self FW_add outs
for r in range(4):
    o=ADD_OUTS[r]
    w(f"theorem pm_frame_{o}_self (initPM : Store) :")
    w(f"    denoteGraph pm initPM {o} = denoteGraph pm_goal_54 (denoteGraph pm initPM) {o} := by")
    w(f"  rw [denote_pm_goal_54_{o}]")
    w("  rw [show (4 : Nat) = pm.numRanks from by native_decide]")
    w(f"  exact pm_full_{o} initPM")
    w()
# helper hInitCut
w("lemma goal_54_hInitCut_helper (Ssm Spm : Store)")
w("    (hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm)")
for g in PREREQS:
    w(f"    (hg{g} : InitGoalHolds pm.numRanks goal_{g} Ssm Spm)")
w("    : InitGoalsHold pm_goal_54.numRanks goal_54_cut_initGoals Ssm Spm := by")
w("  have hnr : pm_goal_54.numRanks = pm.numRanks := by native_decide")
w("  rw [hnr]; intro g hg")
w("  simp only [goal_54_cut_initGoals, goal_54_prereqs, List.mem_append] at hg")
w("  rcases hg with hg | hg")
w("  \u00b7 exact hinitC g hg")
w("  \u00b7 simp only [List.mem_cons, List.not_mem_nil, or_false] at hg")
w("    rcases hg with "+" | ".join(["rfl"]*len(PREREQS)))
for g in PREREQS:
    w(f"    \u00b7 exact hg{g}")
w()
# main
w("theorem goal_54_cut_to_full (h : goal_54_stmt_cut) : goal_54_stmt := by")
w("  intro initSM initPM hSM hPM hInit")
w("  set Ssm := denoteGraph sm initSM with hSsm")
w("  set Spm := denoteGraph pm initPM with hSpm")
for g in PREREQS:
    w(f"  have hg{g} := goal_{g}_intermediate initSM initPM hSM hPM hInit")
w("  have hinitC := initGoals_preserved initSM initPM hInit")
w("  have hnr : pm_goal_54.numRanks = pm.numRanks := by native_decide")
w("  have hInitCut : InitGoalsHold pm_goal_54.numRanks goal_54_cut_initGoals Ssm Spm :=")
w("    goal_54_hInitCut_helper Ssm Spm hinitC "+" ".join([f"hg{g}" for g in PREREQS]))
# shapes: 981 = goal_283 [1,8,32]; 636 = goal_53 [1,8,32]; 2193-2196 = goal_283 tps [1,2,32]; 2169-2172 = goal_53 tps [1,8,8]
w(f"  have h981_smsh : (Ssm 981).shape = [1, 8, 32] := by")
w(f"    have h := hg{GIN_981}.1; simp only [goal_{GIN_981}] at h; exact h")
w(f"  have h636_smsh : (Ssm 636).shape = [1, 8, 32] := by")
w(f"    have h := hg{GIN_636}.1; simp only [goal_{GIN_636}] at h; exact h")
w(f"  have h283tp := hg{GIN_981}.2.1")
w(f"  simp only [goal_{GIN_981}, List.map, List.cons.injEq, and_true] at h283tp")
w("  obtain \u27e8h2193sh, h2194sh, h2195sh, h2196sh\u27e9 := h283tp")
w(f"  have h53tp := hg{GIN_636}.2.1")
w(f"  simp only [goal_{GIN_636}, List.map, List.cons.injEq, and_true] at h53tp")
w("  obtain \u27e8h2169sh, h2170sh, h2171sh, h2172sh\u27e9 := h53tp")
# StoreShapesHold sm: order [(636),(981)]
w("  have hSM54 : StoreShapesHold Ssm sm_goal_54InitEnv := by")
w("    intro tid sh hsh")
w("    rw [sm_goal_54InitEnv] at hsh")
w("    have hmem := mem_of_shapeEnvOfList_eq_some hsh")
w("    simp only [sm_goal_54InitShapes, List.mem_cons, List.not_mem_nil, or_false,")
w("               Prod.mk.injEq] at hmem")
w("    rcases hmem with \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9")
w("    \u00b7 exact h636_smsh")
w("    \u00b7 exact h981_smsh")
# StoreShapesHold pm: order [2169,2170,2171,2172,2193,2194,2195,2196]
w("  have hPM54 : StoreShapesHold Spm pm_goal_54InitEnv := by")
w("    intro tid sh hsh")
w("    rw [pm_goal_54InitEnv] at hsh")
w("    have hmem := mem_of_shapeEnvOfList_eq_some hsh")
w("    simp only [pm_goal_54InitShapes, List.mem_cons, List.not_mem_nil, or_false,")
w("               Prod.mk.injEq] at hmem")
w("    rcases hmem with \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9 | \u27e8rfl, rfl\u27e9")
w("    \u00b7 exact h2169sh")
w("    \u00b7 exact h2170sh")
w("    \u00b7 exact h2171sh")
w("    \u00b7 exact h2172sh")
w("    \u00b7 exact h2193sh")
w("    \u00b7 exact h2194sh")
w("    \u00b7 exact h2195sh")
w("    \u00b7 exact h2196sh")
w("  have hcut := h Ssm Spm hSM54 hPM54 hInitCut")
w(f"  have hsmf : Ssm {SM_OUT} = denoteGraph sm_goal_54 Ssm {SM_OUT} := by")
w(f"    rw [hSsm]; exact sm_frame_{SM_OUT}_self initSM")
for o in ADD_OUTS:
    w(f"  have hpm{o} : Spm {o} = denoteGraph pm_goal_54 Spm {o} := by")
    w(f"    rw [hSpm]; exact pm_frame_{o}_self initPM")
w("  rw [hnr] at hcut")
w("  simp only [goal_54, List.map] at hcut \u22a2")
w("  rw [hsmf, "+", ".join([f"hpm{o}" for o in ADD_OUTS])+"]")
w("  exact hcut")
w()
w("theorem goal_54_intermediate (initSM initPM : Store)")
w("    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)")
w("    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :")
w("    InitGoalHolds pm.numRanks goal_54 (denoteGraph sm initSM) (denoteGraph pm initPM) := by")
w("  have hfull : goal_54_stmt := goal_54_cut_to_full prove_goal_54_cut")
w("  have := hfull initSM initPM hSM hPM hInit")
w("  simpa [InitGoalHolds, goal_54] using this")
w()
w("end TrainVerify.Denote.GeneratedGoals")

with open("trainverify/denote/gpt_ly4_regen/Goal54Bridge.lean","w") as f:
    f.write("\n".join(out)+"\n")
print("Generated Goal54Bridge.lean:", len(out), "lines, prereqs:", len(PREREQS))
