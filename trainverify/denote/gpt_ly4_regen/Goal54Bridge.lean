/- goal_54 bridge (prereqs=[2..53,257-283 odd]=66). FW_add over AllToAll-reshard dim2->1,
   multi-tps gatherDim=1. SM=FW_add(981,636)->637 node 58 [1,8,32].
   PM=4xAllToAllPrim(2169-2172,idim=2 odim=1)->2197-2200 node 380-383 params=[2,1],
      4xFW_add(2193+r,2197+r)->2201-2204 node 384-387 dim1-sharded [1,2,32].
   636=goal_53 (FW_linear column-parallel gatherDim=2 tps 2169-2172 [1,8,8]).
   981=goal_283 (FW_multiref second-out gatherDim=1 tps 2193-2196 [1,2,32]).
   AllToAll reshards dim2-sharded 636 into dim1-chunks, each rank FW_add with 2193-2196.
   Core semantics in prove_goal_54_cut. Bridge = frame only. Template = Goal29Bridge
   (FW_add+AllToAll) with AllToAll dir dim1->2 (params=[1,2]) swapped to dim2->1 (params=[2,1]). -/
import denote.gpt_ly4_regen.Goal53Bridge
import denote.gpt_ly4_regen.Goal283Bridge
import denote.gpt_ly4_regen.Goal_54

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem denote_sm_goal_54_637 (s : Store) :
    denoteGraph sm_goal_54 s 637 = elemwiseAdd (s 981) (s 636) := by
  simp only [sm_goal_54, denoteGraph, List.foldl]
  rw [applyNode_fw_add2_out]

theorem sm_frame_637_self (initSM : Store) :
    denoteGraph sm initSM 637 = denoteGraph sm_goal_54 (denoteGraph sm initSM) 637 := by
  rw [denote_sm_goal_54_637]
  rw [sm_val initSM 58 637 (by native_decide) (by native_decide)]
  rw [show sm.nodes[58]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [981, 636], outs := [637] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [sm_prefix_eq initSM 58 981 (by native_decide),
      sm_prefix_eq initSM 58 636 (by native_decide)]

theorem pm_full_2197 (initPM : Store) :
    denoteGraph pm initPM 2197
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1 := by
  rw [pm_val initPM 380 2197 (by native_decide) (by native_decide)]
  rw [show pm.nodes[380]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2169 + r)), outs := [2197], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 380 2169 (by native_decide),
      pm_prefix_eq initPM 380 2170 (by native_decide),
      pm_prefix_eq initPM 380 2171 (by native_decide),
      pm_prefix_eq initPM 380 2172 (by native_decide)]

theorem pm_full_2198 (initPM : Store) :
    denoteGraph pm initPM 2198
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1 := by
  rw [pm_val initPM 381 2198 (by native_decide) (by native_decide)]
  rw [show pm.nodes[381]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2169 + r)), outs := [2198], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 381 2169 (by native_decide),
      pm_prefix_eq initPM 381 2170 (by native_decide),
      pm_prefix_eq initPM 381 2171 (by native_decide),
      pm_prefix_eq initPM 381 2172 (by native_decide)]

theorem pm_full_2199 (initPM : Store) :
    denoteGraph pm initPM 2199
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1 := by
  rw [pm_val initPM 382 2199 (by native_decide) (by native_decide)]
  rw [show pm.nodes[382]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2169 + r)), outs := [2199], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 382 2169 (by native_decide),
      pm_prefix_eq initPM 382 2170 (by native_decide),
      pm_prefix_eq initPM 382 2171 (by native_decide),
      pm_prefix_eq initPM 382 2172 (by native_decide)]

theorem pm_full_2200 (initPM : Store) :
    denoteGraph pm initPM 2200
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1 := by
  rw [pm_val initPM 383 2200 (by native_decide) (by native_decide)]
  rw [show pm.nodes[383]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 2169 + r)), outs := [2200], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 383 2169 (by native_decide),
      pm_prefix_eq initPM 383 2170 (by native_decide),
      pm_prefix_eq initPM 383 2171 (by native_decide),
      pm_prefix_eq initPM 383 2172 (by native_decide)]

theorem pm_full_2201 (initPM : Store) :
    denoteGraph pm initPM 2201
      = elemwiseAdd (denoteGraph pm initPM 2193)
          (allToAllPrimWithDims pm.numRanks 0
            [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1) := by
  rw [pm_val initPM 384 2201 (by native_decide) (by native_decide)]
  rw [show pm.nodes[384]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [2193, 2197], outs := [2201] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 384 2193 (by native_decide),
      pm_prefix_eq initPM 384 2197 (by native_decide)]
  rw [pm_full_2197]

theorem pm_full_2202 (initPM : Store) :
    denoteGraph pm initPM 2202
      = elemwiseAdd (denoteGraph pm initPM 2194)
          (allToAllPrimWithDims pm.numRanks 1
            [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1) := by
  rw [pm_val initPM 385 2202 (by native_decide) (by native_decide)]
  rw [show pm.nodes[385]'(by native_decide)
      = { rank := 1, op := "OpName.FW_add", ins := [2194, 2198], outs := [2202] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 385 2194 (by native_decide),
      pm_prefix_eq initPM 385 2198 (by native_decide)]
  rw [pm_full_2198]

theorem pm_full_2203 (initPM : Store) :
    denoteGraph pm initPM 2203
      = elemwiseAdd (denoteGraph pm initPM 2195)
          (allToAllPrimWithDims pm.numRanks 2
            [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1) := by
  rw [pm_val initPM 386 2203 (by native_decide) (by native_decide)]
  rw [show pm.nodes[386]'(by native_decide)
      = { rank := 2, op := "OpName.FW_add", ins := [2195, 2199], outs := [2203] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 386 2195 (by native_decide),
      pm_prefix_eq initPM 386 2199 (by native_decide)]
  rw [pm_full_2199]

theorem pm_full_2204 (initPM : Store) :
    denoteGraph pm initPM 2204
      = elemwiseAdd (denoteGraph pm initPM 2196)
          (allToAllPrimWithDims pm.numRanks 3
            [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
           denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] 2 1) := by
  rw [pm_val initPM 387 2204 (by native_decide) (by native_decide)]
  rw [show pm.nodes[387]'(by native_decide)
      = { rank := 3, op := "OpName.FW_add", ins := [2196, 2200], outs := [2204] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 387 2196 (by native_decide),
      pm_prefix_eq initPM 387 2200 (by native_decide)]
  rw [pm_full_2200]

theorem denote_pm_goal_54_2201 (s : Store) :
    denoteGraph pm_goal_54 s 2201
      = elemwiseAdd (s 2193)
          (allToAllPrimWithDims 4 0 [s 2169, s 2170, s 2171, s 2172] 2 1) := by
  simp only [pm_goal_54, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_54_2202 (s : Store) :
    denoteGraph pm_goal_54 s 2202
      = elemwiseAdd (s 2194)
          (allToAllPrimWithDims 4 1 [s 2169, s 2170, s 2171, s 2172] 2 1) := by
  simp only [pm_goal_54, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_54_2203 (s : Store) :
    denoteGraph pm_goal_54 s 2203
      = elemwiseAdd (s 2195)
          (allToAllPrimWithDims 4 2 [s 2169, s 2170, s 2171, s 2172] 2 1) := by
  simp only [pm_goal_54, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_54_2204 (s : Store) :
    denoteGraph pm_goal_54 s 2204
      = elemwiseAdd (s 2196)
          (allToAllPrimWithDims 4 3 [s 2169, s 2170, s 2171, s 2172] 2 1) := by
  simp only [pm_goal_54, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem pm_frame_2201_self (initPM : Store) :
    denoteGraph pm initPM 2201 = denoteGraph pm_goal_54 (denoteGraph pm initPM) 2201 := by
  rw [denote_pm_goal_54_2201]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_2201 initPM

theorem pm_frame_2202_self (initPM : Store) :
    denoteGraph pm initPM 2202 = denoteGraph pm_goal_54 (denoteGraph pm initPM) 2202 := by
  rw [denote_pm_goal_54_2202]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_2202 initPM

theorem pm_frame_2203_self (initPM : Store) :
    denoteGraph pm initPM 2203 = denoteGraph pm_goal_54 (denoteGraph pm initPM) 2203 := by
  rw [denote_pm_goal_54_2203]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_2203 initPM

theorem pm_frame_2204_self (initPM : Store) :
    denoteGraph pm initPM 2204 = denoteGraph pm_goal_54 (denoteGraph pm initPM) 2204 := by
  rw [denote_pm_goal_54_2204]
  rw [show (4 : Nat) = pm.numRanks from by native_decide]
  exact pm_full_2204 initPM

lemma goal_54_hInitCut_helper (Ssm Spm : Store)
    (hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm)
    (hg2 : InitGoalHolds pm.numRanks goal_2 Ssm Spm)
    (hg3 : InitGoalHolds pm.numRanks goal_3 Ssm Spm)
    (hg4 : InitGoalHolds pm.numRanks goal_4 Ssm Spm)
    (hg5 : InitGoalHolds pm.numRanks goal_5 Ssm Spm)
    (hg6 : InitGoalHolds pm.numRanks goal_6 Ssm Spm)
    (hg7 : InitGoalHolds pm.numRanks goal_7 Ssm Spm)
    (hg8 : InitGoalHolds pm.numRanks goal_8 Ssm Spm)
    (hg9 : InitGoalHolds pm.numRanks goal_9 Ssm Spm)
    (hg10 : InitGoalHolds pm.numRanks goal_10 Ssm Spm)
    (hg11 : InitGoalHolds pm.numRanks goal_11 Ssm Spm)
    (hg12 : InitGoalHolds pm.numRanks goal_12 Ssm Spm)
    (hg13 : InitGoalHolds pm.numRanks goal_13 Ssm Spm)
    (hg14 : InitGoalHolds pm.numRanks goal_14 Ssm Spm)
    (hg15 : InitGoalHolds pm.numRanks goal_15 Ssm Spm)
    (hg16 : InitGoalHolds pm.numRanks goal_16 Ssm Spm)
    (hg17 : InitGoalHolds pm.numRanks goal_17 Ssm Spm)
    (hg18 : InitGoalHolds pm.numRanks goal_18 Ssm Spm)
    (hg19 : InitGoalHolds pm.numRanks goal_19 Ssm Spm)
    (hg20 : InitGoalHolds pm.numRanks goal_20 Ssm Spm)
    (hg21 : InitGoalHolds pm.numRanks goal_21 Ssm Spm)
    (hg22 : InitGoalHolds pm.numRanks goal_22 Ssm Spm)
    (hg23 : InitGoalHolds pm.numRanks goal_23 Ssm Spm)
    (hg24 : InitGoalHolds pm.numRanks goal_24 Ssm Spm)
    (hg25 : InitGoalHolds pm.numRanks goal_25 Ssm Spm)
    (hg26 : InitGoalHolds pm.numRanks goal_26 Ssm Spm)
    (hg27 : InitGoalHolds pm.numRanks goal_27 Ssm Spm)
    (hg28 : InitGoalHolds pm.numRanks goal_28 Ssm Spm)
    (hg29 : InitGoalHolds pm.numRanks goal_29 Ssm Spm)
    (hg30 : InitGoalHolds pm.numRanks goal_30 Ssm Spm)
    (hg31 : InitGoalHolds pm.numRanks goal_31 Ssm Spm)
    (hg32 : InitGoalHolds pm.numRanks goal_32 Ssm Spm)
    (hg33 : InitGoalHolds pm.numRanks goal_33 Ssm Spm)
    (hg34 : InitGoalHolds pm.numRanks goal_34 Ssm Spm)
    (hg35 : InitGoalHolds pm.numRanks goal_35 Ssm Spm)
    (hg36 : InitGoalHolds pm.numRanks goal_36 Ssm Spm)
    (hg37 : InitGoalHolds pm.numRanks goal_37 Ssm Spm)
    (hg38 : InitGoalHolds pm.numRanks goal_38 Ssm Spm)
    (hg39 : InitGoalHolds pm.numRanks goal_39 Ssm Spm)
    (hg40 : InitGoalHolds pm.numRanks goal_40 Ssm Spm)
    (hg41 : InitGoalHolds pm.numRanks goal_41 Ssm Spm)
    (hg42 : InitGoalHolds pm.numRanks goal_42 Ssm Spm)
    (hg43 : InitGoalHolds pm.numRanks goal_43 Ssm Spm)
    (hg44 : InitGoalHolds pm.numRanks goal_44 Ssm Spm)
    (hg45 : InitGoalHolds pm.numRanks goal_45 Ssm Spm)
    (hg46 : InitGoalHolds pm.numRanks goal_46 Ssm Spm)
    (hg47 : InitGoalHolds pm.numRanks goal_47 Ssm Spm)
    (hg48 : InitGoalHolds pm.numRanks goal_48 Ssm Spm)
    (hg49 : InitGoalHolds pm.numRanks goal_49 Ssm Spm)
    (hg50 : InitGoalHolds pm.numRanks goal_50 Ssm Spm)
    (hg51 : InitGoalHolds pm.numRanks goal_51 Ssm Spm)
    (hg52 : InitGoalHolds pm.numRanks goal_52 Ssm Spm)
    (hg53 : InitGoalHolds pm.numRanks goal_53 Ssm Spm)
    (hg257 : InitGoalHolds pm.numRanks goal_257 Ssm Spm)
    (hg259 : InitGoalHolds pm.numRanks goal_259 Ssm Spm)
    (hg261 : InitGoalHolds pm.numRanks goal_261 Ssm Spm)
    (hg263 : InitGoalHolds pm.numRanks goal_263 Ssm Spm)
    (hg265 : InitGoalHolds pm.numRanks goal_265 Ssm Spm)
    (hg267 : InitGoalHolds pm.numRanks goal_267 Ssm Spm)
    (hg269 : InitGoalHolds pm.numRanks goal_269 Ssm Spm)
    (hg271 : InitGoalHolds pm.numRanks goal_271 Ssm Spm)
    (hg273 : InitGoalHolds pm.numRanks goal_273 Ssm Spm)
    (hg275 : InitGoalHolds pm.numRanks goal_275 Ssm Spm)
    (hg277 : InitGoalHolds pm.numRanks goal_277 Ssm Spm)
    (hg279 : InitGoalHolds pm.numRanks goal_279 Ssm Spm)
    (hg281 : InitGoalHolds pm.numRanks goal_281 Ssm Spm)
    (hg283 : InitGoalHolds pm.numRanks goal_283 Ssm Spm)
    : InitGoalsHold pm_goal_54.numRanks goal_54_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_54.numRanks = pm.numRanks := by native_decide
  rw [hnr]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_54_cut_initGoals, goal_54_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg50, hg51, hg52, hg53, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, hg281, hg283, List.forall_mem_nil _⟩

theorem goal_54_cut_to_full (h : goal_54_stmt_cut) : goal_54_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg6 := goal_6_intermediate initSM initPM hSM hPM hInit
  have hg7 := goal_7_intermediate initSM initPM hSM hPM hInit
  have hg8 := goal_8_intermediate initSM initPM hSM hPM hInit
  have hg9 := goal_9_intermediate initSM initPM hSM hPM hInit
  have hg10 := goal_10_intermediate initSM initPM hSM hPM hInit
  have hg11 := goal_11_intermediate initSM initPM hSM hPM hInit
  have hg12 := goal_12_intermediate initSM initPM hSM hPM hInit
  have hg13 := goal_13_intermediate initSM initPM hSM hPM hInit
  have hg14 := goal_14_intermediate initSM initPM hSM hPM hInit
  have hg15 := goal_15_intermediate initSM initPM hSM hPM hInit
  have hg16 := goal_16_intermediate initSM initPM hSM hPM hInit
  have hg17 := goal_17_intermediate initSM initPM hSM hPM hInit
  have hg18 := goal_18_intermediate initSM initPM hSM hPM hInit
  have hg19 := goal_19_intermediate initSM initPM hSM hPM hInit
  have hg20 := goal_20_intermediate initSM initPM hSM hPM hInit
  have hg21 := goal_21_intermediate initSM initPM hSM hPM hInit
  have hg22 := goal_22_intermediate initSM initPM hSM hPM hInit
  have hg23 := goal_23_intermediate initSM initPM hSM hPM hInit
  have hg24 := goal_24_intermediate initSM initPM hSM hPM hInit
  have hg25 := goal_25_intermediate initSM initPM hSM hPM hInit
  have hg26 := goal_26_intermediate initSM initPM hSM hPM hInit
  have hg27 := goal_27_intermediate initSM initPM hSM hPM hInit
  have hg28 := goal_28_intermediate initSM initPM hSM hPM hInit
  have hg29 := goal_29_intermediate initSM initPM hSM hPM hInit
  have hg30 := goal_30_intermediate initSM initPM hSM hPM hInit
  have hg31 := goal_31_intermediate initSM initPM hSM hPM hInit
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg33 := goal_33_intermediate initSM initPM hSM hPM hInit
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg38 := goal_38_intermediate initSM initPM hSM hPM hInit
  have hg39 := goal_39_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg41 := goal_41_intermediate initSM initPM hSM hPM hInit
  have hg42 := goal_42_intermediate initSM initPM hSM hPM hInit
  have hg43 := goal_43_intermediate initSM initPM hSM hPM hInit
  have hg44 := goal_44_intermediate initSM initPM hSM hPM hInit
  have hg45 := goal_45_intermediate initSM initPM hSM hPM hInit
  have hg46 := goal_46_intermediate initSM initPM hSM hPM hInit
  have hg47 := goal_47_intermediate initSM initPM hSM hPM hInit
  have hg48 := goal_48_intermediate initSM initPM hSM hPM hInit
  have hg49 := goal_49_intermediate initSM initPM hSM hPM hInit
  have hg50 := goal_50_intermediate initSM initPM hSM hPM hInit
  have hg51 := goal_51_intermediate initSM initPM hSM hPM hInit
  have hg52 := goal_52_intermediate initSM initPM hSM hPM hInit
  have hg53 := goal_53_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg273 := goal_273_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hg281 := goal_281_intermediate initSM initPM hSM hPM hInit
  have hg283 := goal_283_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hinitC
  have hnr : pm_goal_54.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_54.numRanks goal_54_cut_initGoals Ssm Spm :=
    goal_54_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283
  have h981_smsh : (Ssm 981).shape = [1, 8, 32] := by
    have h := hg283.1; simp only [goal_283] at h; exact h
  have h636_smsh : (Ssm 636).shape = [1, 8, 32] := by
    have h := hg53.1; simp only [goal_53] at h; exact h
  have h283tp := hg283.2.1
  simp only [goal_283, List.map, List.cons.injEq, and_true] at h283tp
  obtain ⟨h2193sh, h2194sh, h2195sh, h2196sh⟩ := h283tp
  have h53tp := hg53.2.1
  simp only [goal_53, List.map, List.cons.injEq, and_true] at h53tp
  obtain ⟨h2169sh, h2170sh, h2171sh, h2172sh⟩ := h53tp
  have hSM54 : StoreShapesHold Ssm sm_goal_54InitEnv := by
    intro tid sh hsh
    rw [sm_goal_54InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_54InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h636_smsh
    · exact h981_smsh
  have hPM54 : StoreShapesHold Spm pm_goal_54InitEnv := by
    intro tid sh hsh
    rw [pm_goal_54InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_54InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2169sh
    · exact h2170sh
    · exact h2171sh
    · exact h2172sh
    · exact h2193sh
    · exact h2194sh
    · exact h2195sh
    · exact h2196sh
  have hcut := h Ssm Spm hSM54 hPM54 hInitCut
  have hsmf : Ssm 637 = denoteGraph sm_goal_54 Ssm 637 := by
    rw [hSsm]; exact sm_frame_637_self initSM
  have hpm2201 : Spm 2201 = denoteGraph pm_goal_54 Spm 2201 := by
    rw [hSpm]; exact pm_frame_2201_self initPM
  have hpm2202 : Spm 2202 = denoteGraph pm_goal_54 Spm 2202 := by
    rw [hSpm]; exact pm_frame_2202_self initPM
  have hpm2203 : Spm 2203 = denoteGraph pm_goal_54 Spm 2203 := by
    rw [hSpm]; exact pm_frame_2203_self initPM
  have hpm2204 : Spm 2204 = denoteGraph pm_goal_54 Spm 2204 := by
    rw [hSpm]; exact pm_frame_2204_self initPM
  rw [hnr] at hcut
  simp only [goal_54, List.map] at hcut ⊢
  rw [hsmf, hpm2201, hpm2202, hpm2203, hpm2204]
  exact hcut

theorem goal_54_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_54 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_54_stmt := goal_54_cut_to_full prove_goal_54_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
