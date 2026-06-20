/- goal_58 bridge (prereqs=[2..55,257-285 odd,293]=70). Row-parallel FW_linear
   (per-rank input 2313-2316 + replicated weight 645) + AllGather dim1 -> single-tp 646.
   SM node 64 FW_linear(1012,645)->646 [1,8,32]. PM nodes 400-402,405 4xFW_linear(2313+r,645)->2317-2320
   (per-rank input, shared weight [32,32]) + node 414 AllGatherPrim(range 2317+r, params=[1] dim1)->646 single out.
   input 1012=2313-2316 from goal_293 dim1-gathered [1,8,32]; weight 645 replicated [32,32] from initGoal_645.
   Each rank computes a row-slice [1,2,32]; AllGather dim1 reconstructs [1,8,32] = full linear.
   Core row-parallel semantics (fw_linear_distribute_allGatherPrimDimN_dim1_4_1_2_32) in prove_goal_58_cut. Bridge = frame only.
   Template = Goal56Bridge frame (per-rank op + final AllGather single-out, range-form full-pm ins)
   adapted from column-parallel (shared input, sharded weight) to row-parallel (sharded input, replicated weight). -/
import denote.gpt_ly4_regen.Goal293Bridge
import denote.gpt_ly4_regen.Goal_58

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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

-- ========== mini sm_goal_58 computes 646 (FW_linear 1012,645) ==========
theorem denote_sm_goal_58_646 (s : Store) :
    denoteGraph sm_goal_58 s 646 = fw_linear (s 1012) (s 645) := by
  simp only [sm_goal_58, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== mini pm_goal_58 computes 646 (AllGather dim1 of 4x FW_linear) ==========
theorem denote_pm_goal_58_646 (s : Store) :
    denoteGraph pm_goal_58 s 646
      = allGatherPrimDimN 1 4 0
          [fw_linear (s 2313) (s 645),
           fw_linear (s 2314) (s 645),
           fw_linear (s 2315) (s 645),
           fw_linear (s 2316) (s 645)] := by
  simp only [pm_goal_58, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full computes 646 (node 64 FW_linear) ==========
theorem sm_frame_646_self (initSM : Store) :
    denoteGraph sm initSM 646 = denoteGraph sm_goal_58 (denoteGraph sm initSM) 646 := by
  rw [denote_sm_goal_58_646]
  rw [sm_val initSM 64 646 (by native_decide) (by native_decide)]
  rw [show sm.nodes[64]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1012, 645], outs := [646] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 64 1012 (by native_decide),
      sm_prefix_eq initSM 64 645 (by native_decide)]

-- ========== full pm computes per-rank FW_linear 2317-2320 (nodes 400,401,402,405) ==========
theorem pm_full_2317 (initPM : Store) :
    denoteGraph pm initPM 2317
      = fw_linear (denoteGraph pm initPM 2313) (denoteGraph pm initPM 645) := by
  rw [pm_val initPM 400 2317 (by native_decide) (by native_decide)]
  rw [show pm.nodes[400]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [2313, 645], outs := [2317] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 400 2313 (by native_decide),
      pm_prefix_eq initPM 400 645 (by native_decide)]

theorem pm_full_2318 (initPM : Store) :
    denoteGraph pm initPM 2318
      = fw_linear (denoteGraph pm initPM 2314) (denoteGraph pm initPM 645) := by
  rw [pm_val initPM 401 2318 (by native_decide) (by native_decide)]
  rw [show pm.nodes[401]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [2314, 645], outs := [2318] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 401 2314 (by native_decide),
      pm_prefix_eq initPM 401 645 (by native_decide)]

theorem pm_full_2319 (initPM : Store) :
    denoteGraph pm initPM 2319
      = fw_linear (denoteGraph pm initPM 2315) (denoteGraph pm initPM 645) := by
  rw [pm_val initPM 402 2319 (by native_decide) (by native_decide)]
  rw [show pm.nodes[402]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [2315, 645], outs := [2319] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 402 2315 (by native_decide),
      pm_prefix_eq initPM 402 645 (by native_decide)]

theorem pm_full_2320 (initPM : Store) :
    denoteGraph pm initPM 2320
      = fw_linear (denoteGraph pm initPM 2316) (denoteGraph pm initPM 645) := by
  rw [pm_val initPM 405 2320 (by native_decide) (by native_decide)]
  rw [show pm.nodes[405]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [2316, 645], outs := [2320] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 405 2316 (by native_decide),
      pm_prefix_eq initPM 405 645 (by native_decide)]

-- ========== PM self-frame: 646 (AllGather node 414, range-form ins, dim1) ==========
theorem pm_frame_646_self (initPM : Store) :
    denoteGraph pm initPM 646 = denoteGraph pm_goal_58 (denoteGraph pm initPM) 646 := by
  rw [denote_pm_goal_58_646]
  rw [pm_val initPM 414 646 (by native_decide) (by native_decide)]
  rw [show pm.nodes[414]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 2317 + r)), outs := [646], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 414 2317 (by native_decide),
      pm_prefix_eq initPM 414 2318 (by native_decide),
      pm_prefix_eq initPM 414 2319 (by native_decide),
      pm_prefix_eq initPM 414 2320 (by native_decide)]
  rw [pm_full_2317, pm_full_2318, pm_full_2319, pm_full_2320]
  rw [show pm.numRanks = 4 from by native_decide]

lemma goal_58_hInitCut_helper (Ssm Spm : Store)
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
    (hg54 : InitGoalHolds pm.numRanks goal_54 Ssm Spm)
    (hg55 : InitGoalHolds pm.numRanks goal_55 Ssm Spm)
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
    (hg285 : InitGoalHolds pm.numRanks goal_285 Ssm Spm)
    (hg293 : InitGoalHolds pm.numRanks goal_293 Ssm Spm)
    : InitGoalsHold pm_goal_58.numRanks goal_58_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_58.numRanks = pm.numRanks := by native_decide
  rw [hnr]; intro g hg
  simp only [goal_58_cut_initGoals, goal_58_prereqs, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hinitC g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg2
    · exact hg3
    · exact hg4
    · exact hg5
    · exact hg6
    · exact hg7
    · exact hg8
    · exact hg9
    · exact hg10
    · exact hg11
    · exact hg12
    · exact hg13
    · exact hg14
    · exact hg15
    · exact hg16
    · exact hg17
    · exact hg18
    · exact hg19
    · exact hg20
    · exact hg21
    · exact hg22
    · exact hg23
    · exact hg24
    · exact hg25
    · exact hg26
    · exact hg27
    · exact hg28
    · exact hg29
    · exact hg30
    · exact hg31
    · exact hg32
    · exact hg33
    · exact hg34
    · exact hg35
    · exact hg36
    · exact hg37
    · exact hg38
    · exact hg39
    · exact hg40
    · exact hg41
    · exact hg42
    · exact hg43
    · exact hg44
    · exact hg45
    · exact hg46
    · exact hg47
    · exact hg48
    · exact hg49
    · exact hg50
    · exact hg51
    · exact hg52
    · exact hg53
    · exact hg54
    · exact hg55
    · exact hg257
    · exact hg259
    · exact hg261
    · exact hg263
    · exact hg265
    · exact hg267
    · exact hg269
    · exact hg271
    · exact hg273
    · exact hg275
    · exact hg277
    · exact hg279
    · exact hg281
    · exact hg283
    · exact hg285
    · exact hg293

theorem goal_58_cut_to_full (h : goal_58_stmt_cut) : goal_58_stmt := by
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
  have hg54 := goal_54_intermediate initSM initPM hSM hPM hInit
  have hg55 := goal_55_intermediate initSM initPM hSM hPM hInit
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
  have hg285 := goal_285_intermediate initSM initPM hSM hPM hInit
  have hg293 := goal_293_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg55 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hg293 hinitC
  have hnr : pm_goal_58.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_58.numRanks goal_58_cut_initGoals Ssm Spm :=
    goal_58_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg55 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hg293
  -- input 1012 [1,8,32] (sm ts) from goal_293; 2313-2316 [1,2,32] (pm tps) from goal_293
  have h1012_smsh : (Ssm 1012).shape = [1, 8, 32] := by
    have h := hg293.1; simp only [goal_293] at h; exact h
  have htpXsh := hg293.2.1
  simp only [goal_293, List.map] at htpXsh
  have h2313sh : (Spm 2313).shape = [1, 2, 32] := by
    have := congrArg List.head? htpXsh; simpa using this
  have h2314sh : (Spm 2314).shape = [1, 2, 32] := by
    have := congrArg List.tail htpXsh
    have := congrArg List.head? this; simpa using this
  have h2315sh : (Spm 2315).shape = [1, 2, 32] := by
    have := congrArg (List.tail ∘ List.tail) htpXsh
    have := congrArg List.head? this; simpa using this
  have h2316sh : (Spm 2316).shape = [1, 2, 32] := by
    have := congrArg (List.tail ∘ List.tail ∘ List.tail) htpXsh
    have := congrArg List.head? this; simpa using this
  -- weight 645 [32,32] replicated: SM 645 [32,32] + PM 645 [32,32] from initGoal_645
  have hg645 := hinitC initGoal_645 (by simp only [initGoals]; decide)
  have h645_smsh : (Ssm 645).shape = [32, 32] := by
    have h := hg645.1; simp only [initGoal_645] at h; exact h
  have h645_pmsh : (Spm 645).shape = [32, 32] := by
    have h := hg645.2.1
    simp only [initGoal_645, List.map, List.cons.injEq, and_true] at h
    exact h
  have hSM58 : StoreShapesHold Ssm sm_goal_58InitEnv := by
    intro tid sh hsh
    rw [sm_goal_58InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_58InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h645_smsh
    · exact h1012_smsh
  have hPM58 : StoreShapesHold Spm pm_goal_58InitEnv := by
    intro tid sh hsh
    rw [pm_goal_58InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_58InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h645_pmsh
    · exact h2313sh
    · exact h2314sh
    · exact h2315sh
    · exact h2316sh
  have hcut := h Ssm Spm hSM58 hPM58 hInitCut
  have hsmf : Ssm 646 = denoteGraph sm_goal_58 Ssm 646 := by
    rw [hSsm]; exact sm_frame_646_self initSM
  have hpm646 : Spm 646 = denoteGraph pm_goal_58 Spm 646 := by
    rw [hSpm]; exact pm_frame_646_self initPM
  rw [hnr] at hcut
  simp only [goal_58, List.map] at hcut ⊢
  rw [hsmf, hpm646]
  exact hcut

theorem goal_58_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_58 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_58_stmt := goal_58_cut_to_full prove_goal_58_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
