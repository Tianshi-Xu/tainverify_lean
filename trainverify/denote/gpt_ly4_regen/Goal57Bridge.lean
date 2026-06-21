/- goal_57 bridge (prereqs=[2..55,257-285 odd,291]=70). Column-parallel FW_linear
   (shared input 1000 + column-sharded weight) + AllGather dim2 -> single-tp 644.
   SM node 63 FW_linear(1008,643)->644 [1,8,32]. PM nodes 410-413 4xFW_linear(1000,2285+r)->2289-2292
   (shared input 1000, per-rank weight slice [8,32]) + node 416 AllGatherPrim(range 2289+r, params=[2] dim2)->644 single out.
   input 1008=1000 from goal_291 single-tp [1,8,32]; weights 643->2285-2288 [8,32] from initGoal_643 (in initGoals, column-sharded dim0).
   Each rank computes feature-column slice [1,8,8]; AllGather dim2 reconstructs [1,8,32] = full linear.
   Core column-parallel semantics (fw_linear_column_parallel_*) in prove_goal_57_cut. Bridge = frame only.
   Template = Goal56Bridge (sibling, 1st-out upstream multiref) verbatim clone:
   1004->1008 (goal_289->goal_291), 642->644, 641->643, 2257-2260->2285-2288, 999->1000,
   sm node 62->63, pm nodes 406-409->410-413, AllGather node 415->416 (still range-form ins, dim2). -/
import denote.gpt_ly4_regen.Goal291Bridge
import denote.gpt_ly4_regen.Goal_57

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

-- ========== mini sm_goal_57 computes 644 (FW_linear 1008,643) ==========
theorem denote_sm_goal_57_644 (s : Store) :
    denoteGraph sm_goal_57 s 644 = fw_linear (s 1008) (s 643) := by
  simp only [sm_goal_57, denoteGraph, List.foldl]
  rw [applyNode_fw_linear_out]

-- ========== mini pm_goal_57 computes 644 (AllGather dim2 of 4x FW_linear) ==========
theorem denote_pm_goal_57_644 (s : Store) :
    denoteGraph pm_goal_57 s 644
      = allGatherPrimDimN 2 4 0
          [fw_linear (s 1000) (s 2285),
           fw_linear (s 1000) (s 2286),
           fw_linear (s 1000) (s 2287),
           fw_linear (s 1000) (s 2288)] := by
  simp only [pm_goal_57, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full computes 644 (node 63 FW_linear) ==========
theorem sm_frame_644_self (initSM : Store) :
    denoteGraph sm initSM 644 = denoteGraph sm_goal_57 (denoteGraph sm initSM) 644 := by
  rw [denote_sm_goal_57_644]
  rw [sm_val initSM 63 644 (by native_decide) (by native_decide)]
  rw [show sm.nodes[63]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1008, 643], outs := [644] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [sm_prefix_eq initSM 63 1008 (by native_decide),
      sm_prefix_eq initSM 63 643 (by native_decide)]

-- ========== full pm computes per-rank FW_linear 2289-2292 (node 410-413) ==========
theorem pm_full_2289 (initPM : Store) :
    denoteGraph pm initPM 2289
      = fw_linear (denoteGraph pm initPM 1000) (denoteGraph pm initPM 2285) := by
  rw [pm_val initPM 410 2289 (by native_decide) (by native_decide)]
  rw [show pm.nodes[410]'(by native_decide)
      = { rank := 0, op := "OpName.FW_linear", ins := [1000, 2285], outs := [2289] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 410 1000 (by native_decide),
      pm_prefix_eq initPM 410 2285 (by native_decide)]

theorem pm_full_2290 (initPM : Store) :
    denoteGraph pm initPM 2290
      = fw_linear (denoteGraph pm initPM 1000) (denoteGraph pm initPM 2286) := by
  rw [pm_val initPM 411 2290 (by native_decide) (by native_decide)]
  rw [show pm.nodes[411]'(by native_decide)
      = { rank := 1, op := "OpName.FW_linear", ins := [1000, 2286], outs := [2290] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 411 1000 (by native_decide),
      pm_prefix_eq initPM 411 2286 (by native_decide)]

theorem pm_full_2291 (initPM : Store) :
    denoteGraph pm initPM 2291
      = fw_linear (denoteGraph pm initPM 1000) (denoteGraph pm initPM 2287) := by
  rw [pm_val initPM 412 2291 (by native_decide) (by native_decide)]
  rw [show pm.nodes[412]'(by native_decide)
      = { rank := 2, op := "OpName.FW_linear", ins := [1000, 2287], outs := [2291] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 412 1000 (by native_decide),
      pm_prefix_eq initPM 412 2287 (by native_decide)]

theorem pm_full_2292 (initPM : Store) :
    denoteGraph pm initPM 2292
      = fw_linear (denoteGraph pm initPM 1000) (denoteGraph pm initPM 2288) := by
  rw [pm_val initPM 413 2292 (by native_decide) (by native_decide)]
  rw [show pm.nodes[413]'(by native_decide)
      = { rank := 3, op := "OpName.FW_linear", ins := [1000, 2288], outs := [2292] }
      from by native_decide]
  rw [applyNode_fw_linear_out]
  rw [pm_prefix_eq initPM 413 1000 (by native_decide),
      pm_prefix_eq initPM 413 2288 (by native_decide)]

-- ========== PM self-frame: 644 (AllGather node 416, range-form ins, dim2) ==========
theorem pm_frame_644_self (initPM : Store) :
    denoteGraph pm initPM 644 = denoteGraph pm_goal_57 (denoteGraph pm initPM) 644 := by
  rw [denote_pm_goal_57_644]
  rw [pm_val initPM 416 644 (by native_decide) (by native_decide)]
  rw [show pm.nodes[416]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 2289 + r)), outs := [644], params := [2] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 416 2289 (by native_decide),
      pm_prefix_eq initPM 416 2290 (by native_decide),
      pm_prefix_eq initPM 416 2291 (by native_decide),
      pm_prefix_eq initPM 416 2292 (by native_decide)]
  rw [pm_full_2289, pm_full_2290, pm_full_2291, pm_full_2292]
  rw [show pm.numRanks = 4 from by native_decide]

lemma goal_57_hInitCut_helper (Ssm Spm : Store)
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
    (hg291 : InitGoalHolds pm.numRanks goal_291 Ssm Spm)
    : InitGoalsHold pm_goal_57.numRanks goal_57_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_57.numRanks = pm.numRanks := by native_decide
  rw [hnr]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_57_cut_initGoals, goal_57_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg50, hg51, hg52, hg53, hg54, hg55, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, hg281, hg283, hg285, hg291, List.forall_mem_nil _⟩

theorem goal_57_cut_to_full (h : goal_57_stmt_cut) : goal_57_stmt := by
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
  have hg291 := goal_291_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg55 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hg291 hinitC
  have hnr : pm_goal_57.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_57.numRanks goal_57_cut_initGoals Ssm Spm :=
    goal_57_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg55 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hg291
  -- input 1008 [1,8,32] (sm ts) from goal_291; 1000 [1,8,32] (pm tp) from goal_291
  have h1008_smsh : (Ssm 1008).shape = [1, 8, 32] := by
    have h := hg291.1; simp only [goal_291] at h; exact h
  have h1000_pmsh : (Spm 1000).shape = [1, 8, 32] := by
    have h := hg291.2.1; simp only [goal_291, List.map] at h
    have := congrArg List.head? h; simpa using this
  -- weight 643 [32,32] (sm) + 2285-2288 [8,32] (pm) from initGoal_643 (in initGoals)
  have hg643 := hinitC initGoal_643 (by simp only [initGoals]; decide)
  have h643_smsh : (Ssm 643).shape = [32, 32] := by
    have h := hg643.1; simp only [initGoal_643] at h; exact h
  have hpmW : (Spm 2285).shape = [8,32] ∧ (Spm 2286).shape = [8,32] ∧
              (Spm 2287).shape = [8,32] ∧ (Spm 2288).shape = [8,32] := by
    have h := hg643.2.1
    simp only [initGoal_643, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h2285sh, h2286sh, h2287sh, h2288sh⟩ := hpmW
  have hSM57 : StoreShapesHold Ssm sm_goal_57InitEnv := by
    intro tid sh hsh
    rw [sm_goal_57InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_57InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h643_smsh
    · exact h1008_smsh
  have hPM57 : StoreShapesHold Spm pm_goal_57InitEnv := by
    intro tid sh hsh
    rw [pm_goal_57InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_57InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1000_pmsh
    · exact h2285sh
    · exact h2286sh
    · exact h2287sh
    · exact h2288sh
  have hcut := h Ssm Spm hSM57 hPM57 hInitCut
  have hsmf : Ssm 644 = denoteGraph sm_goal_57 Ssm 644 := by
    rw [hSsm]; exact sm_frame_644_self initSM
  have hpm644 : Spm 644 = denoteGraph pm_goal_57 Spm 644 := by
    rw [hSpm]; exact pm_frame_644_self initPM
  rw [hnr] at hcut
  simp only [goal_57, List.map] at hcut ⊢
  rw [hsmf, hpm644]
  exact hcut

theorem goal_57_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_57 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_57_stmt := goal_57_cut_to_full prove_goal_57_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
