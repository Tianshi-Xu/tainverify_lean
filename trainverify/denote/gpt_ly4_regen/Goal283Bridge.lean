/- goal_283 bridge (prereqs=[2..49,257-279 odd]=60, same as goal_281). Reuse Goal281Bridge
   FW_multiref params=[2] + AllToAll template, but take SECOND output 981.
   SM=FW_multiref(628)->[977,981] node 53, second out 981=628 (applyNode_fw_multiref2_second_out_g283, needs hne).
   PM=4xFW_multiref node 346-349 second outs 3559/3567/3575/3583=2057-2060,
      4xAllToAllPrim(ins=[3559,3567,3575,3583],idim=2 odim=1)->2193-2196 node 351/353/355/357.
   628=goal_49 [1,8,32] dim2-sharded tps 2057-2060 [1,8,8]. Bridge = frame only. -/
import denote.gpt_ly4_regen.Goal49Bridge
import denote.gpt_ly4_regen.Goal273Bridge
import denote.gpt_ly4_regen.Goal275Bridge
import denote.gpt_ly4_regen.Goal277Bridge
import denote.gpt_ly4_regen.Goal279Bridge
import denote.gpt_ly4_regen.Goal_283

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem denote_sm_goal_283_981 (s : Store) :
    denoteGraph sm_goal_283 s 981 = s 628 := by
  simp only [sm_goal_283, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 628 977 981 (by decide)]

theorem sm_frame_981_self (initSM : Store) :
    denoteGraph sm initSM 981 = denoteGraph sm_goal_283 (denoteGraph sm initSM) 981 := by
  rw [denote_sm_goal_283_981]
  rw [sm_val initSM 53 981 (by native_decide) (by native_decide)]
  rw [show sm.nodes[53]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [628], outs := [977, 981], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 628 977 981 (by decide)]
  rw [sm_prefix_eq initSM 53 628 (by native_decide)]

theorem pm_full_g283_3559 (initPM : Store) :
    denoteGraph pm initPM 3559 = denoteGraph pm initPM 2057 := by
  rw [pm_val initPM 346 3559 (by native_decide) (by native_decide)]
  rw [show pm.nodes[346]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [2057], outs := [3557, 3559], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2057 3557 3559 (by decide)]
  rw [pm_prefix_eq initPM 346 2057 (by native_decide)]

theorem pm_full_g283_3567 (initPM : Store) :
    denoteGraph pm initPM 3567 = denoteGraph pm initPM 2058 := by
  rw [pm_val initPM 347 3567 (by native_decide) (by native_decide)]
  rw [show pm.nodes[347]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [2058], outs := [3565, 3567], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2058 3565 3567 (by decide)]
  rw [pm_prefix_eq initPM 347 2058 (by native_decide)]

theorem pm_full_g283_3575 (initPM : Store) :
    denoteGraph pm initPM 3575 = denoteGraph pm initPM 2059 := by
  rw [pm_val initPM 348 3575 (by native_decide) (by native_decide)]
  rw [show pm.nodes[348]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [2059], outs := [3573, 3575], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2059 3573 3575 (by decide)]
  rw [pm_prefix_eq initPM 348 2059 (by native_decide)]

theorem pm_full_g283_3583 (initPM : Store) :
    denoteGraph pm initPM 3583 = denoteGraph pm initPM 2060 := by
  rw [pm_val initPM 349 3583 (by native_decide) (by native_decide)]
  rw [show pm.nodes[349]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [2060], outs := [3581, 3583], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2060 3581 3583 (by decide)]
  rw [pm_prefix_eq initPM 349 2060 (by native_decide)]

theorem pm_full_g283_2193 (initPM : Store) :
    denoteGraph pm initPM 2193
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 3559, denoteGraph pm initPM 3567,
           denoteGraph pm initPM 3575, denoteGraph pm initPM 3583] 2 1 := by
  rw [pm_val initPM 351 2193 (by native_decide) (by native_decide)]
  rw [show pm.nodes[351]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := [3559, 3567, 3575, 3583], outs := [2193], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 351 3559 (by native_decide),
      pm_prefix_eq initPM 351 3567 (by native_decide),
      pm_prefix_eq initPM 351 3575 (by native_decide),
      pm_prefix_eq initPM 351 3583 (by native_decide)]

theorem pm_full_g283_2194 (initPM : Store) :
    denoteGraph pm initPM 2194
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 3559, denoteGraph pm initPM 3567,
           denoteGraph pm initPM 3575, denoteGraph pm initPM 3583] 2 1 := by
  rw [pm_val initPM 353 2194 (by native_decide) (by native_decide)]
  rw [show pm.nodes[353]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := [3559, 3567, 3575, 3583], outs := [2194], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 353 3559 (by native_decide),
      pm_prefix_eq initPM 353 3567 (by native_decide),
      pm_prefix_eq initPM 353 3575 (by native_decide),
      pm_prefix_eq initPM 353 3583 (by native_decide)]

theorem pm_full_g283_2195 (initPM : Store) :
    denoteGraph pm initPM 2195
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 3559, denoteGraph pm initPM 3567,
           denoteGraph pm initPM 3575, denoteGraph pm initPM 3583] 2 1 := by
  rw [pm_val initPM 355 2195 (by native_decide) (by native_decide)]
  rw [show pm.nodes[355]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := [3559, 3567, 3575, 3583], outs := [2195], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 355 3559 (by native_decide),
      pm_prefix_eq initPM 355 3567 (by native_decide),
      pm_prefix_eq initPM 355 3575 (by native_decide),
      pm_prefix_eq initPM 355 3583 (by native_decide)]

theorem pm_full_g283_2196 (initPM : Store) :
    denoteGraph pm initPM 2196
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 3559, denoteGraph pm initPM 3567,
           denoteGraph pm initPM 3575, denoteGraph pm initPM 3583] 2 1 := by
  rw [pm_val initPM 357 2196 (by native_decide) (by native_decide)]
  rw [show pm.nodes[357]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := [3559, 3567, 3575, 3583], outs := [2196], params := [2, 1] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  rw [pm_prefix_eq initPM 357 3559 (by native_decide),
      pm_prefix_eq initPM 357 3567 (by native_decide),
      pm_prefix_eq initPM 357 3575 (by native_decide),
      pm_prefix_eq initPM 357 3583 (by native_decide)]

theorem denote_pm_goal_283_2193 (s : Store) :
    denoteGraph pm_goal_283 s 2193
      = allToAllPrimWithDims 4 0 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_283, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2057 3557 3559 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2058 3565 3567 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2059 3573 3575 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2060 3581 3583 (by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_283_2194 (s : Store) :
    denoteGraph pm_goal_283 s 2194
      = allToAllPrimWithDims 4 1 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_283, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2057 3557 3559 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2058 3565 3567 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2059 3573 3575 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2060 3581 3583 (by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_283_2195 (s : Store) :
    denoteGraph pm_goal_283 s 2195
      = allToAllPrimWithDims 4 2 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_283, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2057 3557 3559 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2058 3565 3567 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2059 3573 3575 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2060 3581 3583 (by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_283_2196 (s : Store) :
    denoteGraph pm_goal_283 s 2196
      = allToAllPrimWithDims 4 3 [s 2057, s 2058, s 2059, s 2060] 2 1 := by
  simp only [pm_goal_283, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.map]
  repeat first
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2057 3557 3559 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2058 3565 3567 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2059 3573 3575 (by decide)]
    | rw [applyNode_fw_multiref2_second_out_g283 _ _ _ 2060 3581 3583 (by decide)]
    | rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem pm_frame_2193_self (initPM : Store) :
    denoteGraph pm initPM 2193 = denoteGraph pm_goal_283 (denoteGraph pm initPM) 2193 := by
  rw [denote_pm_goal_283_2193]
  rw [pm_full_g283_2193]
  rw [pm_full_g283_3559, pm_full_g283_3567, pm_full_g283_3575, pm_full_g283_3583]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2194_self (initPM : Store) :
    denoteGraph pm initPM 2194 = denoteGraph pm_goal_283 (denoteGraph pm initPM) 2194 := by
  rw [denote_pm_goal_283_2194]
  rw [pm_full_g283_2194]
  rw [pm_full_g283_3559, pm_full_g283_3567, pm_full_g283_3575, pm_full_g283_3583]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2195_self (initPM : Store) :
    denoteGraph pm initPM 2195 = denoteGraph pm_goal_283 (denoteGraph pm initPM) 2195 := by
  rw [denote_pm_goal_283_2195]
  rw [pm_full_g283_2195]
  rw [pm_full_g283_3559, pm_full_g283_3567, pm_full_g283_3575, pm_full_g283_3583]
  rw [show pm.numRanks = 4 from by native_decide]

theorem pm_frame_2196_self (initPM : Store) :
    denoteGraph pm initPM 2196 = denoteGraph pm_goal_283 (denoteGraph pm initPM) 2196 := by
  rw [denote_pm_goal_283_2196]
  rw [pm_full_g283_2196]
  rw [pm_full_g283_3559, pm_full_g283_3567, pm_full_g283_3575, pm_full_g283_3583]
  rw [show pm.numRanks = 4 from by native_decide]

lemma goal_283_hInitCut_helper (Ssm Spm : Store)
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
    : InitGoalsHold pm_goal_283.numRanks goal_283_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_283.numRanks = pm.numRanks := by native_decide
  rw [hnr]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_283_cut_initGoals, goal_283_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, List.forall_mem_nil _⟩

theorem goal_283_cut_to_full (h : goal_283_stmt_cut) : goal_283_stmt := by
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
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hinitC
  have hnr : pm_goal_283.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_283.numRanks goal_283_cut_initGoals Ssm Spm :=
    goal_283_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279
  have h628_smsh : (Ssm 628).shape = [1, 8, 32] := by
    have h := hg49.1; simp only [goal_49] at h; exact h
  have hpmsh49 : (Spm 2057).shape = [1,8,8] ∧ (Spm 2058).shape = [1,8,8] ∧
                 (Spm 2059).shape = [1,8,8] ∧ (Spm 2060).shape = [1,8,8] := by
    have h := hg49.2.1
    simp only [goal_49, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h2057sh, h2058sh, h2059sh, h2060sh⟩ := hpmsh49
  have hSM283 : StoreShapesHold Ssm sm_goal_283InitEnv := by
    intro tid sh hsh
    rw [sm_goal_283InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_283InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    · exact h628_smsh
  have hPM283 : StoreShapesHold Spm pm_goal_283InitEnv := by
    intro tid sh hsh
    rw [pm_goal_283InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_283InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2057sh
    · exact h2058sh
    · exact h2059sh
    · exact h2060sh
  have hcut := h Ssm Spm hSM283 hPM283 hInitCut
  have hsmf : Ssm 981 = denoteGraph sm_goal_283 Ssm 981 := by
    rw [hSsm]; exact sm_frame_981_self initSM
  have hpm2193 : Spm 2193 = denoteGraph pm_goal_283 Spm 2193 := by
    rw [hSpm]; exact pm_frame_2193_self initPM
  have hpm2194 : Spm 2194 = denoteGraph pm_goal_283 Spm 2194 := by
    rw [hSpm]; exact pm_frame_2194_self initPM
  have hpm2195 : Spm 2195 = denoteGraph pm_goal_283 Spm 2195 := by
    rw [hSpm]; exact pm_frame_2195_self initPM
  have hpm2196 : Spm 2196 = denoteGraph pm_goal_283 Spm 2196 := by
    rw [hSpm]; exact pm_frame_2196_self initPM
  rw [hnr] at hcut
  simp only [goal_283, List.map] at hcut ⊢
  rw [hsmf, hpm2193, hpm2194, hpm2195, hpm2196]
  exact hcut

theorem goal_283_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_283 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_283_stmt := goal_283_cut_to_full prove_goal_283_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
