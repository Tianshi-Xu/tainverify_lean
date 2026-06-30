/- goal_55 bridge (prereqs=[2..54,257-285 odd]=68). per-rank FW_layernorm (data+replicated
   weight/bias), multi-tps gatherDim=1, no follow-on collective.
   SM=FW_layernorm(989,638,639)->640 node 60 [1,8,32].
   PM=4xFW_layernorm(2225+r,638,639)->2229-2232 node 392-395, each rank data [1,2,32], w/b replicated [32].
   989=goal_285 output [1,8,32] dim1-sharded tps 2225-2228 [1,2,32]; 638/639=initGoal_638/639 replicated [32].
   multi-tps output gatherDim=1; PM mini-graph no collective (input pre-sharded).
   Core semantics (per-rank layernorm + concat = full layernorm) in prove_goal_55_cut. Bridge = frame.
   Template = Goal30Bridge verbatim (same per-rank layernorm no-collective), remap tid/node/shape;
   data upstream goal_271 -> goal_285, weight 603/604 -> 638/639. -/
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal285Bridge
import denote.gpt_ly4_regen.Goal_55

set_option maxRecDepth 100000
set_option maxHeartbeats 0
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

theorem denote_sm_goal_55_640 (s : Store) :
    denoteGraph sm_goal_55 s 640 = fw_layernorm (s 989) (s 638) (s 639) := by
  simp only [sm_goal_55, denoteGraph, List.foldl]
  rw [applyNode_fw_layernorm_out]

theorem denote_pm_goal_55_2229 (s : Store) :
    denoteGraph pm_goal_55 s 2229 = fw_layernorm (s 2225) (s 638) (s 639) := by
  simp only [pm_goal_55, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]

theorem denote_pm_goal_55_2230 (s : Store) :
    denoteGraph pm_goal_55 s 2230 = fw_layernorm (s 2226) (s 638) (s 639) := by
  simp only [pm_goal_55, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_55_2231 (s : Store) :
    denoteGraph pm_goal_55 s 2231 = fw_layernorm (s 2227) (s 638) (s 639) := by
  simp only [pm_goal_55, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_55_2232 (s : Store) :
    denoteGraph pm_goal_55 s 2232 = fw_layernorm (s 2228) (s 638) (s 639) := by
  simp only [pm_goal_55, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_layernorm_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem sm_frame_640_self (initSM : Store) :
    denoteGraph sm initSM 640 = denoteGraph sm_goal_55 (denoteGraph sm initSM) 640 := by
  rw [denote_sm_goal_55_640]
  rw [sm_val initSM 60 640 (by native_decide) (by native_decide)]
  rw [show sm.nodes[60]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [989, 638, 639], outs := [640] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [sm_prefix_eq initSM 60 989 (by native_decide),
      sm_prefix_eq initSM 60 638 (by native_decide),
      sm_prefix_eq initSM 60 639 (by native_decide)]

theorem pm_frame_2229_self (initPM : Store) :
    denoteGraph pm initPM 2229
      = fw_layernorm (denoteGraph pm initPM 2225)
          (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  rw [pm_val initPM 392 2229 (by native_decide) (by native_decide)]
  rw [show pm.nodes[392]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [2225, 638, 639], outs := [2229] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 392 2225 (by native_decide),
      pm_prefix_eq initPM 392 638 (by native_decide),
      pm_prefix_eq initPM 392 639 (by native_decide)]

theorem pm_frame_2230_self (initPM : Store) :
    denoteGraph pm initPM 2230
      = fw_layernorm (denoteGraph pm initPM 2226)
          (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  rw [pm_val initPM 393 2230 (by native_decide) (by native_decide)]
  rw [show pm.nodes[393]'(by native_decide)
      = { rank := 1, op := "OpName.FW_layernorm", ins := [2226, 638, 639], outs := [2230] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 393 2226 (by native_decide),
      pm_prefix_eq initPM 393 638 (by native_decide),
      pm_prefix_eq initPM 393 639 (by native_decide)]

theorem pm_frame_2231_self (initPM : Store) :
    denoteGraph pm initPM 2231
      = fw_layernorm (denoteGraph pm initPM 2227)
          (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  rw [pm_val initPM 394 2231 (by native_decide) (by native_decide)]
  rw [show pm.nodes[394]'(by native_decide)
      = { rank := 2, op := "OpName.FW_layernorm", ins := [2227, 638, 639], outs := [2231] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 394 2227 (by native_decide),
      pm_prefix_eq initPM 394 638 (by native_decide),
      pm_prefix_eq initPM 394 639 (by native_decide)]

theorem pm_frame_2232_self (initPM : Store) :
    denoteGraph pm initPM 2232
      = fw_layernorm (denoteGraph pm initPM 2228)
          (denoteGraph pm initPM 638) (denoteGraph pm initPM 639) := by
  rw [pm_val initPM 395 2232 (by native_decide) (by native_decide)]
  rw [show pm.nodes[395]'(by native_decide)
      = { rank := 3, op := "OpName.FW_layernorm", ins := [2228, 638, 639], outs := [2232] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 395 2228 (by native_decide),
      pm_prefix_eq initPM 395 638 (by native_decide),
      pm_prefix_eq initPM 395 639 (by native_decide)]

lemma goal_55_hInitCut_helper (Ssm Spm : Store)
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
    : InitGoalsHold pm_goal_55.numRanks goal_55_cut_initGoals Ssm Spm := by
  have hnr : pm_goal_55.numRanks = pm.numRanks := by native_decide
  rw [hnr]
  simp only [InitGoalsHold] at hinitC ⊢
  simp only [goal_55_cut_initGoals, goal_55_prereqs, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg44, hg45, hg46, hg47, hg48, hg49, hg50, hg51, hg52, hg53, hg54, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg273, hg275, hg277, hg279, hg281, hg283, hg285, List.forall_mem_nil _⟩

theorem goal_55_cut_to_full (h : goal_55_stmt_cut) : goal_55_stmt := by
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
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285 hinitC
  have hnr : pm_goal_55.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_55.numRanks goal_55_cut_initGoals Ssm Spm :=
    goal_55_hInitCut_helper Ssm Spm hinitC hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg44 hg45 hg46 hg47 hg48 hg49 hg50 hg51 hg52 hg53 hg54 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg273 hg275 hg277 hg279 hg281 hg283 hg285
  have h989_smsh : (Ssm 989).shape = [1, 8, 32] := by
    have h := hg285.1; simp only [goal_285] at h; exact h
  have h285tp := hg285.2.1
  simp only [goal_285, List.map, List.cons.injEq, and_true] at h285tp
  obtain ⟨h2225sh, h2226sh, h2227sh, h2228sh⟩ := h285tp
  have hg638 := hinitC initGoal_638 (by simp only [initGoals]; decide)
  have hg639 := hinitC initGoal_639 (by simp only [initGoals]; decide)
  have h638_smsh : (Ssm 638).shape = [32] := by
    have h := hg638.1; simp only [initGoal_638] at h; exact h
  have h639_smsh : (Ssm 639).shape = [32] := by
    have h := hg639.1; simp only [initGoal_639] at h; exact h
  have h638_pmsh : (Spm 638).shape = [32] := by
    have h := hg638.2.1; simp only [initGoal_638, List.map] at h
    have := congrArg List.head? h; simpa using this
  have h639_pmsh : (Spm 639).shape = [32] := by
    have h := hg639.2.1; simp only [initGoal_639, List.map] at h
    have := congrArg List.head? h; simpa using this
  have hSM55 : StoreShapesHold Ssm sm_goal_55InitEnv := by
    intro tid sh hsh
    rw [sm_goal_55InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_55InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h638_smsh
    · exact h639_smsh
    · exact h989_smsh
  have hPM55 : StoreShapesHold Spm pm_goal_55InitEnv := by
    intro tid sh hsh
    rw [pm_goal_55InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_55InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h638_pmsh
    · exact h639_pmsh
    · exact h2225sh
    · exact h2226sh
    · exact h2227sh
    · exact h2228sh
  have hcut := h Ssm Spm hSM55 hPM55 hInitCut
  have hsmf : Ssm 640 = denoteGraph sm_goal_55 Ssm 640 := by
    rw [hSsm]; exact sm_frame_640_self initSM
  have hpm2229 : Spm 2229 = denoteGraph pm_goal_55 Spm 2229 := by
    rw [denote_pm_goal_55_2229]; rw [hSpm]; exact pm_frame_2229_self initPM
  have hpm2230 : Spm 2230 = denoteGraph pm_goal_55 Spm 2230 := by
    rw [denote_pm_goal_55_2230]; rw [hSpm]; exact pm_frame_2230_self initPM
  have hpm2231 : Spm 2231 = denoteGraph pm_goal_55 Spm 2231 := by
    rw [denote_pm_goal_55_2231]; rw [hSpm]; exact pm_frame_2231_self initPM
  have hpm2232 : Spm 2232 = denoteGraph pm_goal_55 Spm 2232 := by
    rw [denote_pm_goal_55_2232]; rw [hSpm]; exact pm_frame_2232_self initPM
  rw [hnr] at hcut
  simp only [goal_55, List.map] at hcut ⊢
  rw [hsmf, hpm2229, hpm2230, hpm2231, hpm2232]
  exact hcut

theorem goal_55_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_55 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_55_stmt := goal_55_cut_to_full prove_goal_55_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
