/- goal_19 桥 (prereqs=[2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,257,261,263,265])。
   第14种结构: 两输入 FW_matmul, 一个 replicated 输入 (586, goal_18) + 一个 dim3-sharded 输入 (582/1309-1312, goal_14),
   multi-tps 输出 (1413-1416, contraction over gathered dim3)。
   SM=FW_matmul(586,582)→587 (node 19)。
   PM=4×FW_matmul(586,1309-1312)→1413-1416 (node 123-126)。两输入都经 pm_prefix_eq 取全图值; 586 replicated。
   套 Goal16Bridge (两输入 matmul frame) + Goal15Bridge (multi-tps 总装) 模板。
   注: matmul-split 语义 (fw_matmul_split_dimN) 已在 cut 证明里处理; bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal14Bridge
import denote.gpt_ly4_regen.Goal16Bridge
import denote.gpt_ly4_regen.Goal17Bridge
import denote.gpt_ly4_regen.Goal18Bridge
import denote.gpt_ly4_regen.Goal_19

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_19 算 587 (FW_matmul) ==========
theorem denote_sm_goal_19_587 (s : Store) :
    denoteGraph sm_goal_19 s 587 = fw_matmul (s 586) (s 582) := by
  simp only [sm_goal_19, denoteGraph, List.foldl]
  rw [applyNode_fw_matmul_out]

-- ========== 迷你图 pm_goal_19 算 1413-1416 (4×FW_matmul) ==========
theorem denote_pm_goal_19_1413 (s : Store) :
    denoteGraph pm_goal_19 s 1413 = fw_matmul (s 586) (s 1309) := by
  simp only [pm_goal_19, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]

theorem denote_pm_goal_19_1414 (s : Store) :
    denoteGraph pm_goal_19 s 1414 = fw_matmul (s 586) (s 1310) := by
  simp only [pm_goal_19, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_19_1415 (s : Store) :
    denoteGraph pm_goal_19 s 1415 = fw_matmul (s 586) (s 1311) := by
  simp only [pm_goal_19, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_19_1416 (s : Store) :
    denoteGraph pm_goal_19 s 1416 = fw_matmul (s 586) (s 1312) := by
  simp only [pm_goal_19, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_matmul_out]
  congr 1 <;> repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 587 (node 19 FW_matmul) ==========
theorem sm_frame_587_self (initSM : Store) :
    denoteGraph sm initSM 587 = denoteGraph sm_goal_19 (denoteGraph sm initSM) 587 := by
  rw [denote_sm_goal_19_587]
  rw [sm_val initSM 19 587 (by native_decide) (by native_decide)]
  rw [show sm.nodes[19]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [586, 582], outs := [587] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [sm_prefix_eq initSM 19 586 (by native_decide),
      sm_prefix_eq initSM 19 582 (by native_decide)]

-- ========== PM self-frame: 1413-1416 (4×FW_matmul, node 123-126) ==========
theorem pm_frame_1413_self (initPM : Store) :
    denoteGraph pm initPM 1413
      = fw_matmul (denoteGraph pm initPM 586) (denoteGraph pm initPM 1309) := by
  rw [pm_val initPM 123 1413 (by native_decide) (by native_decide)]
  rw [show pm.nodes[123]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [586, 1309], outs := [1413] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 123 586 (by native_decide),
      pm_prefix_eq initPM 123 1309 (by native_decide)]

theorem pm_frame_1414_self (initPM : Store) :
    denoteGraph pm initPM 1414
      = fw_matmul (denoteGraph pm initPM 586) (denoteGraph pm initPM 1310) := by
  rw [pm_val initPM 124 1414 (by native_decide) (by native_decide)]
  rw [show pm.nodes[124]'(by native_decide)
      = { rank := 1, op := "OpName.FW_matmul", ins := [586, 1310], outs := [1414] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 124 586 (by native_decide),
      pm_prefix_eq initPM 124 1310 (by native_decide)]

theorem pm_frame_1415_self (initPM : Store) :
    denoteGraph pm initPM 1415
      = fw_matmul (denoteGraph pm initPM 586) (denoteGraph pm initPM 1311) := by
  rw [pm_val initPM 125 1415 (by native_decide) (by native_decide)]
  rw [show pm.nodes[125]'(by native_decide)
      = { rank := 2, op := "OpName.FW_matmul", ins := [586, 1311], outs := [1415] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 125 586 (by native_decide),
      pm_prefix_eq initPM 125 1311 (by native_decide)]

theorem pm_frame_1416_self (initPM : Store) :
    denoteGraph pm initPM 1416
      = fw_matmul (denoteGraph pm initPM 586) (denoteGraph pm initPM 1312) := by
  rw [pm_val initPM 126 1416 (by native_decide) (by native_decide)]
  rw [show pm.nodes[126]'(by native_decide)
      = { rank := 3, op := "OpName.FW_matmul", ins := [586, 1312], outs := [1416] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 126 586 (by native_decide),
      pm_prefix_eq initPM 126 1312 (by native_decide)]

-- ========== 总装 ==========
theorem goal_19_cut_to_full (h : goal_19_stmt_cut) : goal_19_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg257 hg261 hg263 hg265 hinitC
  have hnr : pm_goal_19.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 586=goal_18.ts [1,4,8,8] (replicated, PM 586=SM 586);
  --            582=goal_14.ts [1,4,8,8]; 1309-1312=goal_14.tps [1,4,8,2]
  have h586_smsh : (Ssm 586).shape = [1, 4, 8, 8] := by
    have h := hg18.1; simp only [goal_18] at h; exact h
  have h586_repl : Ssm 586 = Spm 586 := by
    have hrec := hg18.2.2
    simp only [goal_18, List.map] at hrec
    first | rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at hrec | skip
    rw [reconstructWithDim_singleton] at hrec
    exact hrec
  have h586_pmsh : (Spm 586).shape = [1, 4, 8, 8] := by rw [← h586_repl]; exact h586_smsh
  have h582_smsh : (Ssm 582).shape = [1, 4, 8, 8] := by
    have h := hg14.1; simp only [goal_14] at h; exact h
  have h1309_pmsh : (Spm 1309).shape = [1, 4, 8, 2] := by
    have h := hg14.2.1; simp only [goal_14, List.map, List.cons.injEq, and_true] at h; exact h.1
  have h1310_pmsh : (Spm 1310).shape = [1, 4, 8, 2] := by
    have h := hg14.2.1; simp only [goal_14, List.map, List.cons.injEq, and_true] at h; exact h.2.1
  have h1311_pmsh : (Spm 1311).shape = [1, 4, 8, 2] := by
    have h := hg14.2.1; simp only [goal_14, List.map, List.cons.injEq, and_true] at h; exact h.2.2.1
  have h1312_pmsh : (Spm 1312).shape = [1, 4, 8, 2] := by
    have h := hg14.2.1; simp only [goal_14, List.map, List.cons.injEq, and_true] at h; exact h.2.2.2
  have hSM19 : StoreShapesHold Ssm sm_goal_19InitEnv := by
    intro tid sh hsh
    rw [sm_goal_19InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_19InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h582_smsh
    · exact h586_smsh
  have hPM19 : StoreShapesHold Spm pm_goal_19InitEnv := by
    intro tid sh hsh
    rw [pm_goal_19InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_19InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h586_pmsh
    · exact h1309_pmsh
    · exact h1310_pmsh
    · exact h1311_pmsh
    · exact h1312_pmsh
  have hInitCut : InitGoalsHold pm_goal_19.numRanks goal_19_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_19_cut_initGoals, goal_19_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg257, hg261, hg263, hg265, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM19 hPM19 hInitCut
  -- Frame: 587 (sm), 1413-1416 (pm)
  have hsmf : Ssm 587 = denoteGraph sm_goal_19 Ssm 587 := by
    rw [hSsm]; exact sm_frame_587_self initSM
  have hpm1413 : Spm 1413 = denoteGraph pm_goal_19 Spm 1413 := by
    rw [denote_pm_goal_19_1413]; rw [hSpm]; exact pm_frame_1413_self initPM
  have hpm1414 : Spm 1414 = denoteGraph pm_goal_19 Spm 1414 := by
    rw [denote_pm_goal_19_1414]; rw [hSpm]; exact pm_frame_1414_self initPM
  have hpm1415 : Spm 1415 = denoteGraph pm_goal_19 Spm 1415 := by
    rw [denote_pm_goal_19_1415]; rw [hSpm]; exact pm_frame_1415_self initPM
  have hpm1416 : Spm 1416 = denoteGraph pm_goal_19 Spm 1416 := by
    rw [denote_pm_goal_19_1416]; rw [hSpm]; exact pm_frame_1416_self initPM
  rw [hnr] at hcut
  simp only [goal_19, List.map] at hcut ⊢
  rw [hsmf, hpm1413, hpm1414, hpm1415, hpm1416]
  exact hcut

theorem goal_19_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_19 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_19_stmt := goal_19_cut_to_full prove_goal_19_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
