/- goal_17 桥 (prereqs=[2,3,4,5,6,7,9,10,11,12,15,16,257,261,263])。SM=FW_div(584,c=2)→585;
   PM=4×ChunkPrim(584,dim=1)→1365-1368, 然后 4×FW_div(1365..,c=2)→1369-1372. tps=4个, gatherDim=1.
   584=goal_16 输出 (singleton, shape [1,4,8,8])。第 12 种结构: ChunkPrim+FW_div, multi-tps,
   gather distributes over div (pointwise). 结构同 goal_10 (ChunkPrim+FW_transpose), 换算子. -/
import denote.gpt_ly4_regen.Goal16Bridge
import denote.gpt_ly4_regen.Goal_17

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_17 算 585 ==========
theorem denote_sm_goal_17_585 (s : Store) :
    denoteGraph sm_goal_17 s 585 = fw_div ((2 : Nat) : Scalar) (s 584) := by
  simp only [sm_goal_17, denoteGraph, List.foldl]
  rw [applyNode_fw_div_out_g17]
  norm_num

-- ========== 迷你图 pm_goal_17 算 1369-1372 ==========
theorem denote_pm_goal_17_1369 (s : Store) :
    denoteGraph pm_goal_17 s 1369 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 4 0 (s 584)) := by
  simp only [pm_goal_17, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g17]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_17_1370 (s : Store) :
    denoteGraph pm_goal_17 s 1370 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 4 1 (s 584)) := by
  simp only [pm_goal_17, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g17]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_17_1371 (s : Store) :
    denoteGraph pm_goal_17 s 1371 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 4 2 (s 584)) := by
  simp only [pm_goal_17, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g17]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_17_1372 (s : Store) :
    denoteGraph pm_goal_17 s 1372 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 4 3 (s 584)) := by
  simp only [pm_goal_17, denoteGraph, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_div_out_g17]; congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 585 (node 17) ==========
theorem sm_frame_585_self (initSM : Store) :
    denoteGraph sm initSM 585 = denoteGraph sm_goal_17 (denoteGraph sm initSM) 585 := by
  rw [denote_sm_goal_17_585]
  rw [sm_val initSM 17 585 (by native_decide) (by native_decide)]
  rw [show sm.nodes[17]'(by native_decide)
      = { rank := 0, op := "OpName.FW_div", ins := [584], outs := [585], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g17]
  rw [sm_prefix_eq initSM 17 584 (by native_decide)]
  norm_num

-- ========== PM full: 1365-1368 (4 ChunkPrim, node 106-109) ==========
theorem pm_full_1365 (initPM : Store) :
    denoteGraph pm initPM 1365 = chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 584) := by
  rw [pm_val initPM 106 1365 (by native_decide) (by native_decide)]
  rw [show pm.nodes[106]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [584], outs := [1365], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 106 584 (by native_decide)]

theorem pm_full_1366 (initPM : Store) :
    denoteGraph pm initPM 1366 = chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 584) := by
  rw [pm_val initPM 107 1366 (by native_decide) (by native_decide)]
  rw [show pm.nodes[107]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [584], outs := [1366], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 107 584 (by native_decide)]

theorem pm_full_1367 (initPM : Store) :
    denoteGraph pm initPM 1367 = chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 584) := by
  rw [pm_val initPM 108 1367 (by native_decide) (by native_decide)]
  rw [show pm.nodes[108]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [584], outs := [1367], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 108 584 (by native_decide)]

theorem pm_full_1368 (initPM : Store) :
    denoteGraph pm initPM 1368 = chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 584) := by
  rw [pm_val initPM 109 1368 (by native_decide) (by native_decide)]
  rw [show pm.nodes[109]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [584], outs := [1368], params := [1] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out]
  rw [pm_prefix_eq initPM 109 584 (by native_decide)]

-- ========== PM full: 1369-1372 (4 FW_div, node 110-113) ==========
theorem pm_frame_1369_self (initPM : Store) :
    denoteGraph pm initPM 1369 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 pm.numRanks 0 (denoteGraph pm initPM 584)) := by
  rw [pm_val initPM 110 1369 (by native_decide) (by native_decide)]
  rw [show pm.nodes[110]'(by native_decide)
      = { rank := 0, op := "OpName.FW_div", ins := [1365], outs := [1369], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g17]
  rw [pm_prefix_eq initPM 110 1365 (by native_decide)]
  rw [pm_full_1365]
  norm_num

theorem pm_frame_1370_self (initPM : Store) :
    denoteGraph pm initPM 1370 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 pm.numRanks 1 (denoteGraph pm initPM 584)) := by
  rw [pm_val initPM 111 1370 (by native_decide) (by native_decide)]
  rw [show pm.nodes[111]'(by native_decide)
      = { rank := 1, op := "OpName.FW_div", ins := [1366], outs := [1370], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g17]
  rw [pm_prefix_eq initPM 111 1366 (by native_decide)]
  rw [pm_full_1366]
  norm_num

theorem pm_frame_1371_self (initPM : Store) :
    denoteGraph pm initPM 1371 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 pm.numRanks 2 (denoteGraph pm initPM 584)) := by
  rw [pm_val initPM 112 1371 (by native_decide) (by native_decide)]
  rw [show pm.nodes[112]'(by native_decide)
      = { rank := 2, op := "OpName.FW_div", ins := [1367], outs := [1371], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g17]
  rw [pm_prefix_eq initPM 112 1367 (by native_decide)]
  rw [pm_full_1367]
  norm_num

theorem pm_frame_1372_self (initPM : Store) :
    denoteGraph pm initPM 1372 = fw_div ((2 : Nat) : Scalar) (chunkPrimDimN 1 pm.numRanks 3 (denoteGraph pm initPM 584)) := by
  rw [pm_val initPM 113 1372 (by native_decide) (by native_decide)]
  rw [show pm.nodes[113]'(by native_decide)
      = { rank := 3, op := "OpName.FW_div", ins := [1368], outs := [1372], params := [2] }
      from by native_decide]
  rw [applyNode_fw_div_out_g17]
  rw [pm_prefix_eq initPM 113 1368 (by native_decide)]
  rw [pm_full_1368]
  norm_num

-- ========== 总装 ==========
theorem goal_17_cut_to_full (h : goal_17_stmt_cut) : goal_17_stmt := by
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
  have hg9 := goal_9_intermediate initSM initPM hSM hPM hInit
  have hg10 := goal_10_intermediate initSM initPM hSM hPM hInit
  have hg11 := goal_11_intermediate initSM initPM hSM hPM hInit
  have hg12 := goal_12_intermediate initSM initPM hSM hPM hInit
  have hg15 := goal_15_intermediate initSM initPM hSM hPM hInit
  have hg16 := goal_16_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg9 hg10 hg11 hg12 hg15 hg16 hg257 hg261 hg263 hinitC
  have hnr : pm_goal_17.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_17.numRanks goal_17_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_17_cut_initGoals, goal_17_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg2
      · exact hg3
      · exact hg4
      · exact hg5
      · exact hg6
      · exact hg7
      · exact hg9
      · exact hg10
      · exact hg11
      · exact hg12
      · exact hg15
      · exact hg16
      · exact hg257
      · exact hg261
      · exact hg263
  -- shape: 584 = goal_16.ts/tps (singleton), shape [1,4,8,8]
  have h584_smsh : (Ssm 584).shape = [1, 4, 8, 8] := by
    have h := hg16.1; simp only [goal_16] at h; exact h
  have h584_pmsh : (Spm 584).shape = [1, 4, 8, 8] := by
    have h := hg16.2.1; simp only [goal_16, List.map, List.cons.injEq, and_true] at h; exact h
  have hSM17 : StoreShapesHold Ssm sm_goal_17InitEnv := by
    intro tid sh hsh
    rw [sm_goal_17InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_17InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h584_smsh
  have hPM17 : StoreShapesHold Spm pm_goal_17InitEnv := by
    intro tid sh hsh
    rw [pm_goal_17InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_17InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h584_pmsh
  have hcut := h Ssm Spm hSM17 hPM17 hInitCut
  -- Frame: 585 (sm), 1369-1372 (pm)
  have hsmf : Ssm 585 = denoteGraph sm_goal_17 Ssm 585 := by
    rw [hSsm]; exact sm_frame_585_self initSM
  have hpm1369 : Spm 1369 = denoteGraph pm_goal_17 Spm 1369 := by
    rw [denote_pm_goal_17_1369]
    rw [hSpm]
    have := pm_frame_1369_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1370 : Spm 1370 = denoteGraph pm_goal_17 Spm 1370 := by
    rw [denote_pm_goal_17_1370]
    rw [hSpm]
    have := pm_frame_1370_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1371 : Spm 1371 = denoteGraph pm_goal_17 Spm 1371 := by
    rw [denote_pm_goal_17_1371]
    rw [hSpm]
    have := pm_frame_1371_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1372 : Spm 1372 = denoteGraph pm_goal_17 Spm 1372 := by
    rw [denote_pm_goal_17_1372]
    rw [hSpm]
    have := pm_frame_1372_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_17, List.map] at hcut ⊢
  rw [hsmf, hpm1369, hpm1370, hpm1371, hpm1372]
  exact hcut

theorem goal_17_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_17 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_17_stmt := goal_17_cut_to_full prove_goal_17_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
