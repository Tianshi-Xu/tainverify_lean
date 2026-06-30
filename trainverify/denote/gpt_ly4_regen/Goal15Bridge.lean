/- goal_15 桥 (prereqs=[2,3,4,5,7,11,12,257,263])。SM=FW_transpose(580,p=[2,3])→583;
   PM=4×AllToAllPrim((range4).map(1285+),idim=1,odim=3)→1329-1332, 然后 4×FW_transpose(1329..,p=[2,3])→1333-1336. tps=4个.
   580=goal_11 输出 [1,4,8,8]. 第 10 种结构: AllToAll+FW_transpose, multi-tps.
   套 goal_10 (transpose multi-tps frame) + goal_6 (computed-ins collective) 模板。
   注: AllToAll 语义在 cut 证明里已处理; bridge 只做 frame (两边 mini/full 都含 AllToAll, 不展开语义)。 -/
import denote.gpt_ly4_regen.Goal11Bridge
import denote.gpt_ly4_regen.Goal12Bridge
import denote.gpt_ly4_regen.Goal_15

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_15 算 583 ==========
theorem denote_sm_goal_15_583 (s : Store) :
    denoteGraph sm_goal_15 s 583 = transposeAxes 2 3 (s 580) := by
  simp only [sm_goal_15, denoteGraph, List.foldl]
  rw [applyNode_fw_transposeAxes_out]

-- ========== 迷你图 pm_goal_15 算 1333-1336 (AllToAll → transpose) ==========
-- 每个 = transposeAxes 2 3 (allToAllPrimWithDims 4 r [s 1285, s 1286, s 1287, s 1288] 1 3)
theorem denote_pm_goal_15_1333 (s : Store) :
    denoteGraph pm_goal_15 s 1333
      = transposeAxes 2 3 (allToAllPrimWithDims 4 0 [s 1285, s 1286, s 1287, s 1288] 1 3) := by
  simp only [pm_goal_15, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_15_1334 (s : Store) :
    denoteGraph pm_goal_15 s 1334
      = transposeAxes 2 3 (allToAllPrimWithDims 4 1 [s 1285, s 1286, s 1287, s 1288] 1 3) := by
  simp only [pm_goal_15, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_15_1335 (s : Store) :
    denoteGraph pm_goal_15 s 1335
      = transposeAxes 2 3 (allToAllPrimWithDims 4 2 [s 1285, s 1286, s 1287, s 1288] 1 3) := by
  simp only [pm_goal_15, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

theorem denote_pm_goal_15_1336 (s : Store) :
    denoteGraph pm_goal_15 s 1336
      = transposeAxes 2 3 (allToAllPrimWithDims 4 3 [s 1285, s 1286, s 1287, s 1288] 1 3) := by
  simp only [pm_goal_15, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_transposeAxes_out]
  congr 1
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== SM self-frame: full sm 算 583 (node 15) ==========
theorem sm_frame_583_self (initSM : Store) :
    denoteGraph sm initSM 583 = denoteGraph sm_goal_15 (denoteGraph sm initSM) 583 := by
  rw [denote_sm_goal_15_583]
  rw [sm_val initSM 15 583 (by native_decide) (by native_decide)]
  rw [show sm.nodes[15]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [580], outs := [583], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [sm_prefix_eq initSM 15 580 (by native_decide)]

-- ========== PM full: 1329-1332 (4 AllToAll, node 93-96, ins=computed range) ==========
theorem pm_full_g15_1329 (initPM : Store) :
    denoteGraph pm initPM 1329
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3 := by
  rw [pm_val initPM 93 1329 (by native_decide) (by native_decide)]
  rw [show pm.nodes[93]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1285 + r)), outs := [1329], params := [1, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 93 1285 (by native_decide),
      pm_prefix_eq initPM 93 1286 (by native_decide),
      pm_prefix_eq initPM 93 1287 (by native_decide),
      pm_prefix_eq initPM 93 1288 (by native_decide)]

theorem pm_full_g15_1330 (initPM : Store) :
    denoteGraph pm initPM 1330
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3 := by
  rw [pm_val initPM 94 1330 (by native_decide) (by native_decide)]
  rw [show pm.nodes[94]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1285 + r)), outs := [1330], params := [1, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 94 1285 (by native_decide),
      pm_prefix_eq initPM 94 1286 (by native_decide),
      pm_prefix_eq initPM 94 1287 (by native_decide),
      pm_prefix_eq initPM 94 1288 (by native_decide)]

theorem pm_full_g15_1331 (initPM : Store) :
    denoteGraph pm initPM 1331
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3 := by
  rw [pm_val initPM 95 1331 (by native_decide) (by native_decide)]
  rw [show pm.nodes[95]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1285 + r)), outs := [1331], params := [1, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 95 1285 (by native_decide),
      pm_prefix_eq initPM 95 1286 (by native_decide),
      pm_prefix_eq initPM 95 1287 (by native_decide),
      pm_prefix_eq initPM 95 1288 (by native_decide)]

theorem pm_full_g15_1332 (initPM : Store) :
    denoteGraph pm initPM 1332
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3 := by
  rw [pm_val initPM 96 1332 (by native_decide) (by native_decide)]
  rw [show pm.nodes[96]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1285 + r)), outs := [1332], params := [1, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 96 1285 (by native_decide),
      pm_prefix_eq initPM 96 1286 (by native_decide),
      pm_prefix_eq initPM 96 1287 (by native_decide),
      pm_prefix_eq initPM 96 1288 (by native_decide)]

-- ========== PM full: 1333-1336 (4 FW_transpose, node 97-100) ==========
theorem pm_frame_1333_self (initPM : Store) :
    denoteGraph pm initPM 1333
      = transposeAxes 2 3 (allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3) := by
  rw [pm_val initPM 97 1333 (by native_decide) (by native_decide)]
  rw [show pm.nodes[97]'(by native_decide)
      = { rank := 0, op := "OpName.FW_transpose", ins := [1329], outs := [1333], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 97 1329 (by native_decide)]
  rw [pm_full_g15_1329]

theorem pm_frame_1334_self (initPM : Store) :
    denoteGraph pm initPM 1334
      = transposeAxes 2 3 (allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3) := by
  rw [pm_val initPM 98 1334 (by native_decide) (by native_decide)]
  rw [show pm.nodes[98]'(by native_decide)
      = { rank := 1, op := "OpName.FW_transpose", ins := [1330], outs := [1334], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 98 1330 (by native_decide)]
  rw [pm_full_g15_1330]

theorem pm_frame_1335_self (initPM : Store) :
    denoteGraph pm initPM 1335
      = transposeAxes 2 3 (allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3) := by
  rw [pm_val initPM 99 1335 (by native_decide) (by native_decide)]
  rw [show pm.nodes[99]'(by native_decide)
      = { rank := 2, op := "OpName.FW_transpose", ins := [1331], outs := [1335], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 99 1331 (by native_decide)]
  rw [pm_full_g15_1331]

theorem pm_frame_1336_self (initPM : Store) :
    denoteGraph pm initPM 1336
      = transposeAxes 2 3 (allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1285, denoteGraph pm initPM 1286,
           denoteGraph pm initPM 1287, denoteGraph pm initPM 1288] 1 3) := by
  rw [pm_val initPM 100 1336 (by native_decide) (by native_decide)]
  rw [show pm.nodes[100]'(by native_decide)
      = { rank := 3, op := "OpName.FW_transpose", ins := [1332], outs := [1336], params := [2, 3] }
      from by native_decide]
  rw [applyNode_fw_transposeAxes_out]
  rw [pm_prefix_eq initPM 100 1332 (by native_decide)]
  rw [pm_full_g15_1332]

-- ========== 总装 ==========
theorem goal_15_cut_to_full (h : goal_15_stmt_cut) : goal_15_stmt := by
  intro initSM initPM hSM hPM hInit
  obtain ⟨Ssm, hSsm⟩ : ∃ S, S = denoteGraph sm initSM := ⟨_, rfl⟩
  obtain ⟨Spm, hSpm⟩ : ∃ S, S = denoteGraph pm initPM := ⟨_, rfl⟩
  rw [← hSsm, ← hSpm]
  have hg2 := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 := goal_3_intermediate initSM initPM hSM hPM hInit
  have hg4 := goal_4_intermediate initSM initPM hSM hPM hInit
  have hg5 := goal_5_intermediate initSM initPM hSM hPM hInit
  have hg7 := goal_7_intermediate initSM initPM hSM hPM hInit
  have hg11 := goal_11_intermediate initSM initPM hSM hPM hInit
  have hg12 := goal_12_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg7 hg11 hg12 hg257 hg263 hinitC
  have hnr : pm_goal_15.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_15.numRanks goal_15_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_15_cut_initGoals, goal_15_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg7, hg11, hg12, hg257, hg263, List.forall_mem_nil _⟩
  -- shape 弱化: 580=goal_12.ts [1,4,8,8]; 1285-1288=goal_12.tps [1,1,8,8]
  have h580_smsh : (Ssm 580).shape = [1, 4, 8, 8] := by
    have h := hg12.1; simp only [goal_12] at h; exact h
  have h1285_pmsh : (Spm 1285).shape = [1, 1, 8, 8] := by
    have h := hg12.2.1; simp only [goal_12, List.map, List.cons.injEq, and_true] at h; exact h.1
  have h1286_pmsh : (Spm 1286).shape = [1, 1, 8, 8] := by
    have h := hg12.2.1; simp only [goal_12, List.map, List.cons.injEq, and_true] at h; exact h.2.1
  have h1287_pmsh : (Spm 1287).shape = [1, 1, 8, 8] := by
    have h := hg12.2.1; simp only [goal_12, List.map, List.cons.injEq, and_true] at h; exact h.2.2.1
  have h1288_pmsh : (Spm 1288).shape = [1, 1, 8, 8] := by
    have h := hg12.2.1; simp only [goal_12, List.map, List.cons.injEq, and_true] at h; exact h.2.2.2
  have hSM15 : StoreShapesHold Ssm sm_goal_15InitEnv := by
    intro tid sh hsh
    rw [sm_goal_15InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_15InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h580_smsh
  have hPM15 : StoreShapesHold Spm pm_goal_15InitEnv := by
    intro tid sh hsh
    rw [pm_goal_15InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_15InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1285_pmsh
    · exact h1286_pmsh
    · exact h1287_pmsh
    · exact h1288_pmsh
  have hcut := h Ssm Spm hSM15 hPM15 hInitCut
  -- Frame: 583 (sm), 1333-1336 (pm)
  have hsmf : Ssm 583 = denoteGraph sm_goal_15 Ssm 583 := by
    rw [hSsm]; exact sm_frame_583_self initSM
  have hpm1333 : Spm 1333 = denoteGraph pm_goal_15 Spm 1333 := by
    rw [denote_pm_goal_15_1333]
    rw [hSpm]
    have := pm_frame_1333_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1334 : Spm 1334 = denoteGraph pm_goal_15 Spm 1334 := by
    rw [denote_pm_goal_15_1334]
    rw [hSpm]
    have := pm_frame_1334_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1335 : Spm 1335 = denoteGraph pm_goal_15 Spm 1335 := by
    rw [denote_pm_goal_15_1335]
    rw [hSpm]
    have := pm_frame_1335_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  have hpm1336 : Spm 1336 = denoteGraph pm_goal_15 Spm 1336 := by
    rw [denote_pm_goal_15_1336]
    rw [hSpm]
    have := pm_frame_1336_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_15, List.map] at hcut ⊢
  rw [hsmf, hpm1333, hpm1334, hpm1335, hpm1336]
  exact hcut

theorem goal_15_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_15 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_15_stmt := goal_15_cut_to_full prove_goal_15_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
