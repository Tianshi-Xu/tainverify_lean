/- goal_18 桥 (prereqs=[2,3,4,5,6,7,9,10,11,12,15,16,17,257,261,263])。第13种结构: AllToAll+FW_softmax+AllGather (单 tp)。
   SM=FW_softmax(585)→586 (node 18)。
   PM=4×AllToAllPrim((range4).map(1369+),idim=1,odim=2)→1389-1392 (node 114-117),
      4×FW_softmax(1389..)→1393-1396 (node 118-121),
      AllGatherPrim((range4).map(1393+),dim=2)→586 (node 122, 单 tp)。
   585=goal_17 输出 [1,4,8,8]; 1369-1372=goal_17 tps [1,1,8,8]。
   套 goal_15 (AllToAll computed-ins frame) + goal_6 (单输出 AllGather computed-ins tail) 模板。
   注: AllToAll/softmax/AllGather 的代数语义 (softmax 在 dim2 split 下分配) 已在 cut 证明里处理;
       bridge 只做 frame (两边 mini/full 在 586 处对齐, 不展开语义)。 -/
import denote.gpt_ly4_regen.Goal15Bridge
import denote.gpt_ly4_regen.Goal16Bridge
import denote.gpt_ly4_regen.Goal17Bridge
import denote.gpt_ly4_regen.Goal_18

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_18 算 586 (FW_softmax) ==========
theorem denote_sm_goal_18_586 (s : Store) :
    denoteGraph sm_goal_18 s 586 = fw_softmax (s 585) := by
  simp only [sm_goal_18, denoteGraph, List.foldl]
  rw [applyNode_fw_softmax_out_g18]

-- ========== SM self-frame: full sm 算 586 (node 18 FW_softmax) ==========
theorem sm_frame_586_self (initSM : Store) :
    denoteGraph sm initSM 586 = denoteGraph sm_goal_18 (denoteGraph sm initSM) 586 := by
  rw [denote_sm_goal_18_586]
  rw [sm_val initSM 18 586 (by native_decide) (by native_decide)]
  rw [show sm.nodes[18]'(by native_decide)
      = { rank := 0, op := "OpName.FW_softmax", ins := [585], outs := [586] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g18]
  rw [sm_prefix_eq initSM 18 585 (by native_decide)]

-- ========== full pm: AllToAll 输出 1389-1392 (node 114-117, ins=computed range) ==========
theorem pm_full_1389 (initPM : Store) :
    denoteGraph pm initPM 1389
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2 := by
  rw [pm_val initPM 114 1389 (by native_decide) (by native_decide)]
  rw [show pm.nodes[114]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1369 + r)), outs := [1389], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 114 1369 (by native_decide),
      pm_prefix_eq initPM 114 1370 (by native_decide),
      pm_prefix_eq initPM 114 1371 (by native_decide),
      pm_prefix_eq initPM 114 1372 (by native_decide)]

theorem pm_full_1390 (initPM : Store) :
    denoteGraph pm initPM 1390
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2 := by
  rw [pm_val initPM 115 1390 (by native_decide) (by native_decide)]
  rw [show pm.nodes[115]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1369 + r)), outs := [1390], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 115 1369 (by native_decide),
      pm_prefix_eq initPM 115 1370 (by native_decide),
      pm_prefix_eq initPM 115 1371 (by native_decide),
      pm_prefix_eq initPM 115 1372 (by native_decide)]

theorem pm_full_1391 (initPM : Store) :
    denoteGraph pm initPM 1391
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2 := by
  rw [pm_val initPM 116 1391 (by native_decide) (by native_decide)]
  rw [show pm.nodes[116]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1369 + r)), outs := [1391], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 116 1369 (by native_decide),
      pm_prefix_eq initPM 116 1370 (by native_decide),
      pm_prefix_eq initPM 116 1371 (by native_decide),
      pm_prefix_eq initPM 116 1372 (by native_decide)]

theorem pm_full_1392 (initPM : Store) :
    denoteGraph pm initPM 1392
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2 := by
  rw [pm_val initPM 117 1392 (by native_decide) (by native_decide)]
  rw [show pm.nodes[117]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1369 + r)), outs := [1392], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 117 1369 (by native_decide),
      pm_prefix_eq initPM 117 1370 (by native_decide),
      pm_prefix_eq initPM 117 1371 (by native_decide),
      pm_prefix_eq initPM 117 1372 (by native_decide)]

-- ========== full pm: FW_softmax 输出 1393-1396 (node 118-121) = fw_softmax(AllToAll out) ==========
theorem pm_full_1393 (initPM : Store) :
    denoteGraph pm initPM 1393
      = fw_softmax (allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2) := by
  rw [pm_val initPM 118 1393 (by native_decide) (by native_decide)]
  rw [show pm.nodes[118]'(by native_decide)
      = { rank := 0, op := "OpName.FW_softmax", ins := [1389], outs := [1393] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g18]
  rw [pm_prefix_eq initPM 118 1389 (by native_decide)]
  rw [pm_full_1389]

theorem pm_full_1394 (initPM : Store) :
    denoteGraph pm initPM 1394
      = fw_softmax (allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2) := by
  rw [pm_val initPM 119 1394 (by native_decide) (by native_decide)]
  rw [show pm.nodes[119]'(by native_decide)
      = { rank := 1, op := "OpName.FW_softmax", ins := [1390], outs := [1394] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g18]
  rw [pm_prefix_eq initPM 119 1390 (by native_decide)]
  rw [pm_full_1390]

theorem pm_full_1395 (initPM : Store) :
    denoteGraph pm initPM 1395
      = fw_softmax (allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2) := by
  rw [pm_val initPM 120 1395 (by native_decide) (by native_decide)]
  rw [show pm.nodes[120]'(by native_decide)
      = { rank := 2, op := "OpName.FW_softmax", ins := [1391], outs := [1395] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g18]
  rw [pm_prefix_eq initPM 120 1391 (by native_decide)]
  rw [pm_full_1391]

theorem pm_full_1396 (initPM : Store) :
    denoteGraph pm initPM 1396
      = fw_softmax (allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
           denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2) := by
  rw [pm_val initPM 121 1396 (by native_decide) (by native_decide)]
  rw [show pm.nodes[121]'(by native_decide)
      = { rank := 3, op := "OpName.FW_softmax", ins := [1392], outs := [1396] }
      from by native_decide]
  rw [applyNode_fw_softmax_out_g18]
  rw [pm_prefix_eq initPM 121 1392 (by native_decide)]
  rw [pm_full_1392]

-- ========== PM self-frame: 586 (AllGather node 122, ins=computed range, 单 tp) ==========
theorem pm_frame_586_self (initPM : Store) :
    denoteGraph pm initPM 586
      = allGatherPrimDimN 2 4 0
          [fw_softmax (allToAllPrimWithDims pm.numRanks 0
              [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
               denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2),
           fw_softmax (allToAllPrimWithDims pm.numRanks 1
              [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
               denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2),
           fw_softmax (allToAllPrimWithDims pm.numRanks 2
              [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
               denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2),
           fw_softmax (allToAllPrimWithDims pm.numRanks 3
              [denoteGraph pm initPM 1369, denoteGraph pm initPM 1370,
               denoteGraph pm initPM 1371, denoteGraph pm initPM 1372] 1 2)] := by
  rw [pm_val initPM 122 586 (by native_decide) (by native_decide)]
  rw [show pm.nodes[122]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 1393 + r)), outs := [586], params := [2] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 122 1393 (by native_decide),
      pm_prefix_eq initPM 122 1394 (by native_decide),
      pm_prefix_eq initPM 122 1395 (by native_decide),
      pm_prefix_eq initPM 122 1396 (by native_decide)]
  rw [pm_full_1393, pm_full_1394, pm_full_1395, pm_full_1396]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 迷你图 pm_goal_18 算 586 (4×AllToAll → 4×softmax → AllGather) ==========
theorem denote_pm_goal_18_586 (s : Store) :
    denoteGraph pm_goal_18 s 586 = allGatherPrimDimN 2 4 0
      [fw_softmax (allToAllPrimWithDims 4 0 [s 1369, s 1370, s 1371, s 1372] 1 2),
       fw_softmax (allToAllPrimWithDims 4 1 [s 1369, s 1370, s 1371, s 1372] 1 2),
       fw_softmax (allToAllPrimWithDims 4 2 [s 1369, s 1370, s 1371, s 1372] 1 2),
       fw_softmax (allToAllPrimWithDims 4 3 [s 1369, s 1370, s 1371, s 1372] 1 2)] := by
  simp only [pm_goal_18, denoteGraph, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  congr 1

-- ========== 总装 ==========
theorem goal_18_cut_to_full (h : goal_18_stmt_cut) : goal_18_stmt := by
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
  have hg17 := goal_17_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg9 hg10 hg11 hg12 hg15 hg16 hg17 hg257 hg261 hg263 hinitC
  have hnr : pm_goal_18.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 585=goal_17.ts [1,4,8,8]; 1369-1372=goal_17.tps [1,1,8,8]
  have h585_smsh : (Ssm 585).shape = [1, 4, 8, 8] := by
    have h := hg17.1; simp only [goal_17] at h; exact h
  have h1369_pmsh : (Spm 1369).shape = [1, 1, 8, 8] := by
    have h := hg17.2.1; simp only [goal_17, List.map, List.cons.injEq, and_true] at h; exact h.1
  have h1370_pmsh : (Spm 1370).shape = [1, 1, 8, 8] := by
    have h := hg17.2.1; simp only [goal_17, List.map, List.cons.injEq, and_true] at h; exact h.2.1
  have h1371_pmsh : (Spm 1371).shape = [1, 1, 8, 8] := by
    have h := hg17.2.1; simp only [goal_17, List.map, List.cons.injEq, and_true] at h; exact h.2.2.1
  have h1372_pmsh : (Spm 1372).shape = [1, 1, 8, 8] := by
    have h := hg17.2.1; simp only [goal_17, List.map, List.cons.injEq, and_true] at h; exact h.2.2.2
  have hSM18 : StoreShapesHold Ssm sm_goal_18InitEnv := by
    intro tid sh hsh
    rw [sm_goal_18InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_18InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h585_smsh
  have hPM18 : StoreShapesHold Spm pm_goal_18InitEnv := by
    intro tid sh hsh
    rw [pm_goal_18InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_18InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1369_pmsh
    · exact h1370_pmsh
    · exact h1371_pmsh
    · exact h1372_pmsh
  have hInitCut : InitGoalsHold pm_goal_18.numRanks goal_18_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_18_cut_initGoals, goal_18_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg9, hg10, hg11, hg12, hg15, hg16, hg17, hg257, hg261, hg263, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM18 hPM18 hInitCut
  -- Frame: 586 (sm) 与 586 (pm) 对齐到 mini-graph
  have hsmf : Ssm 586 = denoteGraph sm_goal_18 Ssm 586 := by
    rw [hSsm]; exact sm_frame_586_self initSM
  have hpmf : Spm 586 = denoteGraph pm_goal_18 Spm 586 := by
    rw [denote_pm_goal_18_586]
    rw [hSpm]
    have := pm_frame_586_self initPM
    rw [show (pm.numRanks : Nat) = 4 from by native_decide] at this
    exact this
  rw [hnr] at hcut
  simp only [goal_18, List.map] at hcut ⊢
  rw [hsmf, hpmf]
  exact hcut

theorem goal_18_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_18 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_18_stmt := goal_18_cut_to_full prove_goal_18_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
