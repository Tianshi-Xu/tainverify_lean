/- goal_16 桥 (prereqs=[2,3,4,5,6,7,9,10,11,12,15,257,261,263])。
   SM=FW_matmul(578,583)→584 (sm node 16);
   PM=4×FW_matmul(1261+r,1333+r)→1353-1356 (pm node 101-104), 然后 AllReducePrim(range4.map(1353+r))→584 (pm node 105)。
   578=goal_10 输出 (gather dim3, tps 1261-1264); 583=goal_15 输出 (gather dim2, tps 1333-1336)。
   第 11 种结构: FW_matmul over contraction-dim split + AllReduce。
   套 goal_6 (collective-collect-in-PM, computed range ins 模板) + goal_10 (two-input shard frame)。
   注: matmul-split 语义在 cut 证明里已处理 (fw_matmul_split_dimK); bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal10Bridge
import denote.gpt_ly4_regen.Goal15Bridge
import denote.gpt_ly4_regen.Goal_16

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_16 算 584 (FW_matmul) ==========
theorem denote_sm_goal_16_584 (s : Store) :
    denoteGraph sm_goal_16 s 584 = fw_matmul (s 578) (s 583) := by
  simp only [sm_goal_16, denoteGraph, List.foldl]
  rw [applyNode_fw_matmul_out]

-- ========== 迷你图 pm_goal_16 算 584 (4×FW_matmul → AllReduce) ==========
theorem denote_pm_goal_16_584 (s : Store) :
    denoteGraph pm_goal_16 s 584 = allReducePrim 4 0
      [fw_matmul (s 1261) (s 1333), fw_matmul (s 1262) (s 1334),
       fw_matmul (s 1263) (s 1335), fw_matmul (s 1264) (s 1336)] := by
  simp only [pm_goal_16, denoteGraph, List.foldl]
  rw [applyNode_allReducePrim_out]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full sm 算 584 (node 16 FW_matmul) ==========
theorem sm_frame_584_self (initSM : Store) :
    denoteGraph sm initSM 584 = denoteGraph sm_goal_16 (denoteGraph sm initSM) 584 := by
  rw [denote_sm_goal_16_584]
  rw [sm_val initSM 16 584 (by native_decide) (by native_decide)]
  rw [show sm.nodes[16]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [578, 583], outs := [584] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [sm_prefix_eq initSM 16 578 (by native_decide),
      sm_prefix_eq initSM 16 583 (by native_decide)]

-- ========== full pm 算 FW_matmul 输出 1353-1356 (node 101-104) = fw_matmul(Spm 1261+r, Spm 1333+r) ==========
theorem pm_full_1353 (initPM : Store) :
    denoteGraph pm initPM 1353 = fw_matmul (denoteGraph pm initPM 1261) (denoteGraph pm initPM 1333) := by
  rw [pm_val initPM 101 1353 (by native_decide) (by native_decide)]
  rw [show pm.nodes[101]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [1261, 1333], outs := [1353] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 101 1261 (by native_decide),
      pm_prefix_eq initPM 101 1333 (by native_decide)]

theorem pm_full_1354 (initPM : Store) :
    denoteGraph pm initPM 1354 = fw_matmul (denoteGraph pm initPM 1262) (denoteGraph pm initPM 1334) := by
  rw [pm_val initPM 102 1354 (by native_decide) (by native_decide)]
  rw [show pm.nodes[102]'(by native_decide)
      = { rank := 1, op := "OpName.FW_matmul", ins := [1262, 1334], outs := [1354] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 102 1262 (by native_decide),
      pm_prefix_eq initPM 102 1334 (by native_decide)]

theorem pm_full_1355 (initPM : Store) :
    denoteGraph pm initPM 1355 = fw_matmul (denoteGraph pm initPM 1263) (denoteGraph pm initPM 1335) := by
  rw [pm_val initPM 103 1355 (by native_decide) (by native_decide)]
  rw [show pm.nodes[103]'(by native_decide)
      = { rank := 2, op := "OpName.FW_matmul", ins := [1263, 1335], outs := [1355] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 103 1263 (by native_decide),
      pm_prefix_eq initPM 103 1335 (by native_decide)]

theorem pm_full_1356 (initPM : Store) :
    denoteGraph pm initPM 1356 = fw_matmul (denoteGraph pm initPM 1264) (denoteGraph pm initPM 1336) := by
  rw [pm_val initPM 104 1356 (by native_decide) (by native_decide)]
  rw [show pm.nodes[104]'(by native_decide)
      = { rank := 3, op := "OpName.FW_matmul", ins := [1264, 1336], outs := [1356] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 104 1264 (by native_decide),
      pm_prefix_eq initPM 104 1336 (by native_decide)]

-- ========== PM self-frame: 584 (AllReduce node 105, ins=computed range) ==========
theorem pm_frame_584_self (initPM : Store) :
    denoteGraph pm initPM 584
      = allReducePrim 4 0
          [fw_matmul (denoteGraph pm initPM 1261) (denoteGraph pm initPM 1333),
           fw_matmul (denoteGraph pm initPM 1262) (denoteGraph pm initPM 1334),
           fw_matmul (denoteGraph pm initPM 1263) (denoteGraph pm initPM 1335),
           fw_matmul (denoteGraph pm initPM 1264) (denoteGraph pm initPM 1336)] := by
  rw [pm_val initPM 105 584 (by native_decide) (by native_decide)]
  rw [show pm.nodes[105]'(by native_decide)
      = { rank := 0, op := "OpName.AllReducePrim",
          ins := ((List.range 4).map (fun r => 1353 + r)), outs := [584] }
      from by native_decide]
  rw [applyNode_allReducePrim_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 105 1353 (by native_decide),
      pm_prefix_eq initPM 105 1354 (by native_decide),
      pm_prefix_eq initPM 105 1355 (by native_decide),
      pm_prefix_eq initPM 105 1356 (by native_decide)]
  rw [pm_full_1353, pm_full_1354, pm_full_1355, pm_full_1356]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_16_cut_to_full (h : goal_16_stmt_cut) : goal_16_stmt := by
  intro initSM initPM hSM hPM hInit
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  have hnr : pm_goal_16.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_16.numRanks goal_16_cut_initGoals Ssm Spm := by
    rw [hnr]; intro g hg
    simp only [goal_16_cut_initGoals, goal_16_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact hg257
      · exact hg261
      · exact hg263
  -- shape envs for sm_goal_16 (578,583) and pm_goal_16 (1261-1264, 1333-1336)
  -- 578 = goal_10.ts, 1261-1264 = goal_10.tps; 583 = goal_15.ts, 1333-1336 = goal_15.tps
  have h578_smsh : (Ssm 578).shape = [1, 4, 8, 8] := by
    have h := hg10.1; simp only [goal_10] at h; exact h
  have h583_smsh : (Ssm 583).shape = [1, 4, 8, 8] := by
    have h := hg15.1; simp only [goal_15] at h; exact h
  have hx : (Spm 1261).shape = [1,4,8,2] ∧ (Spm 1262).shape = [1,4,8,2] ∧
            (Spm 1263).shape = [1,4,8,2] ∧ (Spm 1264).shape = [1,4,8,2] := by
    have h := hg10.2.1
    simp only [goal_10, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1261sh, h1262sh, h1263sh, h1264sh⟩ := hx
  have hy : (Spm 1333).shape = [1,4,2,8] ∧ (Spm 1334).shape = [1,4,2,8] ∧
            (Spm 1335).shape = [1,4,2,8] ∧ (Spm 1336).shape = [1,4,2,8] := by
    have h := hg15.2.1
    simp only [goal_15, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1333sh, h1334sh, h1335sh, h1336sh⟩ := hy
  have hSM16 : StoreShapesHold Ssm sm_goal_16InitEnv := by
    intro tid sh hsh
    rw [sm_goal_16InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_16InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h578_smsh
    · exact h583_smsh
  have hPM16 : StoreShapesHold Spm pm_goal_16InitEnv := by
    intro tid sh hsh
    rw [pm_goal_16InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_16InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1261sh
    · exact h1262sh
    · exact h1263sh
    · exact h1264sh
    · exact h1333sh
    · exact h1334sh
    · exact h1335sh
    · exact h1336sh
  have hcut := h Ssm Spm hSM16 hPM16 hInitCut
  -- Frame: 584 (sm node 16), 584 (pm node 105)
  have hsmf : Ssm 584 = denoteGraph sm_goal_16 Ssm 584 := by
    rw [hSsm]; exact sm_frame_584_self initSM
  have hpm584 : Spm 584 = denoteGraph pm_goal_16 Spm 584 := by
    rw [denote_pm_goal_16_584]
    rw [hSpm]; exact pm_frame_584_self initPM
  rw [hnr] at hcut
  simp only [goal_16, List.map] at hcut ⊢
  rw [hsmf, hpm584]
  exact hcut

theorem goal_16_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_16 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_16_stmt := goal_16_cut_to_full prove_goal_16_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_16] using this

end TrainVerify.Denote.GeneratedGoals
