/- goal_4 桥 (非 base case, prereqs=[goal_2,goal_3])。验证拓扑归纳。
   核心: full computed store 当迷你图 init; prereq InitGoalHolds = goal_2/3 桥结论。 -/
import denote.gpt_ly4_regen.SpikeBridge
import denote.gpt_ly4_regen.Goal3Bridge
import denote.gpt_ly4_regen.Goal_4

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== SM self-frame: full 算 567 = 迷你图以 full store 为 init 算 567 ==========
theorem denote_sm_goal_4_567 (s : Store) :
    denoteGraph sm_goal_4 s 567 = elemwiseAdd (s 564) (s 566) := by
  simp only [sm_goal_4, denoteGraph, List.foldl]
  rw [applyNode_fw_add2_out]

theorem sm_frame_567_self (initSM : Store) :
    denoteGraph sm initSM 567 = denoteGraph sm_goal_4 (denoteGraph sm initSM) 567 := by
  rw [denote_sm_goal_4_567]
  have hsplit : sm.nodes = sm.nodes.take 3 ++ sm.nodes.drop 3 :=
    (List.take_append_drop 3 sm.nodes).symm
  have hno : ∀ n ∈ sm.nodes.drop 3, (567:Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes sm initSM 567 (sm.nodes.take 3) (sm.nodes.drop 3) hsplit hno]
  have h564f : denoteGraph sm initSM 564 = denoteGraph { sm with nodes := sm.nodes.take 3 } initSM 564 := by
    have hno2 : ∀ n ∈ sm.nodes.drop 3, (564:Tid) ∉ n.outs := by native_decide
    rw [denoteGraph_tid_eq_of_suffix_no_writes sm initSM 564 (sm.nodes.take 3) (sm.nodes.drop 3) hsplit hno2]
  have h566f : denoteGraph sm initSM 566 = denoteGraph { sm with nodes := sm.nodes.take 3 } initSM 566 := by
    have hno3 : ∀ n ∈ sm.nodes.drop 3, (566:Tid) ∉ n.outs := by native_decide
    rw [denoteGraph_tid_eq_of_suffix_no_writes sm initSM 566 (sm.nodes.take 3) (sm.nodes.drop 3) hsplit hno3]
  rw [h564f, h566f]
  simp only [sm, List.take, denoteGraph, GraphDecl.nodes, List.foldl]
  rw [applyNode_fw_add2_out]
  congr 1 <;> rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== PM self-frame: full 算 1117-1120 = 迷你图以 full store 为 init 算 ==========
-- 迷你图 pm_goal_4 以任意 store s 算 1117-1120 (单 fw_add 节点, chunk/alltoall 沿 foldl defeq 化简)
theorem denote_pm_goal_4_1117 (s : Store) :
    denoteGraph pm_goal_4 s 1117 =
      elemwiseAdd (chunkPrimDimN 2 4 0 (s 564))
        (allToAllPrimWithDims 4 0 [s 1089, s 1090, s 1091, s 1092] 1 2) := by
  simp only [pm_goal_4, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]; congr 1

theorem denote_pm_goal_4_1118 (s : Store) :
    denoteGraph pm_goal_4 s 1118 =
      elemwiseAdd (chunkPrimDimN 2 4 1 (s 564))
        (allToAllPrimWithDims 4 1 [s 1089, s 1090, s 1091, s 1092] 1 2) := by
  simp only [pm_goal_4, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]; congr 1

theorem denote_pm_goal_4_1119 (s : Store) :
    denoteGraph pm_goal_4 s 1119 =
      elemwiseAdd (chunkPrimDimN 2 4 2 (s 564))
        (allToAllPrimWithDims 4 2 [s 1089, s 1090, s 1091, s 1092] 1 2) := by
  simp only [pm_goal_4, denoteGraph, List.foldl]
  rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_add2_out]; congr 1

theorem denote_pm_goal_4_1120 (s : Store) :
    denoteGraph pm_goal_4 s 1120 =
      elemwiseAdd (chunkPrimDimN 2 4 3 (s 564))
        (allToAllPrimWithDims 4 3 [s 1089, s 1090, s 1091, s 1092] 1 2) := by
  simp only [pm_goal_4, denoteGraph, List.foldl]
  rw [applyNode_fw_add2_out]; congr 1

-- 通用: pm 前缀 foldl 单步展开
theorem pm_step (initPM : Store) (k : Nat) (hk : k < pm.nodes.length) :
    denoteGraph {pm with nodes := pm.nodes.take (k+1)} initPM
      = applyNode pm (denoteGraph {pm with nodes := pm.nodes.take k} initPM) pm.nodes[k] := by
  have hfn : applyNode {pm with nodes := pm.nodes.take (k+1)} = applyNode pm :=
    applyNode_congr_numRanks _ _ rfl
  have hfn' : applyNode {pm with nodes := pm.nodes.take k} = applyNode pm :=
    applyNode_congr_numRanks _ _ rfl
  simp only [denoteGraph, hfn, hfn']
  exact foldl_take_succ (applyNode pm) pm.nodes initPM k hk

-- 通用: 单写节点 k 的输出值 = applyNode 该节点 (前缀 store)
theorem pm_val (initPM : Store) (k : Nat) (out : Tid) (hk : k < pm.nodes.length)
    (hdrop : ∀ n ∈ pm.nodes.drop (k+1), out ∉ n.outs) :
    denoteGraph pm initPM out
      = applyNode pm (denoteGraph {pm with nodes := pm.nodes.take k} initPM) pm.nodes[k] out := by
  have e1 : denoteGraph pm initPM out
      = denoteGraph {pm with nodes := pm.nodes.take (k+1)} initPM out :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM out (pm.nodes.take (k+1)) (pm.nodes.drop (k+1))
      (List.take_append_drop (k+1) pm.nodes).symm hdrop
  rw [e1, pm_step initPM k hk]

-- 通用: 后缀不写 tid 时, 前缀算值 = 全图算值
theorem pm_prefix_eq (initPM : Store) (k : Nat) (tid : Tid)
    (hdrop : ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs) :
    denoteGraph {pm with nodes := pm.nodes.take k} initPM tid = denoteGraph pm initPM tid :=
  (denoteGraph_tid_eq_of_suffix_no_writes pm initPM tid (pm.nodes.take k) (pm.nodes.drop k)
    (List.take_append_drop k pm.nodes).symm hdrop).symm

-- chunk 子 frame: 1109-1112
theorem pm_frame_1109 (initPM : Store) :
    denoteGraph pm initPM 1109 = chunkPrimDimN 2 4 0 (denoteGraph pm initPM 564) := by
  rw [pm_val initPM 13 1109 (by native_decide) (by native_decide)]
  rw [show pm.nodes[13]'(by native_decide)
      = { rank := 0, op := "OpName.ChunkPrim", ins := [564], outs := [1109], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out, show pm.numRanks = 4 from rfl,
      pm_prefix_eq initPM 13 564 (by native_decide)]

theorem pm_frame_1110 (initPM : Store) :
    denoteGraph pm initPM 1110 = chunkPrimDimN 2 4 1 (denoteGraph pm initPM 564) := by
  rw [pm_val initPM 14 1110 (by native_decide) (by native_decide)]
  rw [show pm.nodes[14]'(by native_decide)
      = { rank := 1, op := "OpName.ChunkPrim", ins := [564], outs := [1110], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out, show pm.numRanks = 4 from rfl,
      pm_prefix_eq initPM 14 564 (by native_decide)]

theorem pm_frame_1111 (initPM : Store) :
    denoteGraph pm initPM 1111 = chunkPrimDimN 2 4 2 (denoteGraph pm initPM 564) := by
  rw [pm_val initPM 15 1111 (by native_decide) (by native_decide)]
  rw [show pm.nodes[15]'(by native_decide)
      = { rank := 2, op := "OpName.ChunkPrim", ins := [564], outs := [1111], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out, show pm.numRanks = 4 from rfl,
      pm_prefix_eq initPM 15 564 (by native_decide)]

theorem pm_frame_1112 (initPM : Store) :
    denoteGraph pm initPM 1112 = chunkPrimDimN 2 4 3 (denoteGraph pm initPM 564) := by
  rw [pm_val initPM 16 1112 (by native_decide) (by native_decide)]
  rw [show pm.nodes[16]'(by native_decide)
      = { rank := 3, op := "OpName.ChunkPrim", ins := [564], outs := [1112], params := [2] }
      from by native_decide]
  rw [applyNode_chunkPrimDimN_out, show pm.numRanks = 4 from rfl,
      pm_prefix_eq initPM 16 564 (by native_decide)]

-- alltoall 子 frame: 1113-1116
theorem pm_frame_1113 (initPM : Store) :
    denoteGraph pm initPM 1113 = allToAllPrimWithDims 4 0
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  rw [pm_val initPM 17 1113 (by native_decide) (by native_decide)]
  rw [show pm.nodes[17]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim", ins := [1089, 1090, 1091, 1092],
          outs := [1113], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 17 1089 (by native_decide),
      pm_prefix_eq initPM 17 1090 (by native_decide),
      pm_prefix_eq initPM 17 1091 (by native_decide),
      pm_prefix_eq initPM 17 1092 (by native_decide)]

theorem pm_frame_1114 (initPM : Store) :
    denoteGraph pm initPM 1114 = allToAllPrimWithDims 4 1
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  rw [pm_val initPM 18 1114 (by native_decide) (by native_decide)]
  rw [show pm.nodes[18]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim", ins := [1089, 1090, 1091, 1092],
          outs := [1114], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 18 1089 (by native_decide),
      pm_prefix_eq initPM 18 1090 (by native_decide),
      pm_prefix_eq initPM 18 1091 (by native_decide),
      pm_prefix_eq initPM 18 1092 (by native_decide)]

theorem pm_frame_1115 (initPM : Store) :
    denoteGraph pm initPM 1115 = allToAllPrimWithDims 4 2
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  rw [pm_val initPM 19 1115 (by native_decide) (by native_decide)]
  rw [show pm.nodes[19]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim", ins := [1089, 1090, 1091, 1092],
          outs := [1115], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 19 1089 (by native_decide),
      pm_prefix_eq initPM 19 1090 (by native_decide),
      pm_prefix_eq initPM 19 1091 (by native_decide),
      pm_prefix_eq initPM 19 1092 (by native_decide)]

theorem pm_frame_1116 (initPM : Store) :
    denoteGraph pm initPM 1116 = allToAllPrimWithDims 4 3
      [denoteGraph pm initPM 1089, denoteGraph pm initPM 1090,
       denoteGraph pm initPM 1091, denoteGraph pm initPM 1092] 1 2 := by
  rw [pm_val initPM 20 1116 (by native_decide) (by native_decide)]
  rw [show pm.nodes[20]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim", ins := [1089, 1090, 1091, 1092],
          outs := [1116], params := [1, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out, show pm.numRanks = 4 from rfl]
  simp only [List.map]
  rw [pm_prefix_eq initPM 20 1089 (by native_decide),
      pm_prefix_eq initPM 20 1090 (by native_decide),
      pm_prefix_eq initPM 20 1091 (by native_decide),
      pm_prefix_eq initPM 20 1092 (by native_decide)]

theorem pm_frame_1117_self (initPM : Store) :
    denoteGraph pm initPM 1117 = denoteGraph pm_goal_4 (denoteGraph pm initPM) 1117 := by
  rw [denote_pm_goal_4_1117]
  rw [pm_val initPM 21 1117 (by native_decide) (by native_decide)]
  rw [show pm.nodes[21]'(by native_decide)
      = { rank := 0, op := "OpName.FW_add", ins := [1109, 1113], outs := [1117] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 21 1109 (by native_decide),
      pm_prefix_eq initPM 21 1113 (by native_decide),
      pm_frame_1109, pm_frame_1113]

theorem pm_frame_1118_self (initPM : Store) :
    denoteGraph pm initPM 1118 = denoteGraph pm_goal_4 (denoteGraph pm initPM) 1118 := by
  rw [denote_pm_goal_4_1118]
  rw [pm_val initPM 22 1118 (by native_decide) (by native_decide)]
  rw [show pm.nodes[22]'(by native_decide)
      = { rank := 1, op := "OpName.FW_add", ins := [1110, 1114], outs := [1118] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 22 1110 (by native_decide),
      pm_prefix_eq initPM 22 1114 (by native_decide),
      pm_frame_1110, pm_frame_1114]

theorem pm_frame_1119_self (initPM : Store) :
    denoteGraph pm initPM 1119 = denoteGraph pm_goal_4 (denoteGraph pm initPM) 1119 := by
  rw [denote_pm_goal_4_1119]
  rw [pm_val initPM 23 1119 (by native_decide) (by native_decide)]
  rw [show pm.nodes[23]'(by native_decide)
      = { rank := 2, op := "OpName.FW_add", ins := [1111, 1115], outs := [1119] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 23 1111 (by native_decide),
      pm_prefix_eq initPM 23 1115 (by native_decide),
      pm_frame_1111, pm_frame_1115]

theorem pm_frame_1120_self (initPM : Store) :
    denoteGraph pm initPM 1120 = denoteGraph pm_goal_4 (denoteGraph pm initPM) 1120 := by
  rw [denote_pm_goal_4_1120]
  rw [pm_val initPM 24 1120 (by native_decide) (by native_decide)]
  rw [show pm.nodes[24]'(by native_decide)
      = { rank := 3, op := "OpName.FW_add", ins := [1112, 1116], outs := [1120] }
      from by native_decide]
  rw [applyNode_fw_add2_out]
  rw [pm_prefix_eq initPM 24 1112 (by native_decide),
      pm_prefix_eq initPM 24 1116 (by native_decide),
      pm_frame_1112, pm_frame_1116]

-- ========== 拓扑归纳齿轮: 已证 goal 桥 → computed store 上的 InitGoalHolds ==========
-- prove_goal_2_cut + goal_2_cut_to_full 给 goal_2_stmt; 再打包成 InitGoalHolds(=IntermediateGoalHolds)
theorem goal_2_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_2 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_2_stmt := goal_2_cut_to_full prove_goal_2_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_2] using this

theorem goal_3_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_3 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_3_stmt := goal_3_cut_to_full prove_goal_3_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_3] using this

-- ========== initGoals 在 computed store 上保持 (init tid 不被 denoteGraph 改写) ==========
-- 全称：initGoals 所有 g.ts 不被 sm 写、所有 tps.tid 不被 pm 写 (native_decide)
theorem all_initGoal_ts_not_written :
    ∀ g ∈ initGoals, ∀ n ∈ sm.nodes, g.ts ∉ n.outs := by native_decide

theorem all_initGoal_tps_not_written :
    ∀ g ∈ initGoals, ∀ tp ∈ g.tps, ∀ n ∈ pm.nodes, tp.tid ∉ n.outs := by native_decide

theorem initGoals_preserved (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalsHold pm.numRanks initGoals (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  intro g hg
  have hg0 := hInit g hg
  -- g.ts 在 computed SM 不变
  have hts : denoteGraph sm initSM g.ts = initSM g.ts := by
    have : ∀ n ∈ sm.nodes, g.ts ∉ n.outs := all_initGoal_ts_not_written g hg
    have heq := denoteGraph_tid_eq_of_forall_not_mem_outs sm sm.nodes initSM g.ts this
    -- denoteGraph {sm with nodes:=sm.nodes} = denoteGraph sm
    simpa using heq
  -- g.tps 各 tid 在 computed PM 不变
  have htps : ∀ tp ∈ g.tps, denoteGraph pm initPM tp.tid = initPM tp.tid := by
    intro tp htp
    have : ∀ n ∈ pm.nodes, tp.tid ∉ n.outs := all_initGoal_tps_not_written g hg tp htp
    have heq := denoteGraph_tid_eq_of_forall_not_mem_outs pm pm.nodes initPM tp.tid this
    simpa using heq
  -- 重写 InitGoalHolds: 把 computed store 换回 init store
  unfold InitGoalHolds at hg0 ⊢
  simp only [hts]
  rw [List.map_congr_left (g := fun p => initPM p.tid)]
  · exact hg0
  · intro tp htp; exact htps tp htp

-- ========== 总装: goal_4_cut_to_full ==========
theorem goal_4_cut_to_full (h : goal_4_stmt_cut) : goal_4_stmt := by
  intro initSM initPM hSM hPM hInit
  -- computed stores
  set Ssm := denoteGraph sm initSM with hSsm
  set Spm := denoteGraph pm initPM with hSpm
  -- 拓扑归纳: goal_2/goal_3 在 computed store 上的 InitGoalHolds
  have hg2 : InitGoalHolds pm.numRanks goal_2 Ssm Spm := goal_2_intermediate initSM initPM hSM hPM hInit
  have hg3 : InitGoalHolds pm.numRanks goal_3 Ssm Spm := goal_3_intermediate initSM initPM hSM hPM hInit
  -- initGoals 在 computed store 上保持
  have hinitC : InitGoalsHold pm.numRanks initGoals Ssm Spm := initGoals_preserved initSM initPM hInit
  -- numRanks 统一
  have hnr : pm_goal_4.numRanks = pm.numRanks := by native_decide
  -- cut 要的 InitGoalsHold (initGoals ++ [goal_2,goal_3]) 在 computed store
  have hInitCut : InitGoalsHold pm_goal_4.numRanks goal_4_cut_initGoals Ssm Spm := by
    rw [hnr]
    intro g hg
    simp only [goal_4_cut_initGoals, goal_4_prereqs, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hinitC g hg
    · simp only [List.mem_cons, List.mem_singleton] at hg
      rcases hg with rfl | rfl | h
      · exact hg2
      · exact hg3
      · exact absurd h (by simp)
  -- cut 要的 StoreShapesHold (computed) sm_goal_4InitEnv / pm_goal_4InitEnv
  -- 从 hg2/hg3 抽出各 shape
  have h564_smsh : (Ssm 564).shape = [1, 8, 32] := by
    have h := hg2.1; simp only [goal_2] at h; exact h
  have h566_smsh : (Ssm 566).shape = [1, 8, 32] := by
    have h := hg3.1; simp only [goal_3] at h; exact h
  -- PM tps shapes: goal_2 给 564, goal_3 给 1089-1092
  have h564_pmsh : (Spm 564).shape = [1, 8, 32] := by
    have h := hg2.2.1; simp only [goal_2, List.map, List.cons.injEq] at h
    exact h.1
  have hpm_tps : ((goal_3.tps.map (fun p => Spm p.tid)).map (fun t => t.shape))
      = goal_3.tpShapes := hg3.2.1
  -- 拆 1089-1092 四个 shape (用 List.cons.injEq 语法重写, 避免 injection 触发 denoteGraph pm whnf)
  have h4 : (Spm 1089).shape = [1,2,32] ∧ (Spm 1090).shape = [1,2,32] ∧
           (Spm 1091).shape = [1,2,32] ∧ (Spm 1092).shape = [1,2,32] := by
    have h := hpm_tps
    simp only [goal_3, List.map, List.cons.injEq, and_true, and_assoc] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1089_pmsh, h1090_pmsh, h1091_pmsh, h1092_pmsh⟩ := h4
  have hSM4 : StoreShapesHold Ssm sm_goal_4InitEnv := by
    intro tid sh hsh
    rw [sm_goal_4InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_4InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h564_smsh
    · exact h566_smsh
  have hPM4 : StoreShapesHold Spm pm_goal_4InitEnv := by
    intro tid sh hsh
    rw [pm_goal_4InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_4InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h564_pmsh
    · exact h1089_pmsh
    · exact h1090_pmsh
    · exact h1091_pmsh
    · exact h1092_pmsh
  -- 应用 cut h, 传 computed store
  have hcut := h Ssm Spm hSM4 hPM4 hInitCut
  -- hcut : 迷你图版结论 (denoteGraph sm_goal_4 Ssm / pm_goal_4 Spm)
  -- 目标 : 完整图版 (denoteGraph sm initSM / pm initPM)
  -- self-frame 桥接
  -- frame 引理 LHS 用 Ssm/Spm 形态 (匹配 set 后的目标); Ssm/Spm defeq denoteGraph sm/pm
  have hsmf : Ssm 567 = denoteGraph sm_goal_4 Ssm 567 := by
    rw [hSsm]; exact sm_frame_567_self initSM
  have hpm1117 : Spm 1117 = denoteGraph pm_goal_4 Spm 1117 := by
    rw [hSpm]; exact pm_frame_1117_self initPM
  have hpm1118 : Spm 1118 = denoteGraph pm_goal_4 Spm 1118 := by
    rw [hSpm]; exact pm_frame_1118_self initPM
  have hpm1119 : Spm 1119 = denoteGraph pm_goal_4 Spm 1119 := by
    rw [hSpm]; exact pm_frame_1119_self initPM
  have hpm1120 : Spm 1120 = denoteGraph pm_goal_4 Spm 1120 := by
    rw [hSpm]; exact pm_frame_1120_self initPM
  -- 把 hcut 的 numRanks (pm_goal_4.numRanks) 统一到 pm.numRanks
  rw [hnr] at hcut
  -- 目标和 hcut 只在 Ssm/sm_goal_4 、Spm/pm_goal_4 上差, 用 frame 改写目标
  simp only [goal_4, List.map] at hcut ⊢
  rw [hsmf, hpm1117, hpm1118, hpm1119, hpm1120]
  exact hcut

-- ========== 导出 goal_4_intermediate (供后续依赖 goal_4 的 goal 复用) ==========
theorem goal_4_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_4 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_4_stmt := goal_4_cut_to_full prove_goal_4_cut
  have := hfull initSM initPM hSM hPM hInit
  simpa [InitGoalHolds, goal_4] using this

end TrainVerify.Denote.GeneratedGoals

