/- goal_3 桥 (AllGather base case)。验证 goal_2 模板通用性。复用 SpikeBridge 通用引理。 -/
import denote.gpt_ly4_regen.SpikeBridge
import denote.gpt_ly4_regen.Goal_3

set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- base case: cut init = full init
theorem goal_3_cutinit_eq : goal_3_cut_initGoals = initGoals := by
  unfold goal_3_cut_initGoals; rfl

-- ===== SM frame：566 在完整 sm 第1个节点(index1)，sm_goal_3 = [sm.nodes[1]] =====
-- 迷你图不是前缀（566 在 index1，不是 index0），需跳过 node0。
-- node0 写 564，ins[714,563]，不碰 716/565 → 对 566 计算无影响。

-- 辅助：单节点迷你图在 566 上 = fw_embedding(s 716)(s 565)
theorem denote_sm_goal_3_566 (s : Store) :
    denoteGraph sm_goal_3 s 566 = fw_embedding (s 716) (s 565) := by
  simp only [sm_goal_3, denoteGraph, List.foldl]
  rw [applyNode_fw_embedding_out]

theorem sm_frame_566 (initSM : Store) :
    denoteGraph sm initSM 566 = denoteGraph sm_goal_3 initSM 566 := by
  -- 1) 去后缀：sm → 前2节点
  have hsplit : sm.nodes = sm.nodes.take 2 ++ sm.nodes.drop 2 :=
    (List.take_append_drop 2 sm.nodes).symm
  have hno : ∀ n ∈ sm.nodes.drop 2, (566 : Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes sm initSM 566 (sm.nodes.take 2) (sm.nodes.drop 2) hsplit hno]
  -- 2) take 2 = take 1 ++ (drop 1).take 1，拆开为 node0 ++ node1
  have htake2 : ({ sm with nodes := sm.nodes.take 2 } : GraphDecl)
      = { sm with nodes := sm.nodes.take 1 ++ (sm.nodes.drop 1).take 1 } := by native_decide
  rw [htake2, denoteGraph_nodes_append]
  -- 3) sm_goal_3 = {sm with nodes := (drop1).take1}，两边都用该迷你图在 s0/initSM 上
  have hsg3 : ({ sm with nodes := (sm.nodes.drop 1).take 1 } : GraphDecl) = sm_goal_3 := by
    native_decide
  rw [hsg3]
  -- s0 = node0 作用后的 store；在 716/565 上与 initSM 相同
  set s0 := denoteGraph { sm with nodes := sm.nodes.take 1 } initSM with hs0
  have h716 : s0 716 = initSM 716 := by
    rw [hs0]; apply denoteGraph_tid_eq_of_forall_not_mem_outs; native_decide
  have h565 : s0 565 = initSM 565 := by
    rw [hs0]; apply denoteGraph_tid_eq_of_forall_not_mem_outs; native_decide
  -- 4) 两边展开为 fw_embedding
  rw [denote_sm_goal_3_566, denote_sm_goal_3_566, h716, h565]

-- ===== PM frame：1089-1092 各是 embedding 输出（无 collective）=====
-- 迷你图 pm_goal_3 在 1089 上 = fw_embedding(chunk_0(initPM 716))(initPM 565)
-- 完整 pm 同样（1085=chunk_0(716) 在 index1，1089=embedding 在 index8）

-- 先证迷你图侧 1089（复用 cut 证明的 hpm0 结构）
theorem denote_pm_goal_3_mini_1089 (initPM : Store) :
    denoteGraph pm_goal_3 initPM 1089 =
      fw_embedding (chunkPrimDimN 1 4 0 (initPM 716)) (initPM 565) := by
  simp only [pm_goal_3, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

-- 完整 pm 侧 1089：去后缀(drop 9 不写 1089) + 前9节点 foldl 展开
theorem denote_pm_full_1089 (initPM : Store) :
    denoteGraph pm initPM 1089 =
      fw_embedding (chunkPrimDimN 1 4 0 (initPM 716)) (initPM 565) := by
  have hsplit : pm.nodes = pm.nodes.take 9 ++ pm.nodes.drop 9 :=
    (List.take_append_drop 9 pm.nodes).symm
  have hno : ∀ n ∈ pm.nodes.drop 9, (1089 : Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1089 (pm.nodes.take 9) (pm.nodes.drop 9) hsplit hno]
  simp only [pm, List.take, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

theorem pm_frame_1089 (initPM : Store) :
    denoteGraph pm initPM 1089 = denoteGraph pm_goal_3 initPM 1089 := by
  rw [denote_pm_full_1089, denote_pm_goal_3_mini_1089]

-- 1090: writer index 9, chunk rank 1
theorem denote_pm_goal_3_mini_1090 (initPM : Store) :
    denoteGraph pm_goal_3 initPM 1090 =
      fw_embedding (chunkPrimDimN 1 4 1 (initPM 716)) (initPM 565) := by
  simp only [pm_goal_3, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

theorem denote_pm_full_1090 (initPM : Store) :
    denoteGraph pm initPM 1090 =
      fw_embedding (chunkPrimDimN 1 4 1 (initPM 716)) (initPM 565) := by
  have hsplit : pm.nodes = pm.nodes.take 10 ++ pm.nodes.drop 10 :=
    (List.take_append_drop 10 pm.nodes).symm
  have hno : ∀ n ∈ pm.nodes.drop 10, (1090 : Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1090 (pm.nodes.take 10) (pm.nodes.drop 10) hsplit hno]
  simp only [pm, List.take, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

theorem pm_frame_1090 (initPM : Store) :
    denoteGraph pm initPM 1090 = denoteGraph pm_goal_3 initPM 1090 := by
  rw [denote_pm_full_1090, denote_pm_goal_3_mini_1090]

-- 1091: writer index 10, chunk rank 2
theorem denote_pm_goal_3_mini_1091 (initPM : Store) :
    denoteGraph pm_goal_3 initPM 1091 =
      fw_embedding (chunkPrimDimN 1 4 2 (initPM 716)) (initPM 565) := by
  simp only [pm_goal_3, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

theorem denote_pm_full_1091 (initPM : Store) :
    denoteGraph pm initPM 1091 =
      fw_embedding (chunkPrimDimN 1 4 2 (initPM 716)) (initPM 565) := by
  have hsplit : pm.nodes = pm.nodes.take 11 ++ pm.nodes.drop 11 :=
    (List.take_append_drop 11 pm.nodes).symm
  have hno : ∀ n ∈ pm.nodes.drop 11, (1091 : Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1091 (pm.nodes.take 11) (pm.nodes.drop 11) hsplit hno]
  simp only [pm, List.take, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

theorem pm_frame_1091 (initPM : Store) :
    denoteGraph pm initPM 1091 = denoteGraph pm_goal_3 initPM 1091 := by
  rw [denote_pm_full_1091, denote_pm_goal_3_mini_1091]

-- 1092: writer index 12, chunk rank 3
theorem denote_pm_goal_3_mini_1092 (initPM : Store) :
    denoteGraph pm_goal_3 initPM 1092 =
      fw_embedding (chunkPrimDimN 1 4 3 (initPM 716)) (initPM 565) := by
  simp only [pm_goal_3, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

theorem denote_pm_full_1092 (initPM : Store) :
    denoteGraph pm initPM 1092 =
      fw_embedding (chunkPrimDimN 1 4 3 (initPM 716)) (initPM 565) := by
  have hsplit : pm.nodes = pm.nodes.take 13 ++ pm.nodes.drop 13 :=
    (List.take_append_drop 13 pm.nodes).symm
  have hno : ∀ n ∈ pm.nodes.drop 13, (1092 : Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1092 (pm.nodes.take 13) (pm.nodes.drop 13) hsplit hno]
  simp only [pm, List.take, denoteGraph, GraphDecl.nodes, List.foldl]
  repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]
  rw [applyNode_fw_embedding_out]
  congr 1

theorem pm_frame_1092 (initPM : Store) :
    denoteGraph pm initPM 1092 = denoteGraph pm_goal_3 initPM 1092 := by
  rw [denote_pm_full_1092, denote_pm_goal_3_mini_1092]

-- ===== 最终桥：goal_3_stmt_cut → goal_3_stmt =====
theorem goal_3_cut_to_full (h : goal_3_stmt_cut) : goal_3_stmt := by
  intro initSM initPM hSM hPM hInit
  have hnr : pm_goal_3.numRanks = pm.numRanks := by native_decide
  -- InitGoalsHold 转移 (base case: cut_initGoals = initGoals)
  have hInit' : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM := by
    rw [hnr, goal_3_cutinit_eq]; exact hInit
  -- StoreShapesHold 子集弱化
  have hSM' : StoreShapesHold initSM sm_goal_3InitEnv := by
    rw [sm_goal_3InitEnv]; exact storeShapes_weaken (by decide) hSM
  have hPM' : StoreShapesHold initPM pm_goal_3InitEnv := by
    rw [pm_goal_3InitEnv]; exact storeShapes_weaken (by decide) hPM
  -- 应用 cut h
  have hcut := h initSM initPM hSM' hPM' hInit'
  -- 迷你图→完整图。统一 numRanks + 4 个 PM frame + 1 个 SM frame
  rw [← hnr]
  simp only [goal_3, List.map,
    sm_frame_566 initSM, pm_frame_1089 initPM, pm_frame_1090 initPM,
    pm_frame_1091 initPM, pm_frame_1092 initPM]
  simp only [goal_3, List.map] at hcut
  exact hcut

end TrainVerify.Denote.GeneratedGoals
