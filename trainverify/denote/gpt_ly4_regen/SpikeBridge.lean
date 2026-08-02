/- 真证 goal_2 桥。SM frame 已通(EXIT 0)。现攻 PM frame。 -/
import denote.gpt_ly4_regen.Goal_2

set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedGoals

open TrainVerify.Denote
open TrainVerify.Denote.Generated

-- 通用齿轮：shapeEnvOfList lookup 成功 → (tid,sh) 是成员
theorem mem_of_shapeEnvOfList_eq_some {xs : List (Tid × Shape)} {tid sh}
    (h : shapeEnvOfList xs tid = some sh) : (tid, sh) ∈ xs := by
  unfold shapeEnvOfList at h
  cases hf : xs.find? (fun p => p.1 = tid) with
  | none => rw [hf] at h; simp at h
  | some pair =>
    rw [hf] at h
    obtain ⟨t, s⟩ := pair
    simp only [Option.some.injEq] at h
    subst h
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [decide_eq_true_eq] at hpred
    subst hpred
    exact hmem

-- 通用弱化引理：small 每条目在 big 里 find? 到自己 → StoreShapesHold 弱化（子集）
theorem storeShapes_weaken {init : Store} {small big : List (Tid × Shape)}
    (hsub : ∀ p ∈ small, shapeEnvOfList big p.1 = some p.2)
    (hbig : StoreShapesHold init (shapeEnvOfList big)) :
    StoreShapesHold init (shapeEnvOfList small) := by
  intro tid sh hsh
  have hmem : (tid, sh) ∈ small := mem_of_shapeEnvOfList_eq_some hsh
  exact hbig tid sh (hsub (tid, sh) hmem)

-- base case: cut init = full init
theorem goal_2_cutinit_eq : goal_2_cut_initGoals = initGoals := by
  unfold goal_2_cut_initGoals; rfl

-- ===== SM frame（已证）=====
theorem sm_goal_2_eq_take : sm_goal_2 = { sm with nodes := sm.nodes.take 1 } := by
  native_decide

theorem sm_frame_564 (initSM : Store) :
    denoteGraph sm initSM 564 = denoteGraph sm_goal_2 initSM 564 := by
  rw [sm_goal_2_eq_take]
  have hsplit : sm.nodes = sm.nodes.take 1 ++ sm.nodes.drop 1 := (List.take_append_drop 1 sm.nodes).symm
  have hno : ∀ n ∈ sm.nodes.drop 1, (564 : Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes sm initSM 564 (sm.nodes.take 1) (sm.nodes.drop 1) hsplit hno]

-- ===== PM frame：第一步 去后缀（pm → 前12节点）=====
theorem pm_frame_564_step1 (initPM : Store) :
    denoteGraph pm initPM 564 = denoteGraph { pm with nodes := pm.nodes.take 12 } initPM 564 := by
  have hsplit : pm.nodes = pm.nodes.take 12 ++ pm.nodes.drop 12 := (List.take_append_drop 12 pm.nodes).symm
  have hno : ∀ n ∈ pm.nodes.drop 12, (564 : Tid) ∉ n.outs := by native_decide
  rw [denoteGraph_tid_eq_of_suffix_no_writes pm initPM 564 (pm.nodes.take 12) (pm.nodes.drop 12) hsplit hno]

-- 第二步：前12节点 → 迷你图5节点。两边都是顺序 foldl，在 564 上展开。
-- 用 denoteGraph_cons_eq 逐节点 unfold + applyNode 读写化简。
theorem pm_frame_564_step2 (initPM : Store) :
    denoteGraph { pm with nodes := pm.nodes.take 12 } initPM 564
      = denoteGraph pm_goal_2 initPM 564 := by
  simp only [pm, pm_goal_2, List.take, denoteGraph, List.foldl]
  -- 两边都变成 foldl applyNode 序列作用在 564 上。applyNode 只改 outs。
  -- 干扰节点写的 tid ≠ 564 且 ≠ 1069-1072，用 storeSet_eq_of_not_mem_fst 跳过。
  rfl

-- 合成 PM frame
theorem pm_frame_564 (initPM : Store) :
    denoteGraph pm initPM 564 = denoteGraph pm_goal_2 initPM 564 := by
  rw [pm_frame_564_step1, pm_frame_564_step2]

-- ===== 最终桥：goal_2_stmt_cut → goal_2_stmt =====
theorem goal_2_cut_to_full (h : goal_2_stmt_cut) : goal_2_stmt := by
  intro initSM initPM hSM hPM hInit
  -- numRanks 相等
  have hnr : pm_goal_2.numRanks = pm.numRanks := by native_decide
  -- 步骤3：InitGoalsHold 转移（cut_initGoals = initGoals，numRanks 相等）
  have hInit' : InitGoalsHold pm_goal_2.numRanks goal_2_cut_initGoals initSM initPM := by
    rw [hnr, goal_2_cutinit_eq]; exact hInit
  -- 步骤1：StoreShapesHold 子集弱化 SM（通用引理 + decide 验证子集）
  have hSM' : StoreShapesHold initSM sm_goal_2InitEnv := by
    rw [sm_goal_2InitEnv]
    exact storeShapes_weaken (by decide) hSM
  -- 步骤2：StoreShapesHold 子集弱化 PM
  have hPM' : StoreShapesHold initPM pm_goal_2InitEnv := by
    rw [pm_goal_2InitEnv]
    exact storeShapes_weaken (by decide) hPM
  -- 步骤3：应用 cut h 得迷你图结论
  have hcut := h initSM initPM hSM' hPM' hInit'
  -- 步骤4：迷你图→完整图。goal_2.ts=564, goal_2.tps=[{tid:=564}]。
  -- hcut 用 sm_goal_2/pm_goal_2，目标用 sm/pm，只在 564 上差，用 frame 改写。
  -- 先把 numRanks 统一
  rw [← hnr]
  -- 把 goal 里的 denoteGraph sm/pm 在相关 tid 上换成迷你图
  show (denoteGraph sm initSM goal_2.ts).shape = _ ∧
    _ = _ ∧
    denoteGraph sm initSM goal_2.ts = reconstructForGoal goal_2 pm_goal_2.numRanks _
  simp only [goal_2, List.map, sm_frame_564 initSM, pm_frame_564 initPM]
  simp only [goal_2, List.map] at hcut
  exact hcut

end TrainVerify.Denote.GeneratedGoals
