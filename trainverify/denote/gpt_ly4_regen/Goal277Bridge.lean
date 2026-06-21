/- goal_277 桥 (prereqs=[2..30,257,259,261,263,265,267,269,271])。
   FW_multiref 第二输出 (params=[3], outs=[961,965,969] 选 965), 无后续 collective。
   复用 goal_273 第二输出模板, 节点索引同 goal_275 (SM node 33, PM node 201-204)。
   SM=FW_multiref(605)→[961,965,969] (node 33)，取第二输出 965 = 605。
   PM=4×FW_multiref(1665+r)→[35XX,172X,35YY] (node 201-204)，每 rank 取第二输出 = 输入。
   语义: tid 965 复制等于 605, tid 1721-1724 各 rank 等于 1665-1668 (即上游 goal_30 的 ts/4tps)。
   输入 605/1665-1668 来自 goal_30 (FW_layernorm 输出, gatherDim=1)。
   bridge 只做 frame: full sm 算 965 = sm_goal_277 算 965, full pm 算 1721-1724 同理。
   shape 提取用 obtain (规避 simpa 触发的 whnf 整图爆炸, 见 goal_29 教训)。
   multiref3_second_out_g277 lemma 已在 Denote.lean (line 17011) 定义, 与 cut 共用。 -/
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal30Bridge
import denote.gpt_ly4_regen.Goal257Bridge
import denote.gpt_ly4_regen.Goal259Bridge
import denote.gpt_ly4_regen.Goal261Bridge
import denote.gpt_ly4_regen.Goal263Bridge
import denote.gpt_ly4_regen.Goal265Bridge
import denote.gpt_ly4_regen.Goal267Bridge
import denote.gpt_ly4_regen.Goal269Bridge
import denote.gpt_ly4_regen.Goal271Bridge
import denote.gpt_ly4_regen.Goal_277

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
-- Silence noisy cosmetic/convention linters (same rationale as Goal29/271/275Bridge):
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_277 算 965 (FW_multiref params=[3] 第二输出 = s 605) ==========
theorem denote_sm_goal_277_965 (s : Store) :
    denoteGraph sm_goal_277 s 965 = s 605 := by
  simp only [sm_goal_277, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_second_out_g277 _ _ 0 605 961 965 969 (by decide)]

-- ========== 迷你图 pm_goal_277 算 1721-1724 (每 rank 第二输出 = 各 rank 输入) ==========
theorem denote_pm_goal_277_1721 (s : Store) :
    denoteGraph pm_goal_277 s 1721 = s 1665 := by
  simp only [pm_goal_277, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1721 (by decide), applyNode_skip _ _ _ 1721 (by decide),
      applyNode_skip _ _ _ 1721 (by decide),
      applyNode_fw_multiref3_second_out_g277 _ _ 0 1665 3519 1721 3521 (by decide)]

theorem denote_pm_goal_277_1722 (s : Store) :
    denoteGraph pm_goal_277 s 1722 = s 1666 := by
  simp only [pm_goal_277, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1722 (by decide), applyNode_skip _ _ _ 1722 (by decide),
      applyNode_fw_multiref3_second_out_g277 _ _ 1 1666 3529 1722 3531 (by decide),
      applyNode_skip _ _ _ 1666 (by decide)]

theorem denote_pm_goal_277_1723 (s : Store) :
    denoteGraph pm_goal_277 s 1723 = s 1667 := by
  simp only [pm_goal_277, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1723 (by decide),
      applyNode_fw_multiref3_second_out_g277 _ _ 2 1667 3539 1723 3541 (by decide),
      applyNode_skip _ _ _ 1667 (by decide), applyNode_skip _ _ _ 1667 (by decide)]

theorem denote_pm_goal_277_1724 (s : Store) :
    denoteGraph pm_goal_277 s 1724 = s 1668 := by
  simp only [pm_goal_277, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref3_second_out_g277 _ _ 3 1668 3549 1724 3551 (by decide),
      applyNode_skip _ _ _ 1668 (by decide), applyNode_skip _ _ _ 1668 (by decide),
      applyNode_skip _ _ _ 1668 (by decide)]

-- ========== SM self-frame: full sm 算 965 (node 33 FW_multiref 第二输出) ==========
theorem sm_frame_965_self (initSM : Store) :
    denoteGraph sm initSM 965 = denoteGraph sm_goal_277 (denoteGraph sm initSM) 965 := by
  rw [denote_sm_goal_277_965]
  rw [sm_val initSM 33 965 (by native_decide) (by native_decide)]
  rw [show sm.nodes[33]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [605], outs := [961, 965, 969], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g277 _ _ 0 605 961 965 969 (by decide)]
  rw [sm_prefix_eq initSM 33 605 (by native_decide)]

-- ========== full pm: multiref 第二输出 1721 (node 201) = s 1665 ==========
theorem pm_full_1721 (initPM : Store) :
    denoteGraph pm initPM 1721 = denoteGraph pm initPM 1665 := by
  rw [pm_val initPM 201 1721 (by native_decide) (by native_decide)]
  rw [show pm.nodes[201]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1665], outs := [3519, 1721, 3521], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g277 _ _ 0 1665 3519 1721 3521 (by decide)]
  rw [pm_prefix_eq initPM 201 1665 (by native_decide)]

-- ========== full pm: multiref 第二输出 1722 (node 202) = s 1666 ==========
theorem pm_full_1722 (initPM : Store) :
    denoteGraph pm initPM 1722 = denoteGraph pm initPM 1666 := by
  rw [pm_val initPM 202 1722 (by native_decide) (by native_decide)]
  rw [show pm.nodes[202]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1666], outs := [3529, 1722, 3531], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g277 _ _ 1 1666 3529 1722 3531 (by decide)]
  rw [pm_prefix_eq initPM 202 1666 (by native_decide)]

-- ========== full pm: multiref 第二输出 1723 (node 203) = s 1667 ==========
theorem pm_full_1723 (initPM : Store) :
    denoteGraph pm initPM 1723 = denoteGraph pm initPM 1667 := by
  rw [pm_val initPM 203 1723 (by native_decide) (by native_decide)]
  rw [show pm.nodes[203]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1667], outs := [3539, 1723, 3541], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g277 _ _ 2 1667 3539 1723 3541 (by decide)]
  rw [pm_prefix_eq initPM 203 1667 (by native_decide)]

-- ========== full pm: multiref 第二输出 1724 (node 204) = s 1668 ==========
theorem pm_full_1724 (initPM : Store) :
    denoteGraph pm initPM 1724 = denoteGraph pm initPM 1668 := by
  rw [pm_val initPM 204 1724 (by native_decide) (by native_decide)]
  rw [show pm.nodes[204]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1668], outs := [3549, 1724, 3551], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out_g277 _ _ 3 1668 3549 1724 3551 (by decide)]
  rw [pm_prefix_eq initPM 204 1668 (by native_decide)]

theorem pm_frame_1721_self (initPM : Store) :
    denoteGraph pm initPM 1721 = denoteGraph pm_goal_277 (denoteGraph pm initPM) 1721 := by
  rw [denote_pm_goal_277_1721]
  exact pm_full_1721 initPM

theorem pm_frame_1722_self (initPM : Store) :
    denoteGraph pm initPM 1722 = denoteGraph pm_goal_277 (denoteGraph pm initPM) 1722 := by
  rw [denote_pm_goal_277_1722]
  exact pm_full_1722 initPM

theorem pm_frame_1723_self (initPM : Store) :
    denoteGraph pm initPM 1723 = denoteGraph pm_goal_277 (denoteGraph pm initPM) 1723 := by
  rw [denote_pm_goal_277_1723]
  exact pm_full_1723 initPM

theorem pm_frame_1724_self (initPM : Store) :
    denoteGraph pm initPM 1724 = denoteGraph pm_goal_277 (denoteGraph pm initPM) 1724 := by
  rw [denote_pm_goal_277_1724]
  exact pm_full_1724 initPM

-- ========== 总装: goal_277_cut_to_full ==========
theorem goal_277_cut_to_full (h : goal_277_stmt_cut) : goal_277_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hinitC
  have hnr : pm_goal_277.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 605=goal_30.ts [1,8,32]; 1665-1668=goal_30.tps [1,2,32] (obtain 规避 whnf)
  have h605_smsh : (Ssm 605).shape = [1, 8, 32] := by
    have h := hg30.1; simp only [goal_30] at h; exact h
  have h30tp := hg30.2.1
  simp only [goal_30, List.map, List.cons.injEq, and_true] at h30tp
  obtain ⟨h1665_pmsh, h1666_pmsh, h1667_pmsh, h1668_pmsh⟩ := h30tp
  have hSM277 : StoreShapesHold Ssm sm_goal_277InitEnv := by
    intro tid sh hsh
    rw [sm_goal_277InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_277InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h605_smsh
  have hPM277 : StoreShapesHold Spm pm_goal_277InitEnv := by
    intro tid sh hsh
    rw [pm_goal_277InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_277InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1665_pmsh
    · exact h1666_pmsh
    · exact h1667_pmsh
    · exact h1668_pmsh
  have hInitCut : InitGoalsHold pm_goal_277.numRanks goal_277_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_277_cut_initGoals, goal_277_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM277 hPM277 hInitCut
  -- Frame: 965 (sm), 1721-1724 (pm)
  have hsmf : Ssm 965 = denoteGraph sm_goal_277 Ssm 965 := by
    rw [hSsm]; exact sm_frame_965_self initSM
  have hpm1721 : Spm 1721 = denoteGraph pm_goal_277 Spm 1721 := by
    rw [hSpm]; exact pm_frame_1721_self initPM
  have hpm1722 : Spm 1722 = denoteGraph pm_goal_277 Spm 1722 := by
    rw [hSpm]; exact pm_frame_1722_self initPM
  have hpm1723 : Spm 1723 = denoteGraph pm_goal_277 Spm 1723 := by
    rw [hSpm]; exact pm_frame_1723_self initPM
  have hpm1724 : Spm 1724 = denoteGraph pm_goal_277 Spm 1724 := by
    rw [hSpm]; exact pm_frame_1724_self initPM
  rw [hnr] at hcut
  simp only [goal_277, List.map] at hcut ⊢
  rw [hsmf, hpm1721, hpm1722, hpm1723, hpm1724]
  exact hcut

theorem goal_277_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_277 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_277_stmt := goal_277_cut_to_full prove_goal_277_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
