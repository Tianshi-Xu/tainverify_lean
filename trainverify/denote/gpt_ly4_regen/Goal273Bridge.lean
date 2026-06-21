/- goal_273 桥 (prereqs=[2..29,257,259,261,263,265,267,269])。
   第27种结构(复用第24种 FW_multiref 第二输出模板, 同 goal_269)。
   SM=FW_multiref(602)→[946,950] (node 31)，取第二输出 950 = 602。
   PM=4×FW_multiref(1637+r)→[349X, 2049+r] (node 386-389)，每 rank 取第二输出 = 输入。
   语义: tid 950 复制等于 602, tid 2049-2052 各 rank 等于 1637-1640 (即上游 goal_29 的 ts/4tps)。
   输入 602/1637-1640 来自 goal_29 (FW_add 输出, gatherDim=2)。
   bridge 只做 frame: full sm 算 950 = sm_goal_273 算 950, full pm 算 2049-2052 同理。
   shape 提取用 obtain (规避 simpa 触发的 whnf 整图爆炸, 见 goal_29 教训)。 -/
import denote.gpt_ly4_regen.Goal29Bridge
import denote.gpt_ly4_regen.Goal257Bridge
import denote.gpt_ly4_regen.Goal259Bridge
import denote.gpt_ly4_regen.Goal261Bridge
import denote.gpt_ly4_regen.Goal263Bridge
import denote.gpt_ly4_regen.Goal265Bridge
import denote.gpt_ly4_regen.Goal_273

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_273 算 950 (FW_multiref 第二输出 = s 602) ==========
theorem denote_sm_goal_273_950 (s : Store) :
    denoteGraph sm_goal_273 s 950 = s 602 := by
  simp only [sm_goal_273, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_g273]

-- ========== 迷你图 pm_goal_273 算 2049-2052 (每 rank 第二输出 = 各 rank 输入) ==========
theorem denote_pm_goal_273_2049 (s : Store) :
    denoteGraph pm_goal_273 s 2049 = s 1637 := by
  simp only [pm_goal_273, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 2049 (by decide), applyNode_skip _ _ _ 2049 (by decide),
      applyNode_skip _ _ _ 2049 (by decide), applyNode_fw_multiref2_second_out_g273]

theorem denote_pm_goal_273_2050 (s : Store) :
    denoteGraph pm_goal_273 s 2050 = s 1638 := by
  simp only [pm_goal_273, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 2050 (by decide), applyNode_skip _ _ _ 2050 (by decide),
      applyNode_fw_multiref2_second_out_g273, applyNode_skip _ _ _ 1638 (by decide)]

theorem denote_pm_goal_273_2051 (s : Store) :
    denoteGraph pm_goal_273 s 2051 = s 1639 := by
  simp only [pm_goal_273, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 2051 (by decide), applyNode_fw_multiref2_second_out_g273,
      applyNode_skip _ _ _ 1639 (by decide), applyNode_skip _ _ _ 1639 (by decide)]

theorem denote_pm_goal_273_2052 (s : Store) :
    denoteGraph pm_goal_273 s 2052 = s 1640 := by
  simp only [pm_goal_273, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_g273,
      applyNode_skip _ _ _ 1640 (by decide), applyNode_skip _ _ _ 1640 (by decide),
      applyNode_skip _ _ _ 1640 (by decide)]

-- ========== SM self-frame: full sm 算 950 (node 31 FW_multiref 第二输出) ==========
theorem sm_frame_950_self (initSM : Store) :
    denoteGraph sm initSM 950 = denoteGraph sm_goal_273 (denoteGraph sm initSM) 950 := by
  rw [denote_sm_goal_273_950]
  rw [sm_val initSM 31 950 (by native_decide) (by native_decide)]
  rw [show sm.nodes[31]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [602], outs := [946, 950], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g273]
  rw [sm_prefix_eq initSM 31 602 (by native_decide)]

-- ========== full pm: multiref 第二输出 2049 (node 386) = s 1637 ==========
theorem pm_full_2049 (initPM : Store) :
    denoteGraph pm initPM 2049 = denoteGraph pm initPM 1637 := by
  rw [pm_val initPM 189 2049 (by native_decide) (by native_decide)]
  rw [show pm.nodes[189]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1637], outs := [3493, 2049], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g273]
  rw [pm_prefix_eq initPM 189 1637 (by native_decide)]

-- ========== full pm: multiref 第二输出 2050 (node 387) = s 1638 ==========
theorem pm_full_2050 (initPM : Store) :
    denoteGraph pm initPM 2050 = denoteGraph pm initPM 1638 := by
  rw [pm_val initPM 190 2050 (by native_decide) (by native_decide)]
  rw [show pm.nodes[190]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1638], outs := [3499, 2050], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g273]
  rw [pm_prefix_eq initPM 190 1638 (by native_decide)]

-- ========== full pm: multiref 第二输出 2051 (node 388) = s 1639 ==========
theorem pm_full_2051 (initPM : Store) :
    denoteGraph pm initPM 2051 = denoteGraph pm initPM 1639 := by
  rw [pm_val initPM 191 2051 (by native_decide) (by native_decide)]
  rw [show pm.nodes[191]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1639], outs := [3505, 2051], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g273]
  rw [pm_prefix_eq initPM 191 1639 (by native_decide)]

-- ========== full pm: multiref 第二输出 2052 (node 389) = s 1640 ==========
theorem pm_full_2052 (initPM : Store) :
    denoteGraph pm initPM 2052 = denoteGraph pm initPM 1640 := by
  rw [pm_val initPM 192 2052 (by native_decide) (by native_decide)]
  rw [show pm.nodes[192]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1640], outs := [3511, 2052], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g273]
  rw [pm_prefix_eq initPM 192 1640 (by native_decide)]

theorem pm_frame_2049_self (initPM : Store) :
    denoteGraph pm initPM 2049 = denoteGraph pm_goal_273 (denoteGraph pm initPM) 2049 := by
  rw [denote_pm_goal_273_2049]
  exact pm_full_2049 initPM

theorem pm_frame_2050_self (initPM : Store) :
    denoteGraph pm initPM 2050 = denoteGraph pm_goal_273 (denoteGraph pm initPM) 2050 := by
  rw [denote_pm_goal_273_2050]
  exact pm_full_2050 initPM

theorem pm_frame_2051_self (initPM : Store) :
    denoteGraph pm initPM 2051 = denoteGraph pm_goal_273 (denoteGraph pm initPM) 2051 := by
  rw [denote_pm_goal_273_2051]
  exact pm_full_2051 initPM

theorem pm_frame_2052_self (initPM : Store) :
    denoteGraph pm initPM 2052 = denoteGraph pm_goal_273 (denoteGraph pm initPM) 2052 := by
  rw [denote_pm_goal_273_2052]
  exact pm_full_2052 initPM

-- ========== 总装: goal_273_cut_to_full ==========
theorem goal_273_cut_to_full (h : goal_273_stmt_cut) : goal_273_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hinitC
  have hnr : pm_goal_273.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 602=goal_29.ts [1,8,32]; 1637-1640=goal_29.tps [1,8,8] (obtain 规避 whnf)
  have h602_smsh : (Ssm 602).shape = [1, 8, 32] := by
    have h := hg29.1; simp only [goal_29] at h; exact h
  have h29tp := hg29.2.1
  simp only [goal_29, List.map, List.cons.injEq, and_true] at h29tp
  obtain ⟨h1637_pmsh, h1638_pmsh, h1639_pmsh, h1640_pmsh⟩ := h29tp
  have hSM273 : StoreShapesHold Ssm sm_goal_273InitEnv := by
    intro tid sh hsh
    rw [sm_goal_273InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_273InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h602_smsh
  have hPM273 : StoreShapesHold Spm pm_goal_273InitEnv := by
    intro tid sh hsh
    rw [pm_goal_273InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_273InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1637_pmsh
    · exact h1638_pmsh
    · exact h1639_pmsh
    · exact h1640_pmsh
  have hInitCut : InitGoalsHold pm_goal_273.numRanks goal_273_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_273_cut_initGoals, goal_273_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg257, hg259, hg261, hg263, hg265, hg267, hg269, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM273 hPM273 hInitCut
  -- Frame: 950 (sm), 2049-2052 (pm)
  have hsmf : Ssm 950 = denoteGraph sm_goal_273 Ssm 950 := by
    rw [hSsm]; exact sm_frame_950_self initSM
  have hpm2049 : Spm 2049 = denoteGraph pm_goal_273 Spm 2049 := by
    rw [hSpm]; exact pm_frame_2049_self initPM
  have hpm2050 : Spm 2050 = denoteGraph pm_goal_273 Spm 2050 := by
    rw [hSpm]; exact pm_frame_2050_self initPM
  have hpm2051 : Spm 2051 = denoteGraph pm_goal_273 Spm 2051 := by
    rw [hSpm]; exact pm_frame_2051_self initPM
  have hpm2052 : Spm 2052 = denoteGraph pm_goal_273 Spm 2052 := by
    rw [hSpm]; exact pm_frame_2052_self initPM
  rw [hnr] at hcut
  simp only [goal_273, List.map] at hcut ⊢
  rw [hsmf, hpm2049, hpm2050, hpm2051, hpm2052]
  exact hcut

theorem goal_273_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_273 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_273_stmt := goal_273_cut_to_full prove_goal_273_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
