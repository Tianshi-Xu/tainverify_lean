/- goal_269 桥 (prereqs=[2..24,257,259,261,263,265])。
   第24种结构: FW_multiref 第二输出 (params=[2], outs=[934,938] 选 938)。无后续 collective。
   SM=FW_multiref(593)→[934,938] (node 25)，取第二输出 938 = 593。
   PM=4×FW_multiref(1505+r)→[3469+6r, 1629+r] (node 152-155)，每 rank 取第二输出 = 输入。
   语义: tid 938 复制等于 593, tid 1629-1632 各 rank 等于 1505-1508 (即上游 goal_24 的 4 个 tp)。
   reconstruct dim 2 (gatherDim=2) 与 goal_24 的输出一致 (复用 goal_24 prereq)。
   cut 证明 prove_goal_269_cut 已用 applyNode_fw_multiref2_second_out_g269 + applyNode_skip 处理,
   bridge 只做 frame: full sm 算 938 = sm_goal_269 算 938, full pm 算 1629-1632 同理。 -/
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal257Bridge
import denote.gpt_ly4_regen.Goal259Bridge
import denote.gpt_ly4_regen.Goal261Bridge
import denote.gpt_ly4_regen.Goal263Bridge
import denote.gpt_ly4_regen.Goal265Bridge
import denote.gpt_ly4_regen.Goal_269

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_269 算 938 (FW_multiref 第二输出 = s 593) ==========
theorem denote_sm_goal_269_938 (s : Store) :
    denoteGraph sm_goal_269 s 938 = s 593 := by
  simp only [sm_goal_269, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_g269 _ _ _ 593 934 938 (by decide)]

-- ========== 迷你图 pm_goal_269 算 1629-1632 (每 rank 第二输出 = 各 rank 输入) ==========
theorem denote_pm_goal_269_1629 (s : Store) :
    denoteGraph pm_goal_269 s 1629 = s 1505 := by
  simp only [pm_goal_269, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1629 (by decide),
      applyNode_skip _ _ _ 1629 (by decide),
      applyNode_skip _ _ _ 1629 (by decide),
      applyNode_fw_multiref2_second_out_g269 _ _ _ 1505 3469 1629 (by decide)]

theorem denote_pm_goal_269_1630 (s : Store) :
    denoteGraph pm_goal_269 s 1630 = s 1506 := by
  simp only [pm_goal_269, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1630 (by decide),
      applyNode_skip _ _ _ 1630 (by decide),
      applyNode_fw_multiref2_second_out_g269 _ _ _ 1506 3475 1630 (by decide),
      applyNode_skip _ _ _ 1506 (by decide)]

theorem denote_pm_goal_269_1631 (s : Store) :
    denoteGraph pm_goal_269 s 1631 = s 1507 := by
  simp only [pm_goal_269, denoteGraph, List.foldl]
  rw [applyNode_skip _ _ _ 1631 (by decide),
      applyNode_fw_multiref2_second_out_g269 _ _ _ 1507 3481 1631 (by decide),
      applyNode_skip _ _ _ 1507 (by decide),
      applyNode_skip _ _ _ 1507 (by decide)]

theorem denote_pm_goal_269_1632 (s : Store) :
    denoteGraph pm_goal_269 s 1632 = s 1508 := by
  simp only [pm_goal_269, denoteGraph, List.foldl]
  rw [applyNode_fw_multiref2_second_out_g269 _ _ _ 1508 3487 1632 (by decide),
      applyNode_skip _ _ _ 1508 (by decide),
      applyNode_skip _ _ _ 1508 (by decide),
      applyNode_skip _ _ _ 1508 (by decide)]

-- ========== SM self-frame: full sm 算 938 (node 25 FW_multiref 第二输出) ==========
theorem sm_frame_938_self (initSM : Store) :
    denoteGraph sm initSM 938 = denoteGraph sm_goal_269 (denoteGraph sm initSM) 938 := by
  rw [denote_sm_goal_269_938]
  rw [sm_val initSM 25 938 (by native_decide) (by native_decide)]
  rw [show sm.nodes[25]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [593], outs := [934, 938], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g269 _ _ _ 593 934 938 (by decide)]
  rw [sm_prefix_eq initSM 25 593 (by native_decide)]

-- ========== full pm: multiref 第二输出 1629 (node 152) = s 1505 ==========
theorem pm_full_1629 (initPM : Store) :
    denoteGraph pm initPM 1629 = denoteGraph pm initPM 1505 := by
  rw [pm_val initPM 152 1629 (by native_decide) (by native_decide)]
  rw [show pm.nodes[152]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [1505], outs := [3469, 1629], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g269 _ _ _ 1505 3469 1629 (by decide)]
  rw [pm_prefix_eq initPM 152 1505 (by native_decide)]

-- ========== full pm: multiref 第二输出 1630 (node 153) = s 1506 ==========
theorem pm_full_1630 (initPM : Store) :
    denoteGraph pm initPM 1630 = denoteGraph pm initPM 1506 := by
  rw [pm_val initPM 153 1630 (by native_decide) (by native_decide)]
  rw [show pm.nodes[153]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [1506], outs := [3475, 1630], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g269 _ _ _ 1506 3475 1630 (by decide)]
  rw [pm_prefix_eq initPM 153 1506 (by native_decide)]

-- ========== full pm: multiref 第二输出 1631 (node 154) = s 1507 ==========
theorem pm_full_1631 (initPM : Store) :
    denoteGraph pm initPM 1631 = denoteGraph pm initPM 1507 := by
  rw [pm_val initPM 154 1631 (by native_decide) (by native_decide)]
  rw [show pm.nodes[154]'(by native_decide)
      = { rank := 2, op := "OpName.FW_multiref", ins := [1507], outs := [3481, 1631], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g269 _ _ _ 1507 3481 1631 (by decide)]
  rw [pm_prefix_eq initPM 154 1507 (by native_decide)]

-- ========== full pm: multiref 第二输出 1632 (node 155) = s 1508 ==========
theorem pm_full_1632 (initPM : Store) :
    denoteGraph pm initPM 1632 = denoteGraph pm initPM 1508 := by
  rw [pm_val initPM 155 1632 (by native_decide) (by native_decide)]
  rw [show pm.nodes[155]'(by native_decide)
      = { rank := 3, op := "OpName.FW_multiref", ins := [1508], outs := [3487, 1632], params := [2] }
      from by native_decide]
  rw [applyNode_fw_multiref2_second_out_g269 _ _ _ 1508 3487 1632 (by decide)]
  rw [pm_prefix_eq initPM 155 1508 (by native_decide)]

theorem pm_frame_1629_self (initPM : Store) :
    denoteGraph pm initPM 1629 = denoteGraph pm_goal_269 (denoteGraph pm initPM) 1629 := by
  rw [denote_pm_goal_269_1629]
  exact pm_full_1629 initPM

theorem pm_frame_1630_self (initPM : Store) :
    denoteGraph pm initPM 1630 = denoteGraph pm_goal_269 (denoteGraph pm initPM) 1630 := by
  rw [denote_pm_goal_269_1630]
  exact pm_full_1630 initPM

theorem pm_frame_1631_self (initPM : Store) :
    denoteGraph pm initPM 1631 = denoteGraph pm_goal_269 (denoteGraph pm initPM) 1631 := by
  rw [denote_pm_goal_269_1631]
  exact pm_full_1631 initPM

theorem pm_frame_1632_self (initPM : Store) :
    denoteGraph pm initPM 1632 = denoteGraph pm_goal_269 (denoteGraph pm initPM) 1632 := by
  rw [denote_pm_goal_269_1632]
  exact pm_full_1632 initPM

-- ========== 总装: goal_269_cut_to_full ==========
theorem goal_269_cut_to_full (h : goal_269_stmt_cut) : goal_269_stmt := by
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
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg257 hg259 hg261 hg263 hg265 hinitC
  have hnr : pm_goal_269.numRanks = pm.numRanks := by native_decide
  -- shape 弱化: 593=goal_24.ts [1,8,32]; 1505-1508=goal_24.tps [1,8,8]
  have h593_smsh : (Ssm 593).shape = [1, 8, 32] := by
    have h := hg24.1; simp only [goal_24] at h; exact h
  have h24tp := hg24.2.1
  simp only [goal_24, List.map] at h24tp
  have h1505_pmsh : (Spm 1505).shape = [1, 8, 8] := by
    have := congrArg List.head? h24tp; simpa using this
  have h1506_pmsh : (Spm 1506).shape = [1, 8, 8] := by
    have := congrArg List.tail h24tp
    have := congrArg List.head? this; simpa using this
  have h1507_pmsh : (Spm 1507).shape = [1, 8, 8] := by
    have := congrArg (List.tail ∘ List.tail) h24tp
    have := congrArg List.head? this; simpa using this
  have h1508_pmsh : (Spm 1508).shape = [1, 8, 8] := by
    have := congrArg (List.tail ∘ List.tail ∘ List.tail) h24tp
    have := congrArg List.head? this; simpa using this
  have hSM269 : StoreShapesHold Ssm sm_goal_269InitEnv := by
    intro tid sh hsh
    rw [sm_goal_269InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_269InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact h593_smsh
  have hPM269 : StoreShapesHold Spm pm_goal_269InitEnv := by
    intro tid sh hsh
    rw [pm_goal_269InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_269InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1505_pmsh
    · exact h1506_pmsh
    · exact h1507_pmsh
    · exact h1508_pmsh
  have hInitCut : InitGoalsHold pm_goal_269.numRanks goal_269_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_269_cut_initGoals, goal_269_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg257, hg259, hg261, hg263, hg265, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM269 hPM269 hInitCut
  -- Frame: 938 (sm), 1629-1632 (pm)
  have hsmf : Ssm 938 = denoteGraph sm_goal_269 Ssm 938 := by
    rw [hSsm]; exact sm_frame_938_self initSM
  have hpm1629 : Spm 1629 = denoteGraph pm_goal_269 Spm 1629 := by
    rw [hSpm]; exact pm_frame_1629_self initPM
  have hpm1630 : Spm 1630 = denoteGraph pm_goal_269 Spm 1630 := by
    rw [hSpm]; exact pm_frame_1630_self initPM
  have hpm1631 : Spm 1631 = denoteGraph pm_goal_269 Spm 1631 := by
    rw [hSpm]; exact pm_frame_1631_self initPM
  have hpm1632 : Spm 1632 = denoteGraph pm_goal_269 Spm 1632 := by
    rw [hSpm]; exact pm_frame_1632_self initPM
  rw [hnr] at hcut
  simp only [goal_269, List.map] at hcut ⊢
  rw [hsmf, hpm1629, hpm1630, hpm1631, hpm1632]
  exact hcut

theorem goal_269_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_269 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_269_stmt := goal_269_cut_to_full prove_goal_269_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
