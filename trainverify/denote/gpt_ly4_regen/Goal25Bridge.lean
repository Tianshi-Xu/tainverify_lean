/- goal_25 桥 (prereqs=[2..24,257,259,261,263,265,267])。
   第20种结构: FW_layernorm (单 tp 输出) over X(934 sharded dim1) + replicated W(594)/B(595)。
   SM=FW_layernorm(934,594,595)→596 (node 26, [1,8,32], 单算子无 AllGather)。
   PM=4×FW_layernorm(152X,594,595)→1529-1532 (node 160-163, 各 [1,2,32]),
      AllGatherPrim((range4).map(1529+),dim=1)→596 (node 164, 单 tp)。
   934=goal_267 输出 [1,8,32] (gather dim1 of 1525-1528); 1525-1528=goal_267 tps [1,2,32];
   594/595 来自 initGoal_594/595 (replicated)。
   语义 (layernorm distributes over gather dim1, fw_layernorm_distribute_allGatherPrimDimN_dim1_4_1_2_32)
   已在 prove_goal_25_cut 里处理。bridge 只做 frame: SM node 26; PM node 160-164 (AllGather tail)。
   套 Goal24Bridge (SM 单 op frame) + Goal21Bridge (PM AllGather→单tp tail) 混合模板。 -/
import denote.gpt_ly4_regen.Goal21Bridge
import denote.gpt_ly4_regen.Goal22Bridge
import denote.gpt_ly4_regen.Goal23Bridge
import denote.gpt_ly4_regen.Goal24Bridge
import denote.gpt_ly4_regen.Goal267Bridge
import denote.gpt_ly4_regen.Goal_25

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_25 算 596 (FW_layernorm) ==========
theorem denote_sm_goal_25_596 (s : Store) :
    denoteGraph sm_goal_25 s 596 = fw_layernorm (s 934) (s 594) (s 595) := by
  simp only [sm_goal_25, denoteGraph, List.foldl]
  rw [applyNode_fw_layernorm_out]

-- ========== SM self-frame: full sm 算 596 (node 26 FW_layernorm) ==========
theorem sm_frame_596_self (initSM : Store) :
    denoteGraph sm initSM 596 = denoteGraph sm_goal_25 (denoteGraph sm initSM) 596 := by
  rw [denote_sm_goal_25_596]
  rw [sm_val initSM 26 596 (by native_decide) (by native_decide)]
  rw [show sm.nodes[26]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [934, 594, 595], outs := [596] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [sm_prefix_eq initSM 26 934 (by native_decide),
      sm_prefix_eq initSM 26 594 (by native_decide),
      sm_prefix_eq initSM 26 595 (by native_decide)]

-- ========== full pm: FW_layernorm 输出 1529-1532 (node 160-163) ==========
theorem pm_full_g25_1529 (initPM : Store) :
    denoteGraph pm initPM 1529
      = fw_layernorm (denoteGraph pm initPM 1525) (denoteGraph pm initPM 594)
          (denoteGraph pm initPM 595) := by
  rw [pm_val initPM 160 1529 (by native_decide) (by native_decide)]
  rw [show pm.nodes[160]'(by native_decide)
      = { rank := 0, op := "OpName.FW_layernorm", ins := [1525, 594, 595], outs := [1529] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 160 1525 (by native_decide),
      pm_prefix_eq initPM 160 594 (by native_decide),
      pm_prefix_eq initPM 160 595 (by native_decide)]

theorem pm_full_g25_1530 (initPM : Store) :
    denoteGraph pm initPM 1530
      = fw_layernorm (denoteGraph pm initPM 1526) (denoteGraph pm initPM 594)
          (denoteGraph pm initPM 595) := by
  rw [pm_val initPM 161 1530 (by native_decide) (by native_decide)]
  rw [show pm.nodes[161]'(by native_decide)
      = { rank := 1, op := "OpName.FW_layernorm", ins := [1526, 594, 595], outs := [1530] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 161 1526 (by native_decide),
      pm_prefix_eq initPM 161 594 (by native_decide),
      pm_prefix_eq initPM 161 595 (by native_decide)]

theorem pm_full_g25_1531 (initPM : Store) :
    denoteGraph pm initPM 1531
      = fw_layernorm (denoteGraph pm initPM 1527) (denoteGraph pm initPM 594)
          (denoteGraph pm initPM 595) := by
  rw [pm_val initPM 162 1531 (by native_decide) (by native_decide)]
  rw [show pm.nodes[162]'(by native_decide)
      = { rank := 2, op := "OpName.FW_layernorm", ins := [1527, 594, 595], outs := [1531] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 162 1527 (by native_decide),
      pm_prefix_eq initPM 162 594 (by native_decide),
      pm_prefix_eq initPM 162 595 (by native_decide)]

theorem pm_full_g25_1532 (initPM : Store) :
    denoteGraph pm initPM 1532
      = fw_layernorm (denoteGraph pm initPM 1528) (denoteGraph pm initPM 594)
          (denoteGraph pm initPM 595) := by
  rw [pm_val initPM 163 1532 (by native_decide) (by native_decide)]
  rw [show pm.nodes[163]'(by native_decide)
      = { rank := 3, op := "OpName.FW_layernorm", ins := [1528, 594, 595], outs := [1532] }
      from by native_decide]
  rw [applyNode_fw_layernorm_out]
  rw [pm_prefix_eq initPM 163 1528 (by native_decide),
      pm_prefix_eq initPM 163 594 (by native_decide),
      pm_prefix_eq initPM 163 595 (by native_decide)]

-- ========== PM self-frame: 596 (AllGather node 164, 单 tp) ==========
theorem pm_frame_596_self (initPM : Store) :
    denoteGraph pm initPM 596
      = allGatherPrimDimN 1 4 0
          [fw_layernorm (denoteGraph pm initPM 1525) (denoteGraph pm initPM 594)
              (denoteGraph pm initPM 595),
           fw_layernorm (denoteGraph pm initPM 1526) (denoteGraph pm initPM 594)
              (denoteGraph pm initPM 595),
           fw_layernorm (denoteGraph pm initPM 1527) (denoteGraph pm initPM 594)
              (denoteGraph pm initPM 595),
           fw_layernorm (denoteGraph pm initPM 1528) (denoteGraph pm initPM 594)
              (denoteGraph pm initPM 595)] := by
  rw [pm_val initPM 164 596 (by native_decide) (by native_decide)]
  rw [show pm.nodes[164]'(by native_decide)
      = { rank := 0, op := "OpName.AllGatherPrim",
          ins := ((List.range 4).map (fun r => 1529 + r)), outs := [596], params := [1] }
      from by native_decide]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 164 1529 (by native_decide),
      pm_prefix_eq initPM 164 1530 (by native_decide),
      pm_prefix_eq initPM 164 1531 (by native_decide),
      pm_prefix_eq initPM 164 1532 (by native_decide)]
  rw [pm_full_g25_1529, pm_full_g25_1530, pm_full_g25_1531, pm_full_g25_1532]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 迷你图 pm_goal_25 算 596 ==========
theorem denote_pm_goal_25_596 (s : Store) :
    denoteGraph pm_goal_25 s 596 = allGatherPrimDimN 1 4 0
      [fw_layernorm (s 1525) (s 594) (s 595),
       fw_layernorm (s 1526) (s 594) (s 595),
       fw_layernorm (s 1527) (s 594) (s 595),
       fw_layernorm (s 1528) (s 594) (s 595)] := by
  simp only [pm_goal_25, denoteGraph, GraphDecl.nodes, List.foldl]
  rw [applyNode_allGatherPrimDimN_out_thm]
  simp only [List.map]
  repeat rw [applyNode_fw_layernorm_out]
  congr 1 <;>
    · repeat rw [applyNode_eq_of_not_mem_outs (h := by decide)]

-- ========== 总装: goal_25_cut_to_full ==========
theorem goal_25_cut_to_full (h : goal_25_stmt_cut) : goal_25_stmt := by
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
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg257 hg259 hg261 hg263 hg265 hg267 hinitC
  have hnr : pm_goal_25.numRanks = pm.numRanks := by native_decide
  -- 934=goal_267.ts [1,8,32] (gathered dim1); 1525-1528=goal_267.tps [1,2,32].
  have h934_smsh : (Ssm 934).shape = [1, 8, 32] := by
    have h := hg267.1; simp only [goal_267] at h; exact h
  have h267tp := hg267.2.1
  simp only [goal_267, List.map] at h267tp
  have h1525_pmsh : (Spm 1525).shape = [1, 2, 32] := by
    have := congrArg List.head? h267tp; simpa using this
  have h1526_pmsh : (Spm 1526).shape = [1, 2, 32] := by
    have := congrArg List.tail h267tp
    have := congrArg List.head? this; simpa using this
  have h1527_pmsh : (Spm 1527).shape = [1, 2, 32] := by
    have := congrArg (List.tail ∘ List.tail) h267tp
    have := congrArg List.head? this; simpa using this
  have h1528_pmsh : (Spm 1528).shape = [1, 2, 32] := by
    have := congrArg (List.tail ∘ List.tail ∘ List.tail) h267tp
    have := congrArg List.head? this; simpa using this
  -- 594/595 = replicated init weight/bias [32], 从 hinitC 抽 (Ssm=Spm on these tids)
  have h594_full := hinitC initGoal_594 (by simp only [initGoals]; decide)
  have h595_full := hinitC initGoal_595 (by simp only [initGoals]; decide)
  have h594_smsh : (Ssm 594).shape = [32] := by
    have h := h594_full.1; simp only [initGoal_594] at h; exact h
  have h595_smsh : (Ssm 595).shape = [32] := by
    have h := h595_full.1; simp only [initGoal_595] at h; exact h
  have hSM25 : StoreShapesHold Ssm sm_goal_25InitEnv := by
    intro tid sh hsh
    rw [sm_goal_25InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_25InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    -- sm_goal_25InitShapes = [(594,[32]),(595,[32]),(934,[1,8,32])]
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h594_smsh
    · exact h595_smsh
    · exact h934_smsh
  -- PM weight/bias 594/595 (replicated, same tid): shape = SM shape via reconstructWithDim_singleton
  have h594_pmsh : (Spm 594).shape = [32] := by
    have h := h594_full.2.2
    simp only [initGoal_594, List.map] at h
    first | rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h | skip
    rw [reconstructWithDim_singleton] at h
    -- h : Ssm 594 = Spm 594  (opaque forms); goal already (Spm 594).shape
    rw [← h]; exact h594_smsh
  have h595_pmsh : (Spm 595).shape = [32] := by
    have h := h595_full.2.2
    simp only [initGoal_595, List.map] at h
    first | rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h | skip
    rw [reconstructWithDim_singleton] at h
    rw [← h]; exact h595_smsh
  have hPM25 : StoreShapesHold Spm pm_goal_25InitEnv := by
    intro tid sh hsh
    rw [pm_goal_25InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_25InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    -- pm_goal_25InitShapes = [(594,[32]),(595,[32]),(1525,[1,2,32]),(1526,..),(1527,..),(1528,..)]
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h594_pmsh
    · exact h595_pmsh
    · exact h1525_pmsh
    · exact h1526_pmsh
    · exact h1527_pmsh
    · exact h1528_pmsh
  have hInitCut : InitGoalsHold pm_goal_25.numRanks goal_25_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_25_cut_initGoals, goal_25_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg257, hg259, hg261, hg263, hg265, hg267, List.forall_mem_nil _⟩
  have hcut := h Ssm Spm hSM25 hPM25 hInitCut
  -- Frame: 596 (sm) 与 596 (pm) 对齐到 mini-graph
  have hsmf : Ssm 596 = denoteGraph sm_goal_25 Ssm 596 := by
    rw [hSsm]; exact sm_frame_596_self initSM
  have hpmf : Spm 596 = denoteGraph pm_goal_25 Spm 596 := by
    rw [denote_pm_goal_25_596]
    rw [hSpm]
    exact pm_frame_596_self initPM
  rw [hnr] at hcut
  simp only [goal_25, List.map] at hcut ⊢
  rw [hsmf, hpmf]
  exact hcut

theorem goal_25_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_25 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_25_stmt := goal_25_cut_to_full prove_goal_25_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals
