/- goal_44 桥 (prereqs 53 个: goal_2..goal_43 + 257,259,261,263,265,267,269,271,275,277,279)。
   结构: fw_matmul over two AllToAll reshards + AllReducePrim (contraction-dim split, single-tp 输出)。
   SM=FW_matmul(621,617)→622 (sm node 47, [1,4,8,8]×[1,4,8,8]→[1,4,8,8])。
     621=goal_43 输出 (dim2-gather, tps 1929-1932 各 [1,4,2,8]);
     617=goal_39 输出 (dim3-gather, tps 1829-1832 各 [1,4,8,2])。
   PM: x-reshard 4×AllToAll(ins=range(1929..1932), params=[2,3])→1945-1948 (pm node 300-303);
       y-reshard 4×AllToAll(ins=range(1829..1832), params=[3,2])→1949-1952 (pm node 276-279, 非相邻!);
       matmul 4×FW_matmul(1945+r,1949+r)→1953-1956 (pm node 304-307);
       AllReducePrim((range4).map(1953+r))→622 (pm node 308)。
   single-tp 输出 (goal_44.tps=[{0,622}], ts==tid)。
   套 Goal33Bridge 模板 (4×per-rank-op → AllReduce → single output, computed-range ins),
   加 Goal41Bridge 的 AllToAll-reshard 层 (pm_full AllToAll x/y)。
   注: matmul-split-dimK + AllReduce 语义在 prove_goal_44_cut 里已处理
   (fw_matmul_split_dimK_1_4_8_8); bridge 只做 frame。 -/
import denote.gpt_ly4_regen.Goal39Bridge
import denote.gpt_ly4_regen.Goal43Bridge
import denote.gpt_ly4_regen.Goal_44

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.flexible false

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

-- ========== 迷你图 sm_goal_44 算 622 (FW_matmul) ==========
theorem denote_sm_goal_44_622 (s : Store) :
    denoteGraph sm_goal_44 s 622 = fw_matmul (s 621) (s 617) := by
  simp only [sm_goal_44, denoteGraph, List.foldl]
  rw [applyNode_fw_matmul_out]

-- ========== 迷你图 pm_goal_44 算 622 (4×(AllToAll x/y → FW_matmul) → AllReduce) ==========
theorem denote_pm_goal_44_622 (s : Store) :
    denoteGraph pm_goal_44 s 622 = allReducePrim 4 0
      [fw_matmul (allToAllPrimWithDims 4 0 [s 1929, s 1930, s 1931, s 1932] 2 3)
                 (allToAllPrimWithDims 4 0 [s 1829, s 1830, s 1831, s 1832] 3 2),
       fw_matmul (allToAllPrimWithDims 4 1 [s 1929, s 1930, s 1931, s 1932] 2 3)
                 (allToAllPrimWithDims 4 1 [s 1829, s 1830, s 1831, s 1832] 3 2),
       fw_matmul (allToAllPrimWithDims 4 2 [s 1929, s 1930, s 1931, s 1932] 2 3)
                 (allToAllPrimWithDims 4 2 [s 1829, s 1830, s 1831, s 1832] 3 2),
       fw_matmul (allToAllPrimWithDims 4 3 [s 1929, s 1930, s 1931, s 1932] 2 3)
                 (allToAllPrimWithDims 4 3 [s 1829, s 1830, s 1831, s 1832] 3 2)] := by
  simp only [pm_goal_44, denoteGraph, List.foldl]
  rw [applyNode_allReducePrim_out]
  simp only [List.map]
  congr 1

-- ========== SM self-frame: full sm 算 622 (node 47 FW_matmul) ==========
theorem sm_frame_622_self (initSM : Store) :
    denoteGraph sm initSM 622 = denoteGraph sm_goal_44 (denoteGraph sm initSM) 622 := by
  rw [denote_sm_goal_44_622]
  rw [sm_val initSM 47 622 (by native_decide) (by native_decide)]
  rw [show sm.nodes[47]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [621, 617], outs := [622] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [sm_prefix_eq initSM 47 621 (by native_decide),
      sm_prefix_eq initSM 47 617 (by native_decide)]

-- ========== full pm: AllToAll x 输出 1945-1948 (node 300-303, ins=range 1929, params [2,3]) ==========
theorem pm_full_1945 (initPM : Store) :
    denoteGraph pm initPM 1945
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
           denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3 := by
  rw [pm_val initPM 300 1945 (by native_decide) (by native_decide)]
  rw [show pm.nodes[300]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1929 + r)), outs := [1945], params := [2, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 300 1929 (by native_decide),
      pm_prefix_eq initPM 300 1930 (by native_decide),
      pm_prefix_eq initPM 300 1931 (by native_decide),
      pm_prefix_eq initPM 300 1932 (by native_decide)]

theorem pm_full_1946 (initPM : Store) :
    denoteGraph pm initPM 1946
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
           denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3 := by
  rw [pm_val initPM 301 1946 (by native_decide) (by native_decide)]
  rw [show pm.nodes[301]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1929 + r)), outs := [1946], params := [2, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 301 1929 (by native_decide),
      pm_prefix_eq initPM 301 1930 (by native_decide),
      pm_prefix_eq initPM 301 1931 (by native_decide),
      pm_prefix_eq initPM 301 1932 (by native_decide)]

theorem pm_full_1947 (initPM : Store) :
    denoteGraph pm initPM 1947
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
           denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3 := by
  rw [pm_val initPM 302 1947 (by native_decide) (by native_decide)]
  rw [show pm.nodes[302]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1929 + r)), outs := [1947], params := [2, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 302 1929 (by native_decide),
      pm_prefix_eq initPM 302 1930 (by native_decide),
      pm_prefix_eq initPM 302 1931 (by native_decide),
      pm_prefix_eq initPM 302 1932 (by native_decide)]

theorem pm_full_1948 (initPM : Store) :
    denoteGraph pm initPM 1948
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
           denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3 := by
  rw [pm_val initPM 303 1948 (by native_decide) (by native_decide)]
  rw [show pm.nodes[303]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1929 + r)), outs := [1948], params := [2, 3] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 303 1929 (by native_decide),
      pm_prefix_eq initPM 303 1930 (by native_decide),
      pm_prefix_eq initPM 303 1931 (by native_decide),
      pm_prefix_eq initPM 303 1932 (by native_decide)]

-- ========== full pm: AllToAll y 输出 1949-1952 (node 276-279, ins=range 1829, params [3,2]) ==========
theorem pm_full_1949 (initPM : Store) :
    denoteGraph pm initPM 1949
      = allToAllPrimWithDims pm.numRanks 0
          [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
           denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2 := by
  rw [pm_val initPM 276 1949 (by native_decide) (by native_decide)]
  rw [show pm.nodes[276]'(by native_decide)
      = { rank := 0, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1829 + r)), outs := [1949], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 276 1829 (by native_decide),
      pm_prefix_eq initPM 276 1830 (by native_decide),
      pm_prefix_eq initPM 276 1831 (by native_decide),
      pm_prefix_eq initPM 276 1832 (by native_decide)]

theorem pm_full_1950 (initPM : Store) :
    denoteGraph pm initPM 1950
      = allToAllPrimWithDims pm.numRanks 1
          [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
           denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2 := by
  rw [pm_val initPM 277 1950 (by native_decide) (by native_decide)]
  rw [show pm.nodes[277]'(by native_decide)
      = { rank := 1, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1829 + r)), outs := [1950], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 277 1829 (by native_decide),
      pm_prefix_eq initPM 277 1830 (by native_decide),
      pm_prefix_eq initPM 277 1831 (by native_decide),
      pm_prefix_eq initPM 277 1832 (by native_decide)]

theorem pm_full_1951 (initPM : Store) :
    denoteGraph pm initPM 1951
      = allToAllPrimWithDims pm.numRanks 2
          [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
           denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2 := by
  rw [pm_val initPM 278 1951 (by native_decide) (by native_decide)]
  rw [show pm.nodes[278]'(by native_decide)
      = { rank := 2, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1829 + r)), outs := [1951], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 278 1829 (by native_decide),
      pm_prefix_eq initPM 278 1830 (by native_decide),
      pm_prefix_eq initPM 278 1831 (by native_decide),
      pm_prefix_eq initPM 278 1832 (by native_decide)]

theorem pm_full_1952 (initPM : Store) :
    denoteGraph pm initPM 1952
      = allToAllPrimWithDims pm.numRanks 3
          [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
           denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2 := by
  rw [pm_val initPM 279 1952 (by native_decide) (by native_decide)]
  rw [show pm.nodes[279]'(by native_decide)
      = { rank := 3, op := "OpName.AllToAllPrim",
          ins := ((List.range 4).map (fun r => 1829 + r)), outs := [1952], params := [3, 2] }
      from by native_decide]
  rw [applyNode_allToAllPrimWithDims_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 279 1829 (by native_decide),
      pm_prefix_eq initPM 279 1830 (by native_decide),
      pm_prefix_eq initPM 279 1831 (by native_decide),
      pm_prefix_eq initPM 279 1832 (by native_decide)]

-- ========== full pm: FW_matmul 输出 1953-1956 (node 304-307) ==========
theorem pm_full_1953 (initPM : Store) :
    denoteGraph pm initPM 1953
      = fw_matmul (denoteGraph pm initPM 1945) (denoteGraph pm initPM 1949) := by
  rw [pm_val initPM 304 1953 (by native_decide) (by native_decide)]
  rw [show pm.nodes[304]'(by native_decide)
      = { rank := 0, op := "OpName.FW_matmul", ins := [1945, 1949], outs := [1953] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 304 1945 (by native_decide),
      pm_prefix_eq initPM 304 1949 (by native_decide)]

theorem pm_full_1954 (initPM : Store) :
    denoteGraph pm initPM 1954
      = fw_matmul (denoteGraph pm initPM 1946) (denoteGraph pm initPM 1950) := by
  rw [pm_val initPM 305 1954 (by native_decide) (by native_decide)]
  rw [show pm.nodes[305]'(by native_decide)
      = { rank := 1, op := "OpName.FW_matmul", ins := [1946, 1950], outs := [1954] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 305 1946 (by native_decide),
      pm_prefix_eq initPM 305 1950 (by native_decide)]

theorem pm_full_1955 (initPM : Store) :
    denoteGraph pm initPM 1955
      = fw_matmul (denoteGraph pm initPM 1947) (denoteGraph pm initPM 1951) := by
  rw [pm_val initPM 306 1955 (by native_decide) (by native_decide)]
  rw [show pm.nodes[306]'(by native_decide)
      = { rank := 2, op := "OpName.FW_matmul", ins := [1947, 1951], outs := [1955] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 306 1947 (by native_decide),
      pm_prefix_eq initPM 306 1951 (by native_decide)]

theorem pm_full_1956 (initPM : Store) :
    denoteGraph pm initPM 1956
      = fw_matmul (denoteGraph pm initPM 1948) (denoteGraph pm initPM 1952) := by
  rw [pm_val initPM 307 1956 (by native_decide) (by native_decide)]
  rw [show pm.nodes[307]'(by native_decide)
      = { rank := 3, op := "OpName.FW_matmul", ins := [1948, 1952], outs := [1956] }
      from by native_decide]
  rw [applyNode_fw_matmul_out]
  rw [pm_prefix_eq initPM 307 1948 (by native_decide),
      pm_prefix_eq initPM 307 1952 (by native_decide)]

-- ========== PM self-frame: 622 (AllReduce node 308, ins=computed range 1953) ==========
theorem pm_frame_622_self (initPM : Store) :
    denoteGraph pm initPM 622
      = allReducePrim 4 0
          [fw_matmul
             (allToAllPrimWithDims 4 0 [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
                denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3)
             (allToAllPrimWithDims 4 0 [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
                denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2),
           fw_matmul
             (allToAllPrimWithDims 4 1 [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
                denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3)
             (allToAllPrimWithDims 4 1 [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
                denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2),
           fw_matmul
             (allToAllPrimWithDims 4 2 [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
                denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3)
             (allToAllPrimWithDims 4 2 [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
                denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2),
           fw_matmul
             (allToAllPrimWithDims 4 3 [denoteGraph pm initPM 1929, denoteGraph pm initPM 1930,
                denoteGraph pm initPM 1931, denoteGraph pm initPM 1932] 2 3)
             (allToAllPrimWithDims 4 3 [denoteGraph pm initPM 1829, denoteGraph pm initPM 1830,
                denoteGraph pm initPM 1831, denoteGraph pm initPM 1832] 3 2)] := by
  rw [pm_val initPM 308 622 (by native_decide) (by native_decide)]
  rw [show pm.nodes[308]'(by native_decide)
      = { rank := 0, op := "OpName.AllReducePrim",
          ins := ((List.range 4).map (fun r => 1953 + r)), outs := [622] }
      from by native_decide]
  rw [applyNode_allReducePrim_out]
  simp only [List.range, List.range.loop, List.map]
  rw [pm_prefix_eq initPM 308 1953 (by native_decide),
      pm_prefix_eq initPM 308 1954 (by native_decide),
      pm_prefix_eq initPM 308 1955 (by native_decide),
      pm_prefix_eq initPM 308 1956 (by native_decide)]
  rw [pm_full_1953, pm_full_1954, pm_full_1955, pm_full_1956]
  rw [pm_full_1945, pm_full_1946, pm_full_1947, pm_full_1948,
      pm_full_1949, pm_full_1950, pm_full_1951, pm_full_1952]
  rw [show pm.numRanks = 4 from by native_decide]

-- ========== 总装 ==========
theorem goal_44_cut_to_full (h : goal_44_stmt_cut) : goal_44_stmt := by
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
  have hg31 := goal_31_intermediate initSM initPM hSM hPM hInit
  have hg32 := goal_32_intermediate initSM initPM hSM hPM hInit
  have hg33 := goal_33_intermediate initSM initPM hSM hPM hInit
  have hg34 := goal_34_intermediate initSM initPM hSM hPM hInit
  have hg35 := goal_35_intermediate initSM initPM hSM hPM hInit
  have hg36 := goal_36_intermediate initSM initPM hSM hPM hInit
  have hg37 := goal_37_intermediate initSM initPM hSM hPM hInit
  have hg38 := goal_38_intermediate initSM initPM hSM hPM hInit
  have hg39 := goal_39_intermediate initSM initPM hSM hPM hInit
  have hg40 := goal_40_intermediate initSM initPM hSM hPM hInit
  have hg41 := goal_41_intermediate initSM initPM hSM hPM hInit
  have hg42 := goal_42_intermediate initSM initPM hSM hPM hInit
  have hg43 := goal_43_intermediate initSM initPM hSM hPM hInit
  have hg257 := goal_257_intermediate initSM initPM hSM hPM hInit
  have hg259 := goal_259_intermediate initSM initPM hSM hPM hInit
  have hg261 := goal_261_intermediate initSM initPM hSM hPM hInit
  have hg263 := goal_263_intermediate initSM initPM hSM hPM hInit
  have hg265 := goal_265_intermediate initSM initPM hSM hPM hInit
  have hg267 := goal_267_intermediate initSM initPM hSM hPM hInit
  have hg269 := goal_269_intermediate initSM initPM hSM hPM hInit
  have hg271 := goal_271_intermediate initSM initPM hSM hPM hInit
  have hg275 := goal_275_intermediate initSM initPM hSM hPM hInit
  have hg277 := goal_277_intermediate initSM initPM hSM hPM hInit
  have hg279 := goal_279_intermediate initSM initPM hSM hPM hInit
  have hinitC := initGoals_preserved initSM initPM hInit
  rw [← hSsm, ← hSpm] at hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg25 hg26 hg27 hg28 hg29 hg30 hg31 hg32 hg33 hg34 hg35 hg36 hg37 hg38 hg39 hg40 hg41 hg42 hg43 hg257 hg259 hg261 hg263 hg265 hg267 hg269 hg271 hg275 hg277 hg279 hinitC
  have hnr : pm_goal_44.numRanks = pm.numRanks := by native_decide
  have hInitCut : InitGoalsHold pm_goal_44.numRanks goal_44_cut_initGoals Ssm Spm := by
    rw [hnr]
    simp only [InitGoalsHold] at hinitC ⊢
    simp only [goal_44_cut_initGoals, goal_44_prereqs, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨hinitC, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hg24, hg25, hg26, hg27, hg28, hg29, hg30, hg31, hg32, hg33, hg34, hg35, hg36, hg37, hg38, hg39, hg40, hg41, hg42, hg43, hg257, hg259, hg261, hg263, hg265, hg267, hg269, hg271, hg275, hg277, hg279, List.forall_mem_nil _⟩
  -- SM input shapes: 621 = goal_43.ts [1,4,8,8]; 617 = goal_39.ts [1,4,8,8]
  have h621_smsh : (Ssm 621).shape = [1, 4, 8, 8] := by
    have h := hg43.1; simp only [goal_43] at h; exact h
  have h617_smsh : (Ssm 617).shape = [1, 4, 8, 8] := by
    have h := hg39.1; simp only [goal_39] at h; exact h
  -- PM tp shapes: 1929-1932 = goal_43.tps [1,4,2,8]; 1829-1832 = goal_39.tps [1,4,8,2]
  have hx : (Spm 1929).shape = [1,4,2,8] ∧ (Spm 1930).shape = [1,4,2,8] ∧
            (Spm 1931).shape = [1,4,2,8] ∧ (Spm 1932).shape = [1,4,2,8] := by
    have h := hg43.2.1
    simp only [goal_43, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1929sh, h1930sh, h1931sh, h1932sh⟩ := hx
  have hy : (Spm 1829).shape = [1,4,8,2] ∧ (Spm 1830).shape = [1,4,8,2] ∧
            (Spm 1831).shape = [1,4,8,2] ∧ (Spm 1832).shape = [1,4,8,2] := by
    have h := hg39.2.1
    simp only [goal_39, List.map, List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h1829sh, h1830sh, h1831sh, h1832sh⟩ := hy
  have hSM44 : StoreShapesHold Ssm sm_goal_44InitEnv := by
    intro tid sh hsh
    rw [sm_goal_44InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_44InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h617_smsh
    · exact h621_smsh
  have hPM44 : StoreShapesHold Spm pm_goal_44InitEnv := by
    intro tid sh hsh
    rw [pm_goal_44InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_44InitShapes, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1829sh
    · exact h1830sh
    · exact h1831sh
    · exact h1832sh
    · exact h1929sh
    · exact h1930sh
    · exact h1931sh
    · exact h1932sh
  have hcut := h Ssm Spm hSM44 hPM44 hInitCut
  -- Frame: 622 (sm node 47), 622 (pm node 308)
  have hsmf : Ssm 622 = denoteGraph sm_goal_44 Ssm 622 := by
    rw [hSsm]; exact sm_frame_622_self initSM
  have hpm622 : Spm 622 = denoteGraph pm_goal_44 Spm 622 := by
    rw [denote_pm_goal_44_622]
    rw [hSpm]; exact pm_frame_622_self initPM
  rw [hnr] at hcut
  simp only [goal_44, List.map] at hcut ⊢
  rw [hsmf, hpm622]
  exact hcut

theorem goal_44_intermediate (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_44 (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hfull : goal_44_stmt := goal_44_cut_to_full prove_goal_44_cut
  exact hfull initSM initPM hSM hPM hInit

end TrainVerify.Denote.GeneratedGoals