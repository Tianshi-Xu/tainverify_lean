import denote.yoco_goals.ZigzagL11Body

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem applyNode_mref_gen (g : GraphDecl) (s : Store) (rank : Nat) (xTid : Tid)
    (outs : List Tid) (i : Tid) (hi : i ∈ outs) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := outs, params := [outs.length] } i = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact storeSet_replicate_mem_g307 s outs (s xTid) i hi

private theorem wrap_repl_dual_gen (smF pmF : Store) (g : LineageGoal)
    (T p0 p1 : Tid) (sh : Shape)
    (htp : g.tps = [{ rank := 0, tid := p0 }, { rank := 1, tid := p1 }])
    (hrep : g.replicated = true) (hts : g.ts = T) (htsShape : g.tsShape = sh)
    (htpShapes : g.tpShapes = [sh, sh])
    (hval : smF T = pmF p0)
    (hshape0 : (smF T).shape = sh) (hshapeP0 : (pmF p0).shape = sh) (hshapeP1 : (pmF p1).shape = sh) :
    InitGoalHolds pm.numRanks g smF pmF := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape0
  · rw [htp, htpShapes]; simp only [List.map]; rw [hshapeP0, hshapeP1]
  · unfold reconstructForGoal
    rw [hrep]
    simp only [if_true, htp, hts, List.map, List.headD]
    exact hval

/-- 7404 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `4703`. -/
theorem recon_intermediateGoal_7404_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7404
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4703_ringAttn initSM initPM hSM hPM hInit
  have hvB : denoteGraph_ringAttn sm initSM 4703 = denoteGraph_ringAttn pm initPM 4703 :=
    oneTp_valeq intermediateGoal_4703 _ _ 4703 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4703).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4703] using h
  have sG : denoteGraph_ringAttn sm initSM 7404 = id (denoteGraph_ringAttn sm initSM 4703) :=
    ringAttn_reduce1 sm initSM 16
      { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }
      4703 7404 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 4703 [7404, 7408] 7404 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 14644 = id (denoteGraph_ringAttn pm initPM 4703) :=
    ringAttn_reduce1 pm initPM 64
      { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [14644, 14648], params := [2] }
      4703 14644 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 4703 [14644, 14648] 14644 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 14652 = id (denoteGraph_ringAttn pm initPM 4703) :=
    ringAttn_reduce1 pm initPM 65
      { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] }
      4703 14652 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 4703 [14652, 14656] 14652 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7404 7404 14644 14652 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 7408 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `4703`. -/
theorem recon_intermediateGoal_7408_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7408
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4703_ringAttn initSM initPM hSM hPM hInit
  have hvB : denoteGraph_ringAttn sm initSM 4703 = denoteGraph_ringAttn pm initPM 4703 :=
    oneTp_valeq intermediateGoal_4703 _ _ 4703 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4703).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4703] using h
  have sG : denoteGraph_ringAttn sm initSM 7408 = id (denoteGraph_ringAttn sm initSM 4703) :=
    ringAttn_reduce1 sm initSM 16
      { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }
      4703 7408 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 4703 [7404, 7408] 7408 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 14648 = id (denoteGraph_ringAttn pm initPM 4703) :=
    ringAttn_reduce1 pm initPM 64
      { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [14644, 14648], params := [2] }
      4703 14648 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 4703 [14644, 14648] 14648 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 14656 = id (denoteGraph_ringAttn pm initPM 4703) :=
    ringAttn_reduce1 pm initPM 65
      { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] }
      4703 14656 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 4703 [14652, 14656] 14656 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7408 7408 14648 14656 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 7435 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `4736`. -/
theorem recon_intermediateGoal_7435_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7435
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4736_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4736 = denoteGraph_ringAttn pm initPM 4736 :=
    oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4736).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4736] using h
  have sG : denoteGraph_ringAttn sm initSM 7435 = id (denoteGraph_ringAttn sm initSM 4736) :=
    ringAttn_reduce1 sm initSM 41
      { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439], params := [2] }
      4736 7435 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 4736 [7435, 7439] 7435 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 14660 = id (denoteGraph_ringAttn pm initPM 4736) :=
    ringAttn_reduce1 pm initPM 124
      { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [14660, 14664], params := [2] }
      4736 14660 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 4736 [14660, 14664] 14660 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 14668 = id (denoteGraph_ringAttn pm initPM 4736) :=
    ringAttn_reduce1 pm initPM 125
      { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672], params := [2] }
      4736 14668 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 4736 [14668, 14672] 14668 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7435 7435 14660 14668 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 7439 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `4736`. -/
theorem recon_intermediateGoal_7439_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7439
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4736_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4736 = denoteGraph_ringAttn pm initPM 4736 :=
    oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4736).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4736] using h
  have sG : denoteGraph_ringAttn sm initSM 7439 = id (denoteGraph_ringAttn sm initSM 4736) :=
    ringAttn_reduce1 sm initSM 41
      { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439], params := [2] }
      4736 7439 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 4736 [7435, 7439] 7439 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 14664 = id (denoteGraph_ringAttn pm initPM 4736) :=
    ringAttn_reduce1 pm initPM 124
      { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [14660, 14664], params := [2] }
      4736 14664 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 4736 [14660, 14664] 14664 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 14672 = id (denoteGraph_ringAttn pm initPM 4736) :=
    ringAttn_reduce1 pm initPM 125
      { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672], params := [2] }
      4736 14672 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 4736 [14668, 14672] 14672 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7439 7439 14664 14672 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 7444 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `4738`. -/
theorem recon_intermediateGoal_7444_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7444
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4738_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4738 = denoteGraph_ringAttn pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4738).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4738] using h
  have sG : denoteGraph_ringAttn sm initSM 7444 = id (denoteGraph_ringAttn sm initSM 4738) :=
    ringAttn_reduce1 sm initSM 43
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] }
      4738 7444 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 4738 [7444, 7448, 7452] 7444 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 14677 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1 pm initPM 128
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685], params := [3] }
      4738 14677 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 4738 [14677, 14681, 14685] 14677 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 14689 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1 pm initPM 129
      { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] }
      4738 14689 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 4738 [14689, 14693, 14697] 14689 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7444 7444 14677 14689 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 7448 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `4738`. -/
theorem recon_intermediateGoal_7448_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7448
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4738_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4738 = denoteGraph_ringAttn pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4738).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4738] using h
  have sG : denoteGraph_ringAttn sm initSM 7448 = id (denoteGraph_ringAttn sm initSM 4738) :=
    ringAttn_reduce1 sm initSM 43
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] }
      4738 7448 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 4738 [7444, 7448, 7452] 7448 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 14681 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1 pm initPM 128
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685], params := [3] }
      4738 14681 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 4738 [14677, 14681, 14685] 14681 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 14693 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1 pm initPM 129
      { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] }
      4738 14693 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 4738 [14689, 14693, 14697] 14693 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7448 7448 14681 14693 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 7452 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `4738`. -/
theorem recon_intermediateGoal_7452_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7452
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4738_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4738 = denoteGraph_ringAttn pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4738).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4738] using h
  have sG : denoteGraph_ringAttn sm initSM 7452 = id (denoteGraph_ringAttn sm initSM 4738) :=
    ringAttn_reduce1 sm initSM 43
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] }
      4738 7452 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 4738 [7444, 7448, 7452] 7452 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 14685 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1 pm initPM 128
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685], params := [3] }
      4738 14685 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 4738 [14677, 14681, 14685] 14685 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 14697 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1 pm initPM 129
      { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] }
      4738 14697 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 4738 [14689, 14693, 14697] 14697 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7452 7452 14685 14697 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8015 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5332`. -/
theorem recon_intermediateGoal_8015_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8015
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5332_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5332 = denoteGraph_ringAttn pm initPM 5332 :=
    oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5332).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_5332] using h
  have sG : denoteGraph_ringAttn sm initSM 8015 = id (denoteGraph_ringAttn sm initSM 5332) :=
    ringAttn_reduce1 sm initSM 473
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] }
      5332 8015 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5332 [8015, 8019] 8015 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15741 = id (denoteGraph_ringAttn pm initPM 5332) :=
    ringAttn_reduce1 pm initPM 1011
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [15741, 15745], params := [2] }
      5332 15741 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5332 [15741, 15745] 15741 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15749 = id (denoteGraph_ringAttn pm initPM 5332) :=
    ringAttn_reduce1 pm initPM 1012
      { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] }
      5332 15749 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5332 [15749, 15753] 15749 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8015 8015 15741 15749 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8019 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5332`. -/
theorem recon_intermediateGoal_8019_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8019
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5332_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5332 = denoteGraph_ringAttn pm initPM 5332 :=
    oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5332).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_5332] using h
  have sG : denoteGraph_ringAttn sm initSM 8019 = id (denoteGraph_ringAttn sm initSM 5332) :=
    ringAttn_reduce1 sm initSM 473
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] }
      5332 8019 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5332 [8015, 8019] 8019 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15745 = id (denoteGraph_ringAttn pm initPM 5332) :=
    ringAttn_reduce1 pm initPM 1011
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [15741, 15745], params := [2] }
      5332 15745 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5332 [15741, 15745] 15745 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15753 = id (denoteGraph_ringAttn pm initPM 5332) :=
    ringAttn_reduce1 pm initPM 1012
      { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] }
      5332 15753 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5332 [15749, 15753] 15753 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8019 8019 15745 15753 [4096, 1024] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

end TrainVerify.Denote.GeneratedPatterns
