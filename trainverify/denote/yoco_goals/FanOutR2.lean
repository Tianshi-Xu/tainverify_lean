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

/-- 8033 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8033_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8033
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8033 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8033 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8033 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15767 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15767 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15767 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15815 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15815 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15815 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8033 8033 15767 15815 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8037 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8037_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8037
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8037 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8037 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8037 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15771 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15771 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15771 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15819 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15819 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15819 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8037 8037 15771 15819 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8041 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8041_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8041
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8041 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8041 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8041 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15775 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15775 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15775 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15823 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15823 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15823 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8041 8041 15775 15823 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8045 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8045_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8045
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8045 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8045 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8045 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15779 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15779 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15779 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15827 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15827 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15827 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8045 8045 15779 15827 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8049 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8049_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8049
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8049 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8049 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8049 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15783 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15783 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15783 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15831 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15831 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15831 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8049 8049 15783 15831 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8053 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8053_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8053
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8053 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8053 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8053 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15787 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15787 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15787 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15835 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15835 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15835 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8053 8053 15787 15835 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8057 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8057_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8057
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8057 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8057 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8057 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15791 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15791 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15791 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15839 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15839 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15839 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8057 8057 15791 15839 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8061 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8061_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8061
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8061 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8061 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8061 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15795 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15795 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15795 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15843 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15843 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15843 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8061 8061 15795 15843 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8065 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8065_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8065
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8065 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8065 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8065 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15799 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15799 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15799 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15847 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15847 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15847 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8065 8065 15799 15847 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8069 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8069_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8069
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8069 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8069 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8069 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15803 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15803 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15803 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15851 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15851 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15851 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8069 8069 15803 15851 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8073 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8073_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8073
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8073 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8073 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8073 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15807 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15807 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15807 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15855 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15855 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15855 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8073 8073 15807 15855 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8077 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5334`. -/
theorem recon_intermediateGoal_8077_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8077
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5334_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5334 = denoteGraph_ringAttn pm initPM 5334 :=
    oneTp_valeq intermediateGoal_5334 _ _ 5334 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5334).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5334] using h
  have sG : denoteGraph_ringAttn sm initSM 8077 = id (denoteGraph_ringAttn sm initSM 5334) :=
    ringAttn_reduce1 sm initSM 478
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }
      5334 8077 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5334 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 8077 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15811 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1020
      { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }
      5334 15811 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5334 [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811] 15811 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15859 = id (denoteGraph_ringAttn pm initPM 5334) :=
    ringAttn_reduce1 pm initPM 1021
      { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }
      5334 15859 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5334 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 15859 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8077 8077 15811 15859 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

end TrainVerify.Denote.GeneratedPatterns
