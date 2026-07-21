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

/-- 8091 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8091_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8091
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8091 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8091 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8091 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15873 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15873 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15873 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15921 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15921 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15921 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8091 8091 15873 15921 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8095 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8095_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8095
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8095 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8095 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8095 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15877 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15877 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15877 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15925 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15925 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15925 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8095 8095 15877 15925 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8099 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8099_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8099
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8099 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8099 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8099 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15881 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15881 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15881 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15929 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15929 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15929 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8099 8099 15881 15929 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8103 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8103_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8103
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8103 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8103 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8103 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15885 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15885 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15885 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15933 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15933 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15933 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8103 8103 15885 15933 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8107 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8107_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8107
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8107 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8107 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8107 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15889 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15889 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15889 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15937 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15937 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15937 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8107 8107 15889 15937 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8111 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8111_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8111
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8111 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8111 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8111 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15893 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15893 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15893 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15941 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15941 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15941 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8111 8111 15893 15941 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8115 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8115_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8115
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8115 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8115 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8115 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15897 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15897 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15897 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15945 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15945 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15945 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8115 8115 15897 15945 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8119 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8119_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8119
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8119 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8119 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8119 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15901 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15901 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15901 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15949 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15949 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15949 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8119 8119 15901 15949 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8123 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8123_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8123
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8123 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8123 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8123 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15905 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15905 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15905 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15953 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15953 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15953 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8123 8123 15905 15953 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8127 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8127_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8127
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8127 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8127 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8127 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15909 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15909 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15909 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15957 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15957 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15957 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8127 8127 15909 15957 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8131 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8131_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8131
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8131 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8131 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8131 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15913 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15913 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15913 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15961 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15961 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15961 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8131 8131 15913 15961 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

/-- 8135 — 2-tp replicated `FW_multiref` copy of 1-tp replicated base `5336`. -/
theorem recon_intermediateGoal_8135_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8135
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_5336_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 5336 = denoteGraph_ringAttn pm initPM 5336 :=
    oneTp_valeq intermediateGoal_5336 _ _ 5336 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 5336).shape = [4096, 4, 64] := by
    have h := hB.1; simpa [intermediateGoal_5336] using h
  have sG : denoteGraph_ringAttn sm initSM 8135 = id (denoteGraph_ringAttn sm initSM 5336) :=
    ringAttn_reduce1 sm initSM 479
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }
      5336 8135 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen sm s 0 5336 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 8135 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 : denoteGraph_ringAttn pm initPM 15917 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1022
      { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }
      5336 15917 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 0 5336 [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917] 15917 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 : denoteGraph_ringAttn pm initPM 15965 = id (denoteGraph_ringAttn pm initPM 5336) :=
    ringAttn_reduce1 pm initPM 1023
      { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }
      5336 15965 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_mref_gen pm s 1 5336 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 15965 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG p0 p1
  refine wrap_repl_dual_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8135 8135 15917 15965 [4096, 4, 64] rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sG, hvB, ← p0]
  · rw [sG]; exact hsB
  · rw [p0, ← hvB]; exact hsB
  · rw [p1, ← hvB]; exact hsB

end TrainVerify.Denote.GeneratedPatterns
