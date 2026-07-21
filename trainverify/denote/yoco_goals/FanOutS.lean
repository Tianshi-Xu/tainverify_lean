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

private theorem wrap_1tp_distinct (smS pmS : Store) (g : LineageGoal) (Tsm Tpm : Tid) (sh : Shape)
    (htp : g.tps = [{rank := 0, tid := Tpm}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = Tsm) (htsShape : g.tsShape = sh)
    (htpShapes : g.tpShapes = [sh])
    (hval : smS Tsm = pmS Tpm)
    (hshape : (smS Tsm).shape = sh) :
    InitGoalHolds pm.numRanks g smS pmS := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape
  · rw [htp, htpShapes]; simp only [List.map, List.cons.injEq, and_true]; rw [← hval]; exact hshape
  · rw [reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, htp, hts, hgd]
    simp only [List.map, reconstructWithDim]; exact hval

/-- 7415 — 1-tp `FW_multiref` (pos 0) copy of replicated base `4705`.
    Single PM shard `11875` = full copy; SM 7415 = SM 4705 = PM 4705 = PM 11875. -/
theorem recon_intermediateGoal_7415_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7415
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hvB : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4705] using h
  have sG : denoteGraph_ringAttn sm initSM 7415 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7415 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 4705 7415 7419 7423 7427 7431)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11875 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11875 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 4705 11875 11876 11877 11878 11879)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7415 = denoteGraph_ringAttn pm initPM 11875 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7415).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7415 7415 11875 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7423 — 1-tp `FW_multiref` (pos 2) copy of replicated base `4705`.
    Single PM shard `11877` = full copy; SM 7423 = SM 4705 = PM 4705 = PM 11877. -/
theorem recon_intermediateGoal_7423_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7423
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hvB : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4705] using h
  have sG : denoteGraph_ringAttn sm initSM 7423 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7423 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4705 7415 7419 7423 7427 7431 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11877 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11877 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 4705 11875 11876 11877 11878 11879 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7423 = denoteGraph_ringAttn pm initPM 11877 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7423).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7423 7423 11877 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7427 — 1-tp `FW_multiref` (pos 3) copy of replicated base `4705`.
    Single PM shard `11878` = full copy; SM 7427 = SM 4705 = PM 4705 = PM 11878. -/
theorem recon_intermediateGoal_7427_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7427
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hvB : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4705] using h
  have sG : denoteGraph_ringAttn sm initSM 7427 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7427 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4705 7415 7419 7423 7427 7431 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11878 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11878 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 4705 11875 11876 11877 11878 11879 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7427 = denoteGraph_ringAttn pm initPM 11878 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7427).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7427 7427 11878 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7431 — 1-tp `FW_multiref` (pos 4) copy of replicated base `4705`.
    Single PM shard `11879` = full copy; SM 7431 = SM 4705 = PM 4705 = PM 11879. -/
theorem recon_intermediateGoal_7431_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7431
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hvB : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4705] using h
  have sG : denoteGraph_ringAttn sm initSM 7431 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7431 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4705 7415 7419 7423 7427 7431 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11879 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11879 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 4705 11875 11876 11877 11878 11879 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7431 = denoteGraph_ringAttn pm initPM 11879 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7431).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7431 7431 11879 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7456 — 1-tp `FW_multiref` (pos 0) copy of replicated base `4757`.
    Single PM shard `11889` = full copy; SM 7456 = SM 4757 = PM 4757 = PM 11889. -/
theorem recon_intermediateGoal_7456_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7456
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4757_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4757 = denoteGraph_ringAttn pm initPM 4757 :=
    oneTp_valeq intermediateGoal_4757 _ _ 4757 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4757).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4757] using h
  have sG : denoteGraph_ringAttn sm initSM 7456 = id (denoteGraph_ringAttn sm initSM 4757) :=
    ringAttn_reduce1 sm initSM 55
      { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] }
      4757 7456 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4757 7456 7460)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11889 = id (denoteGraph_ringAttn pm initPM 4757) :=
    ringAttn_reduce1 pm initPM 160
      { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }
      4757 11889 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 4757 11889 11890)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7456 = denoteGraph_ringAttn pm initPM 11889 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7456).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7456 7456 11889 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7467 — 1-tp `FW_multiref` (pos 0) copy of replicated base `4759`.
    Single PM shard `11903` = full copy; SM 7467 = SM 4759 = PM 4759 = PM 11903. -/
theorem recon_intermediateGoal_7467_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7467
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4759] using h
  have sG : denoteGraph_ringAttn sm initSM 7467 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1 sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7467 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 4759 7467 7471 7475 7479 7483)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11903 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1 pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11903 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 4759 11903 11904 11905 11906 11907)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7467 = denoteGraph_ringAttn pm initPM 11903 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7467).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7467 7467 11903 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7475 — 1-tp `FW_multiref` (pos 2) copy of replicated base `4759`.
    Single PM shard `11905` = full copy; SM 7475 = SM 4759 = PM 4759 = PM 11905. -/
theorem recon_intermediateGoal_7475_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7475
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4759] using h
  have sG : denoteGraph_ringAttn sm initSM 7475 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1 sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7475 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11905 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1 pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11905 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7475 = denoteGraph_ringAttn pm initPM 11905 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7475).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7475 7475 11905 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7479 — 1-tp `FW_multiref` (pos 3) copy of replicated base `4759`.
    Single PM shard `11906` = full copy; SM 7479 = SM 4759 = PM 4759 = PM 11906. -/
theorem recon_intermediateGoal_7479_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7479
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4759] using h
  have sG : denoteGraph_ringAttn sm initSM 7479 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1 sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7479 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11906 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1 pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11906 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7479 = denoteGraph_ringAttn pm initPM 11906 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7479).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7479 7479 11906 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 7483 — 1-tp `FW_multiref` (pos 4) copy of replicated base `4759`.
    Single PM shard `11907` = full copy; SM 7483 = SM 4759 = PM 4759 = PM 11907. -/
theorem recon_intermediateGoal_7483_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7483
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hB := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hvB : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl hB
  have hsB : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have h := hB.1; simpa [intermediateGoal_4759] using h
  have sG : denoteGraph_ringAttn sm initSM 7483 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1 sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7483 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have pT : denoteGraph_ringAttn pm initPM 11907 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1 pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11907 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG pT
  have hval : denoteGraph_ringAttn sm initSM 7483 = denoteGraph_ringAttn pm initPM 11907 := by
    rw [sG, hvB, ← pT]
  have hshape : (denoteGraph_ringAttn sm initSM 7483).shape = [4096, 1024] := by rw [sG]; exact hsB
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7483 7483 11907 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
