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
    (htp : g.tps = [{ rank := 0, tid := Tpm }]) (hgd : g.gatherDim = 0)
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

/-- 8007 — 1-tp `FW_multiref` (pos 0) copy of the 2-tp base `5330`.
    The single PM shard `11917 = AllGatherPrim(14597, 14599)`, where
    `14597 = mref₀(9625)` and `14599 = mref₀(9626)` are identity copies of
    `5330`'s two shards. Hence `SM 8007 = SM 5330 = allGather[9625,9626] = PM 11917`. -/
theorem recon_intermediateGoal_8007_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8007
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have sG : denoteGraph_ringAttn sm initSM 8007 = id (denoteGraph_ringAttn sm initSM 5330) :=
    ringAttn_reduce1 sm initSM 470
      { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] }
      5330 8007 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5330 8007 8011)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨hgB, hsPA, hsPB⟩ := twoTp_gather _ _ intermediateGoal_5330 5330 9625 9626
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5330_ringAttn initSM initPM hSM hPM hInit hWF)
  have q0 : denoteGraph_ringAttn pm initPM 14597 = id (denoteGraph_ringAttn pm initPM 9625) :=
    ringAttn_reduce1 pm initPM 1001
      { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] }
      9625 14597 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9625 14597 13257)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 : denoteGraph_ringAttn pm initPM 14599 = id (denoteGraph_ringAttn pm initPM 9626) :=
    ringAttn_reduce1 pm initPM 1002
      { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] }
      9626 14599 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9626 14599 13258)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 : denoteGraph_ringAttn pm initPM 11917
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14597, denoteGraph_ringAttn pm initPM 14599] :=
    ringAttn_reduce2 pm initPM 1004
      { rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917], params := [0] }
      14597 14599 11917 (fun a b => allGatherPrimDimN 0 pm.numRanks 0 [a, b])
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_allGatherPrimDimN_out pm s 0 [14597, 14599] 11917 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at sG q0 q1
  have hnr : pm.numRanks = 2 := rfl
  have hval : denoteGraph_ringAttn sm initSM 8007 = denoteGraph_ringAttn pm initPM 11917 := by
    rw [sG, hgB, r0, q0, q1]
  have hshape : (denoteGraph_ringAttn sm initSM 8007).shape = [4096, 1024] := by
    rw [hval, r0, q0, q1, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsPA])]
    simp [List.set, List.getD]
  exact wrap_1tp_distinct (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8007 8007 11917 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
