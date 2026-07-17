/- Worker #26 — YOCO cross-decoder Layer-0 residual: 8143 + 5354.

   `8143` is the SM multiref fan-out `mref₁(5338)` (SM node 474,
   `FW_multiref(5338) → [8139, 8143]`, params=[2]).  W25 wrongly hypothesised it
   was the PM-namespace `FW_per_head_mix_precision_linear(14926, 4901)` node —
   that is a *different* tid living in the PM graph's tid space, unrelated to the
   SM reconstruction goal for tid 8143.  The exact SM/PM slice is:

   - SM  474: `FW_multiref(5338) → [8139, 8143]`   (8143 = mref index 1 of 5338)
   - PM 1006: `FW_multiref(9655) → [15969, 15973]`  (rank 0, 15973 = mref₁(9655))
   - PM 1009: `FW_multiref(9656) → [15977, 15981]`  (rank 1, 15981 = mref₁(9656))

   `5338` (= gather[9655, 9656], shard `[2048,1024]`) was already reconstructed by
   W24 in `L12MaybeShuffle`.  Since `fw_multiref` is the identity on the data
   tensor, `8143` is `5338` re-labelled on both SM and PM sides — the *sibling*
   output of the very multiref whose index-0 leg (`8139/15969/15977`) W24 already
   traversed to prove `5340`.  So `8143` is classification #1 (a multiref/fan-out
   alias of an already-reconstructed L12 boundary value); no new gears, no new WF
   fields, no deep decoder lineage.

   `5354 = FW_add(8143, 5353)` is then the layer-0 residual add, closed by the
   standard dim-0 add-commute (`fw_add_allGather0_commute_2_2048_1024`). -/
import denote.yoco_goals.ZigzagL0Entry

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 8143 — `mref₁(5338)` (SM node 474).  Identity alias of the proven L12 boundary
    `5338`; the sibling `8139` (index 0) was already used by W24 to prove `5340`. -/
theorem recon_intermediateGoal_8143_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8143
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg38, hs9655, hs9656⟩ := twoTp_gather _ _ intermediateGoal_5338 5338 9655 9656
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5338_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8143 : denoteGraph_ringAttn sm initSM 8143 = denoteGraph_ringAttn sm initSM 5338 :=
    ringAttn_reduce1_pm_opaque sm initSM 474
      { rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] }
      5338 8143 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5338 8139 8143 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15973 : denoteGraph_ringAttn pm initPM 15973 = denoteGraph_ringAttn pm initPM 9655 :=
    ringAttn_reduce1_pm_opaque pm initPM 1006
      { rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] }
      9655 15973 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9655 15969 15973 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15981 : denoteGraph_ringAttn pm initPM 15981 = denoteGraph_ringAttn pm initPM 9656 :=
    ringAttn_reduce1_pm_opaque pm initPM 1009
      { rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] }
      9656 15981 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9656 15977 15981 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 8143
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15973, denoteGraph_ringAttn pm initPM 15981] := by
    rw [s8143, hg38, ← p15973, ← p15981]
  have hsp0 : (denoteGraph_ringAttn pm initPM 15973).shape = [2048, 1024] := by
    rw [p15973]; exact hs9655
  have hsp1 : (denoteGraph_ringAttn pm initPM 15981).shape = [2048, 1024] := by
    rw [p15981]; exact hs9656
  have hshape : (denoteGraph_ringAttn sm initSM 8143).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8143 8143 15973 15981 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5354 — `FW_add(8143, 5353)`, the layer-0 residual add (SM node 511).
    Both addends gather over shard `[2048,1024]`; closed by dim-0 add-commute. -/
theorem recon_intermediateGoal_5354_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5354
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval8143, hs15973, hs15981⟩ := twoTp_gather _ _ intermediateGoal_8143 8143 15973 15981
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_8143_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr53, hs9713, hs9714⟩ := twoTp_gather _ _ intermediateGoal_5353 5353 9713 9714
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5353_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5354
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 8143) (denoteGraph_ringAttn sm initSM 5353) :=
    ringAttn_reduce2_pm_opaque sm initSM 511
      { rank := 0, op := "OpName.FW_add", ins := [8143, 5353], outs := [5354] }
      8143 5353 5354 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 8143 5353 5354)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9717
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15973) (denoteGraph_ringAttn pm initPM 9713) :=
    ringAttn_reduce2_pm_opaque pm initPM 1084
      { rank := 0, op := "OpName.FW_add", ins := [15973, 9713], outs := [9717] }
      15973 9713 9717 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15973 9713 9717)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9718
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15981) (denoteGraph_ringAttn pm initPM 9714) :=
    ringAttn_reduce2_pm_opaque pm initPM 1085
      { rank := 1, op := "OpName.FW_add", ins := [15981, 9714], outs := [9718] }
      15981 9714 9718 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15981 9714 9718)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5354
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9717, denoteGraph_ringAttn pm initPM 9718] := by
    rw [rSM, hval8143, hbr53, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15973 hs15981 hs9713 hs9714,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9717).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15973 hs9713
  have hsp1 : (denoteGraph_ringAttn pm initPM 9718).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15981 hs9714
  have hshape : (denoteGraph_ringAttn sm initSM 5354).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5354 5354 9717 9718 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5356 — `FW_rms_norm(mref₀(5354), 5355)` (SM node 513).  Same template as
    `5340`: 2-tp dim-0 RMSNorm through the residual multiref `8147=mref₀(5354)`. -/
theorem recon_intermediateGoal_5356_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5356
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg54, hs9717, hs9718⟩ := twoTp_gather _ _ intermediateGoal_5354 5354 9717 9718
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5354_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8147 : denoteGraph_ringAttn sm initSM 8147 = id (denoteGraph_ringAttn sm initSM 5354) :=
    ringAttn_reduce1_pm_opaque sm initSM 512
      { rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151], params := [2] }
      5354 8147 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5354 8147 8151)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15985 : denoteGraph_ringAttn pm initPM 15985 = id (denoteGraph_ringAttn pm initPM 9717) :=
    ringAttn_reduce1_pm_opaque pm initPM 1086
      { rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989], params := [2] }
      9717 15985 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9717 15985 15989)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15993 : denoteGraph_ringAttn pm initPM 15993 = id (denoteGraph_ringAttn pm initPM 9718) :=
    ringAttn_reduce1_pm_opaque pm initPM 1087
      { rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997], params := [2] }
      9718 15993 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9718 15993 15997)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8147 p15985 p15993
  have hs15985 : (denoteGraph_ringAttn pm initPM 15985).shape = [2048, 1024] := by
    rw [p15985]; exact hs9717
  have hs15993 : (denoteGraph_ringAttn pm initPM 15993).shape = [2048, 1024] := by
    rw [p15993]; exact hs9718
  have hbr : denoteGraph_ringAttn sm initSM 8147
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15985, denoteGraph_ringAttn pm initPM 15993] := by
    rw [s8147, hg54, ← p15985, ← p15993]
  have hw5355 : denoteGraph_ringAttn sm initSM 5355 = denoteGraph_ringAttn pm initPM 5355 :=
    veq_weight_ring initSM initPM hInit initGoal_5355 (by native_decide) 5355
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5356
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 8147) (denoteGraph_ringAttn sm initSM 5355) :=
    ringAttn_reduce2_pm_opaque sm initSM 513
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8147, 5355], outs := [5356] }
      8147 5355 5356 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 8147 5355 5356)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9721
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15985) (denoteGraph_ringAttn pm initPM 5355) :=
    ringAttn_reduce2_pm_opaque pm initPM 1088
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15985, 5355], outs := [9721] }
      15985 5355 9721 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15985 5355 9721)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9722
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15993) (denoteGraph_ringAttn pm initPM 5355) :=
    ringAttn_reduce2_pm_opaque pm initPM 1089
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15993, 5355], outs := [9722] }
      15993 5355 9722 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15993 5355 9722)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5356
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9721, denoteGraph_ringAttn pm initPM 9722] := by
    rw [rSM, hbr, hw5355, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15985 hs15993,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9721).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15985
  have hsp1 : (denoteGraph_ringAttn pm initPM 9722).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15993
  have hshape : (denoteGraph_ringAttn sm initSM 5356).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5356 5356 9721 9722 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5357 — `FW_float(mref₀(5356))` (SM node 515), the MoE-router input cast.
    Identity cast through the 5-way residual multiref `8158=mref₀(5356)`. -/
theorem recon_intermediateGoal_5357_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5357
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg56, hs9721, hs9722⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8158 : denoteGraph_ringAttn sm initSM 8158 = id (denoteGraph_ringAttn sm initSM 5356) :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8158 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out sm s 0 5356 8158 8162 8166 8170 8174)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16004 : denoteGraph_ringAttn pm initPM 16004 = id (denoteGraph_ringAttn pm initPM 9721) :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16004 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 0 9721 16004 16008 16012 16016 16020)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16027 : denoteGraph_ringAttn pm initPM 16027 = id (denoteGraph_ringAttn pm initPM 9722) :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16027 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => RouterShapesHelpers.applyNode_fw_multiref5_first_out pm s 1 9722 16027 16031 16035 16039 16043)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5357 = id (denoteGraph_ringAttn sm initSM 8158) :=
    ringAttn_reduce1_pm_opaque sm initSM 515
      { rank := 0, op := "OpName.FW_float", ins := [8158], outs := [5357] }
      8158 5357 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 8158 5357 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9723 = id (denoteGraph_ringAttn pm initPM 16004) :=
    ringAttn_reduce1_pm_opaque pm initPM 1092
      { rank := 0, op := "OpName.FW_float", ins := [16004], outs := [9723] }
      16004 9723 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 16004 9723 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9724 = id (denoteGraph_ringAttn pm initPM 16027) :=
    ringAttn_reduce1_pm_opaque pm initPM 1096
      { rank := 1, op := "OpName.FW_float", ins := [16027], outs := [9724] }
      16027 9724 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 16027 9724 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8158 p16004 p16027 rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 5357
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9723, denoteGraph_ringAttn pm initPM 9724] := by
    rw [rSM, s8158, hg56, ← p16004, ← rP0, ← p16027, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9723).shape = [2048, 1024] := by
    rw [rP0, p16004]; exact hs9721
  have hsp1 : (denoteGraph_ringAttn pm initPM 9724).shape = [2048, 1024] := by
    rw [rP1, p16027]; exact hs9722
  have hshape : (denoteGraph_ringAttn sm initSM 5357).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5357 5357 9723 9724 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5359 — `FW_norm_linear(5357, 5358)`, the MoE router logits (SM node 519).
    2-tp dim-0; weight `5358` is the replicated `[64,1024]` router projection. -/
theorem recon_intermediateGoal_5359_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5359
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg57, hs9723, hs9724⟩ := twoTp_gather _ _ intermediateGoal_5357 5357 9723 9724
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5357_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5358 : denoteGraph_ringAttn sm initSM 5358 = denoteGraph_ringAttn pm initPM 5358 :=
    veq_weight_ring initSM initPM hInit initGoal_5358 (by native_decide) 5358
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5358 : (denoteGraph_ringAttn sm initSM 5358).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5358 (by native_decide) 5358 [64, 1024]
      rfl rfl (by native_decide)
  have hspw : (denoteGraph_ringAttn pm initPM 5358).shape = [64, 1024] := by
    rw [← hw5358]; exact hsw5358
  have rSM : denoteGraph_ringAttn sm initSM 5359
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 5357) (denoteGraph_ringAttn sm initSM 5358) :=
    ringAttn_reduce2_pm_opaque sm initSM 519
      { rank := 0, op := "OpName.FW_norm_linear", ins := [5357, 5358], outs := [5359] }
      5357 5358 5359 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 5357 5358 5359)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9729
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9723) (denoteGraph_ringAttn pm initPM 5358) :=
    ringAttn_reduce2_pm_opaque pm initPM 1100
      { rank := 0, op := "OpName.FW_norm_linear", ins := [9723, 5358], outs := [9729] }
      9723 5358 9729 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 9723 5358 9729)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9730
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 9724) (denoteGraph_ringAttn pm initPM 5358) :=
    ringAttn_reduce2_pm_opaque pm initPM 1104
      { rank := 1, op := "OpName.FW_norm_linear", ins := [9724, 5358], outs := [9730] }
      9724 5358 9730 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 9724 5358 9730)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5359
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9729, denoteGraph_ringAttn pm initPM 9730] := by
    rw [rSM, hg57, hw5358, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64 (by omega) (by omega) (by omega)
          hs9723 hs9724 hspw,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9729).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by omega) hs9723 hspw
  have hsp1 : (denoteGraph_ringAttn pm initPM 9730).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by omega) hs9724 hspw
  have hshape : (denoteGraph_ringAttn sm initSM 5359).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5359 5359 9729 9730 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
