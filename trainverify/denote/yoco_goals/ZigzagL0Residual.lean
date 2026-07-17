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

/-- Shape of a broadcast elementwise product `[S,1] * [S,H] = [S,H]`.  Stated on
    abstract tensors so `simp` never tries to `whnf`-reduce an opaque denotation. -/
private theorem elemwiseMul_shape_broadcast_S1 (a c : Tensor) (S H : Nat) (hH : 1 ≤ H)
    (ha : a.shape = [S, 1]) (hc : c.shape = [S, H]) : (elemwiseMul a c).shape = [S, H] := by
  simp [elemwiseMul, Tensor.mkShape, outShape2, ha, hc, Nat.max_eq_right hH]

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

/-- 5366 — `FW_reshape(mref₂(5356))` `[4096,1024]→[4096,1024]` (SM node 516).
    Identity reshape of the expert-input branch read from position 2 of the 5-way
    residual multiref; reconstructs via the row-preserving view commute. -/
theorem recon_intermediateGoal_5366_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5366
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg56, hs9721, hs9722⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8166 : denoteGraph_ringAttn sm initSM 8166 = id (denoteGraph_ringAttn sm initSM 5356) :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8166 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16012 : denoteGraph_ringAttn pm initPM 16012 = id (denoteGraph_ringAttn pm initPM 9721) :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16012 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16035 : denoteGraph_ringAttn pm initPM 16035 = id (denoteGraph_ringAttn pm initPM 9722) :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16035 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8166 p16012 p16035
  have rSM : denoteGraph_ringAttn sm initSM 5366
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 8166) :=
    ringAttn_reshape_reduce_g12 sm initSM 516 0 8166 5366 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9743
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 16012) :=
    ringAttn_reshape_reduce_g12 pm initPM 1093 0 16012 9743 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9744
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 16035) :=
    ringAttn_reshape_reduce_g12 pm initPM 1097 1 16035 9744 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5366
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9743, denoteGraph_ringAttn pm initPM 9744] := by
    rw [rSM, s8166, hg56, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 1024 (by decide) hs9721 hs9722,
        ← p16012, ← p16035, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9743).shape = [2048, 1024] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9744).shape = [2048, 1024] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5366).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5366 5366 9743 9744 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5371 — `FW_reshape(mref₃(5356))` `[4096,1024]→[4096,1024]` (SM node 517).
    Identity reshape of the second expert-input branch (position 3 of the 5-way
    residual multiref). -/
theorem recon_intermediateGoal_5371_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5371
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg56, hs9721, hs9722⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8170 : denoteGraph_ringAttn sm initSM 8170 = id (denoteGraph_ringAttn sm initSM 5356) :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8170 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16016 : denoteGraph_ringAttn pm initPM 16016 = id (denoteGraph_ringAttn pm initPM 9721) :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16016 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16039 : denoteGraph_ringAttn pm initPM 16039 = id (denoteGraph_ringAttn pm initPM 9722) :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16039 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8170 p16016 p16039
  have rSM : denoteGraph_ringAttn sm initSM 5371
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 8170) :=
    ringAttn_reshape_reduce_g12 sm initSM 517 0 8170 5371 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9757
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 16016) :=
    ringAttn_reshape_reduce_g12 pm initPM 1094 0 16016 9757 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9758
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 16039) :=
    ringAttn_reshape_reduce_g12 pm initPM 1098 1 16039 9758 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5371
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9757, denoteGraph_ringAttn pm initPM 9758] := by
    rw [rSM, s8170, hg56, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 1024 (by decide) hs9721 hs9722,
        ← p16016, ← p16039, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9757).shape = [2048, 1024] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9758).shape = [2048, 1024] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5371).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5371 5371 9757 9758 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5375 — `FW_reshape(mref₄(5356))` `[4096,1024]→[4096,1024]` (SM node 518).
    Identity reshape of the third expert-input branch (position 4 of the 5-way
    residual multiref). -/
theorem recon_intermediateGoal_5375_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5375
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg56, hs9721, hs9722⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8174 : denoteGraph_ringAttn sm initSM 8174 = id (denoteGraph_ringAttn sm initSM 5356) :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8174 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16020 : denoteGraph_ringAttn pm initPM 16020 = id (denoteGraph_ringAttn pm initPM 9721) :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16020 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16043 : denoteGraph_ringAttn pm initPM 16043 = id (denoteGraph_ringAttn pm initPM 9722) :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16043 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8174 p16020 p16043
  have rSM : denoteGraph_ringAttn sm initSM 5375
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 8174) :=
    ringAttn_reshape_reduce_g12 sm initSM 518 0 8174 5375 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9775
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 16020) :=
    ringAttn_reshape_reduce_g12 pm initPM 1095 0 16020 9775 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9776
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 16043) :=
    ringAttn_reshape_reduce_g12 pm initPM 1099 1 16043 9776 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5375
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9775, denoteGraph_ringAttn pm initPM 9776] := by
    rw [rSM, s8174, hg56, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 1024 (by decide) hs9721 hs9722,
        ← p16020, ← p16043, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9775).shape = [2048, 1024] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9776).shape = [2048, 1024] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5375).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5375 5375 9775 9776 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5368 — `FW_mix_precision_linear(5366, 5367)` `[4096,1]` gate-projection
    (SM node 520); replicated weight `5367 : [1,1024]`. -/
theorem recon_intermediateGoal_5368_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5368
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg66, hs9743, hs9744⟩ := twoTp_gather _ _ intermediateGoal_5366 5366 9743 9744
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5366_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw : denoteGraph_ringAttn sm initSM 5367 = denoteGraph_ringAttn pm initPM 5367 :=
    veq_weight_ring initSM initPM hInit initGoal_5367 (by native_decide) 5367
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw : (denoteGraph_ringAttn sm initSM 5367).shape = [1, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5367 (by native_decide) 5367 [1, 1024]
      rfl rfl (by native_decide)
  have hspw : (denoteGraph_ringAttn pm initPM 5367).shape = [1, 1024] := by rw [← hw]; exact hsw
  have rSM : denoteGraph_ringAttn sm initSM 5368
      = fw_linear (denoteGraph_ringAttn sm initSM 5366) (denoteGraph_ringAttn sm initSM 5367) :=
    ringAttn_reduce2_pm_opaque sm initSM 520
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5366, 5367], outs := [5368] }
      5366 5367 5368 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5366 5367 5368)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9747
      = fw_linear (denoteGraph_ringAttn pm initPM 9743) (denoteGraph_ringAttn pm initPM 5367) :=
    ringAttn_reduce2_pm_opaque pm initPM 1101
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9743, 5367], outs := [9747] }
      9743 5367 9747 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9743 5367 9747)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9748
      = fw_linear (denoteGraph_ringAttn pm initPM 9744) (denoteGraph_ringAttn pm initPM 5367) :=
    ringAttn_reduce2_pm_opaque pm initPM 1105
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9744, 5367], outs := [9748] }
      9744 5367 9748 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9744 5367 9748)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5368
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9747, denoteGraph_ringAttn pm initPM 9748] := by
    rw [rSM, hg66, hw, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1 (by decide) (by decide)
          (by decide) hs9743 hs9744 hspw, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9747).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9743 hspw
  have hsp1 : (denoteGraph_ringAttn pm initPM 9748).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs9744 hspw
  have hshape : (denoteGraph_ringAttn sm initSM 5368).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5368 5368 9747 9748 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5373 — `FW_mix_precision_linear(5371, 5372)` `[4096,512]` up-branch A
    (SM node 521); replicated weight `5372 : [512,1024]`. -/
theorem recon_intermediateGoal_5373_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5373
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg71, hs9757, hs9758⟩ := twoTp_gather _ _ intermediateGoal_5371 5371 9757 9758
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5371_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw : denoteGraph_ringAttn sm initSM 5372 = denoteGraph_ringAttn pm initPM 5372 :=
    veq_weight_ring initSM initPM hInit initGoal_5372 (by native_decide) 5372
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw : (denoteGraph_ringAttn sm initSM 5372).shape = [512, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5372 (by native_decide) 5372 [512, 1024]
      rfl rfl (by native_decide)
  have hspw : (denoteGraph_ringAttn pm initPM 5372).shape = [512, 1024] := by rw [← hw]; exact hsw
  have rSM : denoteGraph_ringAttn sm initSM 5373
      = fw_linear (denoteGraph_ringAttn sm initSM 5371) (denoteGraph_ringAttn sm initSM 5372) :=
    ringAttn_reduce2_pm_opaque sm initSM 521
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5371, 5372], outs := [5373] }
      5371 5372 5373 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5371 5372 5373)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9761
      = fw_linear (denoteGraph_ringAttn pm initPM 9757) (denoteGraph_ringAttn pm initPM 5372) :=
    ringAttn_reduce2_pm_opaque pm initPM 1102
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9757, 5372], outs := [9761] }
      9757 5372 9761 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9757 5372 9761)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9762
      = fw_linear (denoteGraph_ringAttn pm initPM 9758) (denoteGraph_ringAttn pm initPM 5372) :=
    ringAttn_reduce2_pm_opaque pm initPM 1106
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9758, 5372], outs := [9762] }
      9758 5372 9762 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9758 5372 9762)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5373
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9761, denoteGraph_ringAttn pm initPM 9762] := by
    rw [rSM, hg71, hw, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512 (by decide) (by decide)
          (by decide) hs9757 hs9758 hspw, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9761).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9757 hspw
  have hsp1 : (denoteGraph_ringAttn pm initPM 9762).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9758 hspw
  have hshape : (denoteGraph_ringAttn sm initSM 5373).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5373 5373 9761 9762 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5377 — `FW_mix_precision_linear(5375, 5376)` `[4096,512]` up-branch B
    (SM node 522); replicated weight `5376 : [512,1024]`. -/
theorem recon_intermediateGoal_5377_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5377
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg75, hs9775, hs9776⟩ := twoTp_gather _ _ intermediateGoal_5375 5375 9775 9776
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5375_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw : denoteGraph_ringAttn sm initSM 5376 = denoteGraph_ringAttn pm initPM 5376 :=
    veq_weight_ring initSM initPM hInit initGoal_5376 (by native_decide) 5376
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw : (denoteGraph_ringAttn sm initSM 5376).shape = [512, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5376 (by native_decide) 5376 [512, 1024]
      rfl rfl (by native_decide)
  have hspw : (denoteGraph_ringAttn pm initPM 5376).shape = [512, 1024] := by rw [← hw]; exact hsw
  have rSM : denoteGraph_ringAttn sm initSM 5377
      = fw_linear (denoteGraph_ringAttn sm initSM 5375) (denoteGraph_ringAttn sm initSM 5376) :=
    ringAttn_reduce2_pm_opaque sm initSM 522
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5375, 5376], outs := [5377] }
      5375 5376 5377 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5375 5376 5377)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9779
      = fw_linear (denoteGraph_ringAttn pm initPM 9775) (denoteGraph_ringAttn pm initPM 5376) :=
    ringAttn_reduce2_pm_opaque pm initPM 1103
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9775, 5376], outs := [9779] }
      9775 5376 9779 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9775 5376 9779)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9780
      = fw_linear (denoteGraph_ringAttn pm initPM 9776) (denoteGraph_ringAttn pm initPM 5376) :=
    ringAttn_reduce2_pm_opaque pm initPM 1107
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9776, 5376], outs := [9780] }
      9776 5376 9780 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9776 5376 9780)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5377
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9779, denoteGraph_ringAttn pm initPM 9780] := by
    rw [rSM, hg75, hw, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512 (by decide) (by decide)
          (by decide) hs9775 hs9776 hspw, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9779).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9775 hspw
  have hsp1 : (denoteGraph_ringAttn pm initPM 9780).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs9776 hspw
  have hshape : (denoteGraph_ringAttn sm initSM 5377).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5377 5377 9779 9780 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5369 — `FW_view(5368)` `[4096,1]→[4096,1]` (SM node 524). -/
theorem recon_intermediateGoal_5369_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5369
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg68, hs9747, hs9748⟩ := twoTp_gather _ _ intermediateGoal_5368 5368 9747 9748
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5368_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5369
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 5368) :=
    ringAttn_reduce1_pm_opaque sm initSM 524
      { rank := 0, op := "OpName.FW_view", ins := [5368], outs := [5369], params := [4096, 1] }
      5368 5369 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 5368 5369)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9753
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9747) :=
    ringAttn_reduce1_pm_opaque pm initPM 1109
      { rank := 0, op := "OpName.FW_view", ins := [9747], outs := [9753], params := [2048, 1] }
      9747 9753 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 9747 9753)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9754
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 9748) :=
    ringAttn_reduce1_pm_opaque pm initPM 1113
      { rank := 1, op := "OpName.FW_view", ins := [9748], outs := [9754], params := [2048, 1] }
      9748 9754 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 9748 9754)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5369
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9753, denoteGraph_ringAttn pm initPM 9754] := by
    rw [rSM, hg68, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 1 (by decide) hs9747 hs9748, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9753).shape = [2048, 1] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9754).shape = [2048, 1] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5369).shape = [4096, 1] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5369 5369 9753 9754 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5374 — `FW_view(5373)` `[4096,512]→[4096,512]` (SM node 525). -/
theorem recon_intermediateGoal_5374_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5374
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg73, hs9761, hs9762⟩ := twoTp_gather _ _ intermediateGoal_5373 5373 9761 9762
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5373_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5374
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5373) :=
    ringAttn_reduce1_pm_opaque sm initSM 525
      { rank := 0, op := "OpName.FW_view", ins := [5373], outs := [5374], params := [4096, 512] }
      5373 5374 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5373 5374)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9771
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9761) :=
    ringAttn_reduce1_pm_opaque pm initPM 1110
      { rank := 0, op := "OpName.FW_view", ins := [9761], outs := [9771], params := [2048, 512] }
      9761 9771 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9761 9771)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9772
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9762) :=
    ringAttn_reduce1_pm_opaque pm initPM 1114
      { rank := 1, op := "OpName.FW_view", ins := [9762], outs := [9772], params := [2048, 512] }
      9762 9772 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9762 9772)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5374
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9771, denoteGraph_ringAttn pm initPM 9772] := by
    rw [rSM, hg73, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 512 (by decide) hs9761 hs9762, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9771).shape = [2048, 512] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9772).shape = [2048, 512] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5374).shape = [4096, 512] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5374 5374 9771 9772 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5378 — `FW_view(5377)` `[4096,512]→[4096,512]` (SM node 526). -/
theorem recon_intermediateGoal_5378_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5378
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg77, hs9779, hs9780⟩ := twoTp_gather _ _ intermediateGoal_5377 5377 9779 9780
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5377_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5378
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5377) :=
    ringAttn_reduce1_pm_opaque sm initSM 526
      { rank := 0, op := "OpName.FW_view", ins := [5377], outs := [5378], params := [4096, 512] }
      5377 5378 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 5377 5378)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9789
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9779) :=
    ringAttn_reduce1_pm_opaque pm initPM 1111
      { rank := 0, op := "OpName.FW_view", ins := [9779], outs := [9789], params := [2048, 512] }
      9779 9789 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 9779 9789)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9790
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9780) :=
    ringAttn_reduce1_pm_opaque pm initPM 1115
      { rank := 1, op := "OpName.FW_view", ins := [9780], outs := [9790], params := [2048, 512] }
      9780 9790 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 9780 9790)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5378
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9789, denoteGraph_ringAttn pm initPM 9790] := by
    rw [rSM, hg77, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 512 (by decide) hs9779 hs9780, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9789).shape = [2048, 512] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9790).shape = [2048, 512] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5378).shape = [4096, 512] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5378 5378 9789 9790 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5370 — `FW_sigmoid(5369)` `[4096,1]` expert gate (SM node 528). -/
theorem recon_intermediateGoal_5370_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5370
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg69, hs9753, hs9754⟩ := twoTp_gather _ _ intermediateGoal_5369 5369 9753 9754
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5369_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5370 = fw_sigmoid (denoteGraph_ringAttn sm initSM 5369) :=
    ringAttn_reduce1_pm_opaque sm initSM 528
      { rank := 0, op := "OpName.FW_sigmoid", ins := [5369], outs := [5370] }
      5369 5370 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out_1p sm s 0 5369 5370)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9755 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9753) :=
    ringAttn_reduce1_pm_opaque pm initPM 1117
      { rank := 0, op := "OpName.FW_sigmoid", ins := [9753], outs := [9755] }
      9753 9755 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out_1p pm s 0 9753 9755)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9756 = fw_sigmoid (denoteGraph_ringAttn pm initPM 9754) :=
    ringAttn_reduce1_pm_opaque pm initPM 1120
      { rank := 1, op := "OpName.FW_sigmoid", ins := [9754], outs := [9756] }
      9754 9756 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out_1p pm s 1 9754 9756)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5370
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9755, denoteGraph_ringAttn pm initPM 9756] := by
    rw [rSM, hg69, hnr,
        fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs9753 hs9754, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9755).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs9753
  have hsp1 : (denoteGraph_ringAttn pm initPM 9756).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs9754
  have hshape : (denoteGraph_ringAttn sm initSM 5370).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5370 5370 9755 9756 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5379 — `FW_swiglu(5374, 5378)` `[4096,512]` gated expert activation (SM node 529). -/
theorem recon_intermediateGoal_5379_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5379
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg74, hs9771, hs9772⟩ := twoTp_gather _ _ intermediateGoal_5374 5374 9771 9772
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5374_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hg78, hs9789, hs9790⟩ := twoTp_gather _ _ intermediateGoal_5378 5378 9789 9790
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5378_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5379
      = fw_swiglu (denoteGraph_ringAttn sm initSM 5374) (denoteGraph_ringAttn sm initSM 5378) :=
    ringAttn_reduce2_pm_opaque sm initSM 529
      { rank := 0, op := "OpName.FW_swiglu", ins := [5374, 5378], outs := [5379] }
      5374 5378 5379 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out_1p sm s 0 5374 5378 5379)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9793
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9771) (denoteGraph_ringAttn pm initPM 9789) :=
    ringAttn_reduce2_pm_opaque pm initPM 1118
      { rank := 0, op := "OpName.FW_swiglu", ins := [9771, 9789], outs := [9793] }
      9771 9789 9793 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out_1p pm s 0 9771 9789 9793)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9794
      = fw_swiglu (denoteGraph_ringAttn pm initPM 9772) (denoteGraph_ringAttn pm initPM 9790) :=
    ringAttn_reduce2_pm_opaque pm initPM 1121
      { rank := 1, op := "OpName.FW_swiglu", ins := [9772, 9790], outs := [9794] }
      9772 9790 9794 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out_1p pm s 1 9772 9790 9794)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5379
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9793, denoteGraph_ringAttn pm initPM 9794] := by
    rw [rSM, hg74, hg78, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
          hs9771 hs9772 hs9789 hs9790, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9793).shape = [2048, 512] := by
    rw [rP0, fw_swiglu_shape]; exact hs9789
  have hsp1 : (denoteGraph_ringAttn pm initPM 9794).shape = [2048, 512] := by
    rw [rP1, fw_swiglu_shape]; exact hs9790
  have hshape : (denoteGraph_ringAttn sm initSM 5379).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5379 5379 9793 9794 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5380 — `FW_reshape(5379)` `[4096,512]→[4096,512]` (SM node 530). -/
theorem recon_intermediateGoal_5380_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5380
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg79, hs9793, hs9794⟩ := twoTp_gather _ _ intermediateGoal_5379 5379 9793 9794
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5379_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5380
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 5379) :=
    ringAttn_reshape_reduce_g12 sm initSM 530 0 5379 5380 [4096, 512] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9795
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9793) :=
    ringAttn_reshape_reduce_g12 pm initPM 1122 0 9793 9795 [2048, 512] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9796
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 9794) :=
    ringAttn_reshape_reduce_g12 pm initPM 1123 1 9794 9796 [2048, 512] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5380
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9795, denoteGraph_ringAttn pm initPM 9796] := by
    rw [rSM, hg79, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 512 (by decide) hs9793 hs9794, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9795).shape = [2048, 512] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9796).shape = [2048, 512] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5380).shape = [4096, 512] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5380 5380 9795 9796 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5382 — `FW_mix_precision_linear(5380, 5381)` `[4096,1024]` expert down-projection
    (SM node 531); replicated weight `5381 : [1024,512]`. -/
theorem recon_intermediateGoal_5382_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5382
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg80, hs9795, hs9796⟩ := twoTp_gather _ _ intermediateGoal_5380 5380 9795 9796
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5380_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw : denoteGraph_ringAttn sm initSM 5381 = denoteGraph_ringAttn pm initPM 5381 :=
    veq_weight_ring initSM initPM hInit initGoal_5381 (by native_decide) 5381
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw : (denoteGraph_ringAttn sm initSM 5381).shape = [1024, 512] :=
    shape_weight_ring initSM initPM hInit initGoal_5381 (by native_decide) 5381 [1024, 512]
      rfl rfl (by native_decide)
  have hspw : (denoteGraph_ringAttn pm initPM 5381).shape = [1024, 512] := by rw [← hw]; exact hsw
  have rSM : denoteGraph_ringAttn sm initSM 5382
      = fw_linear (denoteGraph_ringAttn sm initSM 5380) (denoteGraph_ringAttn sm initSM 5381) :=
    ringAttn_reduce2_pm_opaque sm initSM 531
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5380, 5381], outs := [5382] }
      5380 5381 5382 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 5380 5381 5382)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9801
      = fw_linear (denoteGraph_ringAttn pm initPM 9795) (denoteGraph_ringAttn pm initPM 5381) :=
    ringAttn_reduce2_pm_opaque pm initPM 1124
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9795, 5381], outs := [9801] }
      9795 5381 9801 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 9795 5381 9801)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9802
      = fw_linear (denoteGraph_ringAttn pm initPM 9796) (denoteGraph_ringAttn pm initPM 5381) :=
    ringAttn_reduce2_pm_opaque pm initPM 1125
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9796, 5381], outs := [9802] }
      9796 5381 9802 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 9796 5381 9802)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5382
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9801, denoteGraph_ringAttn pm initPM 9802] := by
    rw [rSM, hg80, hw, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024 (by decide) (by decide)
          (by decide) hs9795 hs9796 hspw, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9801).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9795 hspw
  have hsp1 : (denoteGraph_ringAttn pm initPM 9802).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs9796 hspw
  have hshape : (denoteGraph_ringAttn sm initSM 5382).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5382 5382 9801 9802 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5383 — `FW_view(5382)` `[4096,1024]→[4096,1024]` (SM node 532). -/
theorem recon_intermediateGoal_5383_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5383
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg82, hs9801, hs9802⟩ := twoTp_gather _ _ intermediateGoal_5382 5382 9801 9802
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5382_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5383
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 5382) :=
    ringAttn_reduce1_pm_opaque sm initSM 532
      { rank := 0, op := "OpName.FW_view", ins := [5382], outs := [5383], params := [4096, 1024] }
      5382 5383 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 5382 5383)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9811
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9801) :=
    ringAttn_reduce1_pm_opaque pm initPM 1126
      { rank := 0, op := "OpName.FW_view", ins := [9801], outs := [9811], params := [2048, 1024] }
      9801 9811 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 9801 9811)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9812
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 9802) :=
    ringAttn_reduce1_pm_opaque pm initPM 1127
      { rank := 1, op := "OpName.FW_view", ins := [9802], outs := [9812], params := [2048, 1024] }
      9802 9812 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 9802 9812)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5383
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9811, denoteGraph_ringAttn pm initPM 9812] := by
    rw [rSM, hg82, hnr,
        fw_view_allGather0_commute_2_of _ _ 2048 1024 (by decide) hs9801 hs9802, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9811).shape = [2048, 1024] := by rw [rP0]; rfl
  have hsp1 : (denoteGraph_ringAttn pm initPM 9812).shape = [2048, 1024] := by rw [rP1]; rfl
  have hshape : (denoteGraph_ringAttn sm initSM 5383).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5383 5383 9811 9812 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5384 — `FW_mul(5370, 5383)` `[4096,1024]` broadcast gate×down (SM node 533).
    Gate `5370 : [4096,1]` broadcasts over down-projection `5383 : [4096,1024]`. -/
theorem recon_intermediateGoal_5384_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5384
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg70, hs9755, hs9756⟩ := twoTp_gather _ _ intermediateGoal_5370 5370 9755 9756
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5370_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hg83, hs9811, hs9812⟩ := twoTp_gather _ _ intermediateGoal_5383 5383 9811 9812
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5383_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5384
      = elemwiseMul (denoteGraph_ringAttn sm initSM 5370) (denoteGraph_ringAttn sm initSM 5383) :=
    ringAttn_reduce2_pm_opaque sm initSM 533
      { rank := 0, op := "OpName.FW_mul", ins := [5370, 5383], outs := [5384] }
      5370 5383 5384 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 5370 5383 5384)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9815
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9755) (denoteGraph_ringAttn pm initPM 9811) :=
    ringAttn_reduce2_pm_opaque pm initPM 1128
      { rank := 0, op := "OpName.FW_mul", ins := [9755, 9811], outs := [9815] }
      9755 9811 9815 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 9755 9811 9815)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9816
      = elemwiseMul (denoteGraph_ringAttn pm initPM 9756) (denoteGraph_ringAttn pm initPM 9812) :=
    ringAttn_reduce2_pm_opaque pm initPM 1129
      { rank := 1, op := "OpName.FW_mul", ins := [9756, 9812], outs := [9816] }
      9756 9812 9816 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 9756 9812 9816)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5384
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9815, denoteGraph_ringAttn pm initPM 9816] := by
    rw [rSM, hg70, hg83, hnr,
        fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024 (by omega) (by omega)
          (by decide) (by decide) (by decide) hs9755 hs9756 hs9811 hs9812, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9815).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseMul_shape_broadcast_S1 _ _ 2048 1024 (by omega) hs9755 hs9811
  have hsp1 : (denoteGraph_ringAttn pm initPM 9816).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseMul_shape_broadcast_S1 _ _ 2048 1024 (by omega) hs9756 hs9812
  have hshape : (denoteGraph_ringAttn sm initSM 5384).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5384 5384 9815 9816 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5360 — `FW_topk_routing(5359).fst` routing-probs `[4096,64]` (SM node 523,
    params `[8,1]`, numExperts read from logits trailing dim 64). -/
theorem recon_intermediateGoal_5360_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5360
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg59, hs9729, hs9730⟩ := twoTp_gather _ _ intermediateGoal_5359 5359 9729 9730
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5359_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5359sm : (denoteGraph_ringAttn sm initSM 5359).shape = [4096, 64] := by
    rw [hg59, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs9729])]
    simp [List.set, List.getD]
  have hpreSM : denoteGraph_ringAttn sm initSM 5359
      = (sm.nodes.take 523).foldl (applyNodeRingAttn sm) initSM 5359 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5359 523 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 523).foldl (applyNodeRingAttn sm) initSM 5359).shape.reverse.head?
      = some 64 := by rw [← hpreSM, hs5359sm]; rfl
  have hpreP0 : denoteGraph_ringAttn pm initPM 9729
      = (pm.nodes.take 1108).foldl (applyNodeRingAttn pm) initPM 9729 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9729 1108 (by native_decide) (by native_decide)
  have hlastP0 : ((pm.nodes.take 1108).foldl (applyNodeRingAttn pm) initPM 9729).shape.reverse.head?
      = some 64 := by rw [← hpreP0, hs9729]; rfl
  have hpreP1 : denoteGraph_ringAttn pm initPM 9730
      = (pm.nodes.take 1112).foldl (applyNodeRingAttn pm) initPM 9730 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9730 1112 (by native_decide) (by native_decide)
  have hlastP1 : ((pm.nodes.take 1112).foldl (applyNodeRingAttn pm) initPM 9730).shape.reverse.head?
      = some 64 := by rw [← hpreP1, hs9730]; rfl
  have rSM : denoteGraph_ringAttn sm initSM 5360
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5359) 8 64).1 :=
    ringAttn_reduce1_at sm initSM 523
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360, 5361, 5362], params := [8, 1] }
      5359 5360 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 523).foldl (applyNodeRingAttn sm) initSM) 0 5359 5360 5361 5362 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9731
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9729) 8 64).1 :=
    ringAttn_reduce1_at pm initPM 1108
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731, 9733, 9735], params := [8, 1] }
      9729 9731 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 1108).foldl (applyNodeRingAttn pm) initPM) 0 9729 9731 9733 9735 hlastP0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9732
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9730) 8 64).1 :=
    ringAttn_reduce1_at pm initPM 1112
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732, 9734, 9736], params := [8, 1] }
      9730 9732 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 1112).foldl (applyNodeRingAttn pm) initPM) 0 9730 9732 9734 9736 hlastP1)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5360
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9731, denoteGraph_ringAttn pm initPM 9732] := by
    rw [rSM, hg59, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9729 hs9730,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5360).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs5359sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9731).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9729]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9732).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs9730]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5360 5360 9731 9732 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5361 — `FW_topk_routing(5359).snd.fst` routing-map `[4096,64]` (SM node 523). -/
theorem recon_intermediateGoal_5361_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5361
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg59, hs9729, hs9730⟩ := twoTp_gather _ _ intermediateGoal_5359 5359 9729 9730
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5359_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs5359sm : (denoteGraph_ringAttn sm initSM 5359).shape = [4096, 64] := by
    rw [hg59, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs9729])]
    simp [List.set, List.getD]
  have hpreSM : denoteGraph_ringAttn sm initSM 5359
      = (sm.nodes.take 523).foldl (applyNodeRingAttn sm) initSM 5359 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 5359 523 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 523).foldl (applyNodeRingAttn sm) initSM 5359).shape.reverse.head?
      = some 64 := by rw [← hpreSM, hs5359sm]; rfl
  have hpreP0 : denoteGraph_ringAttn pm initPM 9729
      = (pm.nodes.take 1108).foldl (applyNodeRingAttn pm) initPM 9729 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9729 1108 (by native_decide) (by native_decide)
  have hlastP0 : ((pm.nodes.take 1108).foldl (applyNodeRingAttn pm) initPM 9729).shape.reverse.head?
      = some 64 := by rw [← hpreP0, hs9729]; rfl
  have hpreP1 : denoteGraph_ringAttn pm initPM 9730
      = (pm.nodes.take 1112).foldl (applyNodeRingAttn pm) initPM 9730 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 9730 1112 (by native_decide) (by native_decide)
  have hlastP1 : ((pm.nodes.take 1112).foldl (applyNodeRingAttn pm) initPM 9730).shape.reverse.head?
      = some 64 := by rw [← hpreP1, hs9730]; rfl
  have rSM : denoteGraph_ringAttn sm initSM 5361
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 5359) 8 64).2.1 :=
    ringAttn_reduce1_at sm initSM 523
      { rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360, 5361, 5362], params := [8, 1] }
      5359 5361 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 523).foldl (applyNodeRingAttn sm) initSM) 0 5359 5360 5361 5362 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9733
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9729) 8 64).2.1 :=
    ringAttn_reduce1_at pm initPM 1108
      { rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731, 9733, 9735], params := [8, 1] }
      9729 9733 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 1108).foldl (applyNodeRingAttn pm) initPM) 0 9729 9731 9733 9735 (by decide) hlastP0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9734
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 9730) 8 64).2.1 :=
    ringAttn_reduce1_at pm initPM 1112
      { rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732, 9734, 9736], params := [8, 1] }
      9730 9734 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 1112).foldl (applyNodeRingAttn pm) initPM) 0 9730 9732 9734 9736 (by decide) hlastP1)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5361
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9733, denoteGraph_ringAttn pm initPM 9734] := by
    rw [rSM, hg59, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs9729 hs9730,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5361).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs5359sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 9733).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9729]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9734).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs9730]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5361 5361 9733 9734 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 5365 — cross-decoder layer-0 expert-parallel MoE all2all (2-tp, expert-sharded).
    `SM 5365 = fw_all2all_moe_gmm` over experts `[0,64)` (SM node 527, params
    `[64,0,64,8]`).  PM shards experts across 2 ranks: rank 0 → `[0,32)` (`9741`,
    node 1116), rank 1 → `[32,64)` (`9742`, node 1119), reconstructed via
    `fw_all2all_moe_gmm_split_commute_2_of` given the per-rank routing maps
    `9733`/`9734` are expert-local (the `wf5365_hdisjA/B` harness invariants,
    same class as `wf5308_hdisjA/B`).  Token input `8162 = mref5-pos1(5356)`
    (SM node 514, PM nodes 1090/1091); routing-probs `5360` (PM `9731`/`9732`),
    routing-map `5361` (PM `9733`/`9734`), expert weights `5363`/`5364`. -/
theorem recon_intermediateGoal_5365_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5365
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 8162 = mref5-pos1(5356).
  obtain ⟨hbr13, hs9721, hs9722⟩ := twoTp_gather _ _ intermediateGoal_5356 5356 9721 9722
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5356_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8162 : denoteGraph_ringAttn sm initSM 8162 = id (denoteGraph_ringAttn sm initSM 5356) :=
    ringAttn_reduce1_pm_opaque sm initSM 514
      { rank := 0, op := "OpName.FW_multiref", ins := [5356],
        outs := [8158, 8162, 8166, 8170, 8174], params := [5] }
      5356 8162 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 5356 8158 8162 8166 8170 8174 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16008 : denoteGraph_ringAttn pm initPM 16008 = id (denoteGraph_ringAttn pm initPM 9721) :=
    ringAttn_reduce1_pm_opaque pm initPM 1090
      { rank := 0, op := "OpName.FW_multiref", ins := [9721],
        outs := [16004, 16008, 16012, 16016, 16020], params := [5] }
      9721 16008 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 9721 16004 16008 16012 16016 16020 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16031 : denoteGraph_ringAttn pm initPM 16031 = id (denoteGraph_ringAttn pm initPM 9722) :=
    ringAttn_reduce1_pm_opaque pm initPM 1091
      { rank := 1, op := "OpName.FW_multiref", ins := [9722],
        outs := [16027, 16031, 16035, 16039, 16043], params := [5] }
      9722 16031 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 9722 16027 16031 16035 16039 16043 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8162 p16008 p16031
  have hsInA : (denoteGraph_ringAttn pm initPM 16008).shape = [2048, 1024] := by
    rw [p16008]; exact hs9721
  have hsInB : (denoteGraph_ringAttn pm initPM 16031).shape = [2048, 1024] := by
    rw [p16031]; exact hs9722
  have hbrIn : denoteGraph_ringAttn sm initSM 8162
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 16008, denoteGraph_ringAttn pm initPM 16031] := by
    rw [s8162, hbr13, hnr, ← p16008, ← p16031]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_5360 5360 9731 9732
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5360_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_5361 5361 9733 9734
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5361_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 5360
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9731, denoteGraph_ringAttn pm initPM 9732] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 5361
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 9733, denoteGraph_ringAttn pm initPM 9734] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_5363
    (by native_decide) 5363 9737 9738 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_5364
    (by native_decide) 5364 9739 9740 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 9737).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5363 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5363, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9737 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 9738).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_5363 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5363, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9738 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 9739).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5364 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5364, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9739 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 9740).shape = [32, 1024, 512] := by
    have h := hpres initGoal_5364 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_5364, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 9740 (by native_decide)]; exact hs.2
  -- SM 5365 = full-range all2all (SM node 527).
  have hSMout : denoteGraph_ringAttn sm initSM 5365
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 8162)
          (denoteGraph_ringAttn sm initSM 5360) (denoteGraph_ringAttn sm initSM 5361)
          (denoteGraph_ringAttn sm initSM 5363) (denoteGraph_ringAttn sm initSM 5364)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 527
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8162, 5360, 5361, 5363, 5364],
        outs := [5365], params := [64, 0, 64, 8] }
      8162 5360 5361 5363 5364 5365
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 8162 5360 5361 5363 5364 5365 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9741 = rank-0 sharded-range all2all (PM node 1116).
  have hP0 : denoteGraph_ringAttn pm initPM 9741
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 16008)
          (denoteGraph_ringAttn pm initPM 9731) (denoteGraph_ringAttn pm initPM 9733)
          (denoteGraph_ringAttn pm initPM 9737) (denoteGraph_ringAttn pm initPM 9739)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 1116
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16008, 9731, 9733, 9737, 9739],
        outs := [9741], params := [64, 0, 32, 8] }
      16008 9731 9733 9737 9739 9741
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 16008 9731 9733 9737 9739 9741 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 9742 = rank-1 sharded-range all2all (PM node 1119).
  have hP1 : denoteGraph_ringAttn pm initPM 9742
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 16031)
          (denoteGraph_ringAttn pm initPM 9732) (denoteGraph_ringAttn pm initPM 9734)
          (denoteGraph_ringAttn pm initPM 9738) (denoteGraph_ringAttn pm initPM 9740)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 1119
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16031, 9732, 9734, 9738, 9740],
        outs := [9742], params := [64, 32, 64, 8] }
      16031 9732 9734 9738 9740 9742
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 16031 9732 9734 9738 9740 9742 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 16008) (denoteGraph_ringAttn pm initPM 16031)
      (denoteGraph_ringAttn pm initPM 9731) (denoteGraph_ringAttn pm initPM 9732)
      (denoteGraph_ringAttn pm initPM 9733) (denoteGraph_ringAttn pm initPM 9734)
      (denoteGraph_ringAttn pm initPM 9737) (denoteGraph_ringAttn pm initPM 9738)
      (denoteGraph_ringAttn pm initPM 9739) (denoteGraph_ringAttn pm initPM 9740)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf5365_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf5365_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 5365
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9741, denoteGraph_ringAttn pm initPM 9742] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9741).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 9742).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 5365).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5365 5365 9741 9742 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 8151 — second position of the layer-0 post-MoE residual `mref2(5354)` (2-tp,
    PM shards `15989`/`15997`; SM node 512, PM nodes 1086/1087). -/
theorem recon_intermediateGoal_8151_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_8151
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr, hs9717, hs9718⟩ := twoTp_gather _ _ intermediateGoal_5354 5354 9717 9718
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5354_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 8151 = id (denoteGraph_ringAttn sm initSM 5354) :=
    ringAttn_reduce1_pm_opaque sm initSM 512
      { rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151], params := [2] }
      5354 8151 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5354 8147 8151 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 15989 = id (denoteGraph_ringAttn pm initPM 9717) :=
    ringAttn_reduce1_pm_opaque pm initPM 1086
      { rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989], params := [2] }
      9717 15989 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9717 15985 15989 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 15997 = id (denoteGraph_ringAttn pm initPM 9718) :=
    ringAttn_reduce1_pm_opaque pm initPM 1087
      { rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997], params := [2] }
      9718 15997 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9718 15993 15997 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hsp0 : (denoteGraph_ringAttn pm initPM 15989).shape = [2048, 1024] := by rw [rP0]; exact hs9717
  have hsp1 : (denoteGraph_ringAttn pm initPM 15997).shape = [2048, 1024] := by rw [rP1]; exact hs9718
  have hval : denoteGraph_ringAttn sm initSM 8151
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15989, denoteGraph_ringAttn pm initPM 15997] := by
    rw [rSM, hbr, hnr, ← rP0, ← rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 8151).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_8151 8151 15989 15997 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5385 — post-MoE residual add `5365 + 5384` (2-tp, PM `9819`/`9820`). -/
theorem recon_intermediateGoal_5385_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5385
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbrA, hs9741, hs9742⟩ := twoTp_gather _ _ intermediateGoal_5365 5365 9741 9742
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5365_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrB, hs9815, hs9816⟩ := twoTp_gather _ _ intermediateGoal_5384 5384 9815 9816
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5384_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5385
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 5365) (denoteGraph_ringAttn sm initSM 5384) :=
    ringAttn_reduce2_pm_opaque sm initSM 534
      { rank := 0, op := "OpName.FW_add", ins := [5365, 5384], outs := [5385] }
      5365 5384 5385 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 5365 5384 5385)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9819
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9741) (denoteGraph_ringAttn pm initPM 9815) :=
    ringAttn_reduce2_pm_opaque pm initPM 1130
      { rank := 0, op := "OpName.FW_add", ins := [9741, 9815], outs := [9819] }
      9741 9815 9819 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 9741 9815 9819)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9820
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 9742) (denoteGraph_ringAttn pm initPM 9816) :=
    ringAttn_reduce2_pm_opaque pm initPM 1131
      { rank := 1, op := "OpName.FW_add", ins := [9742, 9816], outs := [9820] }
      9742 9816 9820 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 9742 9816 9820)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5385
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9819, denoteGraph_ringAttn pm initPM 9820] := by
    rw [rSM, hbrA, hbrB, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs9741 hs9742 hs9815 hs9816,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9819).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9741 hs9815
  have hsp1 : (denoteGraph_ringAttn pm initPM 9820).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs9742 hs9816
  have hshape : (denoteGraph_ringAttn sm initSM 5385).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5385 5385 9819 9820 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5386 — `FW_float(5385)` (identity, 2-tp PM `9825`/`9826`). -/
theorem recon_intermediateGoal_5386_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5386
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr, hs9819, hs9820⟩ := twoTp_gather _ _ intermediateGoal_5385 5385 9819 9820
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5385_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5386 = id (denoteGraph_ringAttn sm initSM 5385) :=
    ringAttn_reduce1_pm_opaque sm initSM 535
      { rank := 0, op := "OpName.FW_float", ins := [5385], outs := [5386] }
      5385 5386 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 5385 5386 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9825 = id (denoteGraph_ringAttn pm initPM 9819) :=
    ringAttn_reduce1_pm_opaque pm initPM 1132
      { rank := 0, op := "OpName.FW_float", ins := [9819], outs := [9825] }
      9819 9825 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 9819 9825 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9826 = id (denoteGraph_ringAttn pm initPM 9820) :=
    ringAttn_reduce1_pm_opaque pm initPM 1133
      { rank := 1, op := "OpName.FW_float", ins := [9820], outs := [9826] }
      9820 9826 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 9820 9826 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hsp0 : (denoteGraph_ringAttn pm initPM 9825).shape = [2048, 1024] := by rw [rP0]; exact hs9819
  have hsp1 : (denoteGraph_ringAttn pm initPM 9826).shape = [2048, 1024] := by rw [rP1]; exact hs9820
  have hval : denoteGraph_ringAttn sm initSM 5386
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9825, denoteGraph_ringAttn pm initPM 9826] := by
    rw [rSM, hbr, ← rP0, ← rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 5386).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5386 5386 9825 9826 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5387 — cross-block residual add `8151 + 5386` (2-tp, PM `9829`/`9830`). -/
theorem recon_intermediateGoal_5387_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5387
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbrA, hs15989, hs15997⟩ := twoTp_gather _ _ intermediateGoal_8151 8151 15989 15997
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_8151_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrB, hs9825, hs9826⟩ := twoTp_gather _ _ intermediateGoal_5386 5386 9825 9826
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5386_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 5387
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 8151) (denoteGraph_ringAttn sm initSM 5386) :=
    ringAttn_reduce2_pm_opaque sm initSM 536
      { rank := 0, op := "OpName.FW_add", ins := [8151, 5386], outs := [5387] }
      8151 5386 5387 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 8151 5386 5387)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9829
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15989) (denoteGraph_ringAttn pm initPM 9825) :=
    ringAttn_reduce2_pm_opaque pm initPM 1134
      { rank := 0, op := "OpName.FW_add", ins := [15989, 9825], outs := [9829] }
      15989 9825 9829 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 15989 9825 9829)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9830
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 15997) (denoteGraph_ringAttn pm initPM 9826) :=
    ringAttn_reduce2_pm_opaque pm initPM 1135
      { rank := 1, op := "OpName.FW_add", ins := [15997, 9826], outs := [9830] }
      15997 9826 9830 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 15997 9826 9830)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5387
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9829, denoteGraph_ringAttn pm initPM 9830] := by
    rw [rSM, hbrA, hbrB, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs15989 hs15997 hs9825 hs9826,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9829).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15989 hs9825
  have hsp1 : (denoteGraph_ringAttn pm initPM 9830).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs15997 hs9826
  have hshape : (denoteGraph_ringAttn sm initSM 5387).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5387 5387 9829 9830 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5389 — layer-0 next-block RMSNorm `fw_rms_norm(mref2₀(5387), 5388)`
    (2-tp, PM `9833`/`9834`; weight `5388 : [1024]` replicated).  `8178 =
    mref2-pos0(5387)` inlined (SM node 537, PM nodes 1136/1137); rms_norm SM
    node 538, PM nodes 1138/1139. -/
theorem recon_intermediateGoal_5389_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5389
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr87, hs9829, hs9830⟩ := twoTp_gather _ _ intermediateGoal_5387 5387 9829 9830
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5387_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8178 : denoteGraph_ringAttn sm initSM 8178 = id (denoteGraph_ringAttn sm initSM 5387) :=
    ringAttn_reduce1_pm_opaque sm initSM 537
      { rank := 0, op := "OpName.FW_multiref", ins := [5387], outs := [8178, 8182], params := [2] }
      5387 8178 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5387 8178 8182)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16047 : denoteGraph_ringAttn pm initPM 16047 = id (denoteGraph_ringAttn pm initPM 9829) :=
    ringAttn_reduce1_pm_opaque pm initPM 1136
      { rank := 0, op := "OpName.FW_multiref", ins := [9829], outs := [16047, 16051], params := [2] }
      9829 16047 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9829 16047 16051)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p16055 : denoteGraph_ringAttn pm initPM 16055 = id (denoteGraph_ringAttn pm initPM 9830) :=
    ringAttn_reduce1_pm_opaque pm initPM 1137
      { rank := 1, op := "OpName.FW_multiref", ins := [9830], outs := [16055, 16059], params := [2] }
      9830 16055 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9830 16055 16059)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8178 p16047 p16055
  have hs16047 : (denoteGraph_ringAttn pm initPM 16047).shape = [2048, 1024] := by
    rw [p16047]; exact hs9829
  have hs16055 : (denoteGraph_ringAttn pm initPM 16055).shape = [2048, 1024] := by
    rw [p16055]; exact hs9830
  have hbrIn : denoteGraph_ringAttn sm initSM 8178
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 16047, denoteGraph_ringAttn pm initPM 16055] := by
    rw [s8178, hbr87, ← p16047, ← p16055]
  have hw5388 : denoteGraph_ringAttn sm initSM 5388 = denoteGraph_ringAttn pm initPM 5388 :=
    veq_weight_ring initSM initPM hInit initGoal_5388 (by native_decide) 5388
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5389
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 8178) (denoteGraph_ringAttn sm initSM 5388) :=
    ringAttn_reduce2_pm_opaque sm initSM 538
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8178, 5388], outs := [5389] }
      8178 5388 5389 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 8178 5388 5389)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9833
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 16047) (denoteGraph_ringAttn pm initPM 5388) :=
    ringAttn_reduce2_pm_opaque pm initPM 1138
      { rank := 0, op := "OpName.FW_rms_norm", ins := [16047, 5388], outs := [9833] }
      16047 5388 9833 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 16047 5388 9833)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9834
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 16055) (denoteGraph_ringAttn pm initPM 5388) :=
    ringAttn_reduce2_pm_opaque pm initPM 1139
      { rank := 1, op := "OpName.FW_rms_norm", ins := [16055, 5388], outs := [9834] }
      16055 5388 9834 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 16055 5388 9834)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5389
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9833, denoteGraph_ringAttn pm initPM 9834] := by
    rw [rSM, hbrIn, hw5388, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs16047 hs16055,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9833).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs16047
  have hsp1 : (denoteGraph_ringAttn pm initPM 9834).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs16055
  have hshape : (denoteGraph_ringAttn sm initSM 5389).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5389 5389 9833 9834 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5391 — layer-0 next-block per-head Q projection
    `fw_per_head_linear(5389, 5390)` (2-tp, PM `9835`/`9836`; weight
    `5390 : [16,64,1024]` replicated).  SM node 539, PM nodes 1140/1141.
    This is the Q input of the next zigzag entry `5396`. -/
theorem recon_intermediateGoal_5391_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5391
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr89, hs9833, hs9834⟩ := twoTp_gather _ _ intermediateGoal_5389 5389 9833 9834
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5389_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5390 : denoteGraph_ringAttn sm initSM 5390 = denoteGraph_ringAttn pm initPM 5390 :=
    veq_weight_ring initSM initPM hInit initGoal_5390 (by native_decide) 5390
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5390 : (denoteGraph_ringAttn sm initSM 5390).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5390 (by native_decide) 5390 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw5390 : (denoteGraph_ringAttn pm initPM 5390).shape = [16, 64, 1024] := by
    rw [← hw5390]; exact hsw5390
  have rSM : denoteGraph_ringAttn sm initSM 5391
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 5389) (denoteGraph_ringAttn sm initSM 5390) :=
    ringAttn_reduce2_pm_opaque sm initSM 539
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5389, 5390], outs := [5391] }
      5389 5390 5391 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 5389 5390 5391 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9835
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 9833) (denoteGraph_ringAttn pm initPM 5390) :=
    ringAttn_reduce2_pm_opaque pm initPM 1140
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9833, 5390], outs := [9835] }
      9833 5390 9835 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 9833 5390 9835 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9836
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 9834) (denoteGraph_ringAttn pm initPM 5390) :=
    ringAttn_reduce2_pm_opaque pm initPM 1141
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9834, 5390], outs := [9836] }
      9834 5390 9836 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 9834 5390 9836 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5391
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9835, denoteGraph_ringAttn pm initPM 9836] := by
    rw [rSM, hbr89, hw5390, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs9833 hs9834 hpw5390,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9835).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs9833 hpw5390
  have hsp1 : (denoteGraph_ringAttn pm initPM 9836).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs9834 hpw5390
  have hshape : (denoteGraph_ringAttn sm initSM 5391).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_5391 5391 9835 9836 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
