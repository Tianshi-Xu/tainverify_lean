/- Worker #24 — Layer-12 BOUNDARY maybe-shuffle branch (2-tp sharded).

   The second global-cache branch of the YOCO cross-decoder transition.  Unlike
   the K/V cache (`5332..5344`, replicated), this branch stays genuinely 2-tp
   sharded along dim 0 (the sequence): `5338 / 5340 / 5342`
   (`tps = [{0, tid₀}, {1, tid₁}]`, shard `[2048, …]`).

   - `5338 = FW_maybe_shuffle(mref₁(5330), 5337)`.  `fw_maybe_shuffle` is the
     identity on the data tensor in this varlen model (Denote.lean:1235, audited
     against Python `wrap_maybe_shuffle`), and commutes with dim-0 sharding
     (`fw_maybe_shuffle_allGather0_commute_2`).  So `5338` is `5330` re-sharded.
     Note the CP metadata differs between SM (`[1,0]`) and PM (`[2,0]/[2,1]`),
     which is irrelevant precisely because the op ignores it.
   - `5340 = FW_rms_norm(mref₀(5338), 5339)` — 2-tp sharded RMSNorm, identical
     template to the periodic `5299`, backed by `fw_rms_norm_allGather0_commute_2`.
   - `5342 = FW_per_head(5340, 5341)` — 2-tp sharded per-head projection for the
     16-head Q path, backed by `fw_per_head_mix_precision_linear_allGather0_commute_2`.

   Each is closed by the standard `wrap_2tp_allGather_gen` gather bridge on the
   proven predecessor goal, so the whole L12 boundary tail is now closed. -/
import denote.yoco_goals.L12Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- Identity-shuffle lineage record used only by the value-lossy ring-attention
track. The faithful corpus uses `intermediateGoal_5338_zigzag` instead. -/
def ringAttnIntermediateGoal_5338 : LineageGoal :=
  { ts := 5338, tsShape := [4096, 1024],
    tps := [{ rank := 0, tid := 9655 }, { rank := 1, tid := 9656 }],
    tpShapes := [[2048, 1024], [2048, 1024]] }

def ringAttnIntermediateGoal_5340 : LineageGoal :=
  { ts := 5340, tsShape := [4096, 1024],
    tps := [{ rank := 0, tid := 9657 }, { rank := 1, tid := 9658 }],
    tpShapes := [[2048, 1024], [2048, 1024]] }

def ringAttnIntermediateGoal_5342 : LineageGoal :=
  { ts := 5342, tsShape := [4096, 16, 64],
    tps := [{ rank := 0, tid := 9659 }, { rank := 1, tid := 9660 }],
    tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

/-- 5338 — 2-tp `FW_maybe_shuffle(mref₁(5330), 5337)` (identity on data).
    Reconstructed as `5330` re-sharded via the maybe_shuffle/allGather commute. -/
theorem recon_intermediateGoal_5338_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_5338
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg30, hs9625, hs9626⟩ := twoTp_gather _ _ intermediateGoal_5330 5330 9625 9626
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5330_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8011 : denoteGraph_ringAttn sm initSM 8011 = denoteGraph_ringAttn sm initSM 5330 :=
    ringAttn_reduce1_pm_opaque sm initSM 470
      { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] }
      5330 8011 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 5330 8007 8011 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p13257 : denoteGraph_ringAttn pm initPM 13257 = denoteGraph_ringAttn pm initPM 9625 :=
    ringAttn_reduce1_pm_opaque pm initPM 1001
      { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] }
      9625 13257 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 9625 14597 13257 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p13258 : denoteGraph_ringAttn pm initPM 13258 = denoteGraph_ringAttn pm initPM 9626 :=
    ringAttn_reduce1_pm_opaque pm initPM 1002
      { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] }
      9626 13258 (fun x => x) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 9626 14599 13258 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5338
      = fw_maybe_shuffle (denoteGraph_ringAttn sm initSM 8011) (denoteGraph_ringAttn sm initSM 5337) 1 0 :=
    ringAttn_reduce2_pm_opaque sm initSM 472
      { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [8011, 5337], outs := [5338], params := [1, 0] }
      8011 5337 5338 (fun a b => fw_maybe_shuffle a b 1 0)
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_maybe_shuffle_out sm s 0 1 0 8011 5337 5338)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9655
      = fw_maybe_shuffle (denoteGraph_ringAttn pm initPM 13257) (denoteGraph_ringAttn pm initPM 5337) 2 0 :=
    ringAttn_reduce2_pm_opaque pm initPM 1003
      { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [13257, 5337], outs := [9655], params := [2, 0] }
      13257 5337 9655 (fun a b => fw_maybe_shuffle a b 2 0)
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_maybe_shuffle_out pm s 0 2 0 13257 5337 9655)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9656
      = fw_maybe_shuffle (denoteGraph_ringAttn pm initPM 13258) (denoteGraph_ringAttn pm initPM 5337) 2 1 :=
    ringAttn_reduce2_pm_opaque pm initPM 1005
      { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [13258, 5337], outs := [9656], params := [2, 1] }
      13258 5337 9656 (fun a b => fw_maybe_shuffle a b 2 1)
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_maybe_shuffle_out pm s 1 2 1 13258 5337 9656)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5338
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9655, denoteGraph_ringAttn pm initPM 9656] := by
    rw [rSM, rP0, rP1, s8011, p13257, p13258, hg30, hnr]
    simp only [fw_maybe_shuffle]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9655).shape = [2048, 1024] := by
    rw [rP0, p13257]; simp only [fw_maybe_shuffle]; exact hs9625
  have hsp1 : (denoteGraph_ringAttn pm initPM 9656).shape = [2048, 1024] := by
    rw [rP1, p13258]; simp only [fw_maybe_shuffle]; exact hs9626
  have hshape : (denoteGraph_ringAttn sm initSM 5338).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_5338 5338 9655 9656 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5340 — 2-tp `FW_rms_norm(mref₀(5338), 5339)`.  Same template as `5299`. -/
theorem recon_intermediateGoal_5340_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_5340
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg38, hs9655, hs9656⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5338 5338 9655 9656
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5338_ringAttn initSM initPM hSM hPM hInit hWF)
  have s8139 : denoteGraph_ringAttn sm initSM 8139 = id (denoteGraph_ringAttn sm initSM 5338) :=
    ringAttn_reduce1_pm_opaque sm initSM 474
      { rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] }
      5338 8139 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 5338 8139 8143)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15969 : denoteGraph_ringAttn pm initPM 15969 = id (denoteGraph_ringAttn pm initPM 9655) :=
    ringAttn_reduce1_pm_opaque pm initPM 1006
      { rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] }
      9655 15969 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 9655 15969 15973)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p15977 : denoteGraph_ringAttn pm initPM 15977 = id (denoteGraph_ringAttn pm initPM 9656) :=
    ringAttn_reduce1_pm_opaque pm initPM 1009
      { rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] }
      9656 15977 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 9656 15977 15981)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s8139 p15969 p15977
  have hs15969 : (denoteGraph_ringAttn pm initPM 15969).shape = [2048, 1024] := by
    rw [p15969]; exact hs9655
  have hs15977 : (denoteGraph_ringAttn pm initPM 15977).shape = [2048, 1024] := by
    rw [p15977]; exact hs9656
  have hbr : denoteGraph_ringAttn sm initSM 8139
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 15969, denoteGraph_ringAttn pm initPM 15977] := by
    rw [s8139, hg38, ← p15969, ← p15977]
  have hw5339 : denoteGraph_ringAttn sm initSM 5339 = denoteGraph_ringAttn pm initPM 5339 :=
    veq_weight_ring initSM initPM hInit initGoal_5339 (by native_decide) 5339
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 5340
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 8139) (denoteGraph_ringAttn sm initSM 5339) :=
    ringAttn_reduce2_pm_opaque sm initSM 477
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8139, 5339], outs := [5340] }
      8139 5339 5340 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 8139 5339 5340)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9657
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15969) (denoteGraph_ringAttn pm initPM 5339) :=
    ringAttn_reduce2_pm_opaque pm initPM 1010
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15969, 5339], outs := [9657] }
      15969 5339 9657 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 15969 5339 9657)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9658
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 15977) (denoteGraph_ringAttn pm initPM 5339) :=
    ringAttn_reduce2_pm_opaque pm initPM 1013
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15977, 5339], outs := [9658] }
      15977 5339 9658 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 15977 5339 9658)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5340
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9657, denoteGraph_ringAttn pm initPM 9658] := by
    rw [rSM, hbr, hw5339, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs15969 hs15977,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9657).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15969
  have hsp1 : (denoteGraph_ringAttn pm initPM 9658).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs15977
  have hshape : (denoteGraph_ringAttn sm initSM 5340).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_5340 5340 9657 9658 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 5342 — 2-tp `FW_per_head(5340, 5341)` (16-head Q path).  The per-head input
    is the goal tid `5340` directly (no intervening multiref). -/
theorem recon_intermediateGoal_5342_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks ringAttnIntermediateGoal_5342
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hg40, hs9657, hs9658⟩ := twoTp_gather _ _ ringAttnIntermediateGoal_5340 5340 9657 9658
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5340_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw5341 : denoteGraph_ringAttn sm initSM 5341 = denoteGraph_ringAttn pm initPM 5341 :=
    veq_weight_ring initSM initPM hInit initGoal_5341 (by native_decide) 5341
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw5341 : (denoteGraph_ringAttn sm initSM 5341).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_5341 (by native_decide) 5341 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hspw : (denoteGraph_ringAttn pm initPM 5341).shape = [16, 64, 1024] := by
    rw [← hw5341]; exact hsw5341
  have rSM : denoteGraph_ringAttn sm initSM 5342
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 5340) (denoteGraph_ringAttn sm initSM 5341) :=
    ringAttn_reduce2_pm_opaque sm initSM 480
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5340, 5341], outs := [5342] }
      5340 5341 5342 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 5340 5341 5342 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 9659
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 9657) (denoteGraph_ringAttn pm initPM 5341) :=
    ringAttn_reduce2_pm_opaque pm initPM 1014
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9657, 5341], outs := [9659] }
      9657 5341 9659 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 9657 5341 9659 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 9660
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 9658) (denoteGraph_ringAttn pm initPM 5341) :=
    ringAttn_reduce2_pm_opaque pm initPM 1019
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9658, 5341], outs := [9660] }
      9658 5341 9660 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 9658 5341 9660 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 5342
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 9659, denoteGraph_ringAttn pm initPM 9660] := by
    rw [rSM, hg40, hw5341, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs9657 hs9658 hspw,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 9659).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs9657 hspw
  have hsp1 : (denoteGraph_ringAttn pm initPM 9660).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs9658 hspw
  have hshape : (denoteGraph_ringAttn sm initSM 5342).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    ringAttnIntermediateGoal_5342 5342 9659 9660 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
