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

end TrainVerify.Denote.GeneratedPatterns
