/- Worker #23 — Layer-3 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from `recon_intermediateGoal_4804_ringAttn` (the layer-3
   sliding-window attention output, unconditional-given-WF) through the layer-3
   forward block.

   Unlike L2, the L3 block has NO gather-to-full node (L2's PM node 150
   `AllGatherPrim`): the residual stream stays sequence-parallel, so *every* L3
   intermediate is a genuine 2-tp SHARDED goal (`tps = [{0,r0},{1,r1}]`,
   `tpShapes = [shard, shard]`). This is verified from `GeneratedYOCOMoE.lean`
   (e.g. `intermediateGoal_4808` targets `[7821, 7822]`, not a single rank-0
   tid). The reconstruction therefore reuses L2's phase-3d 2-tp cascade gears
   (`twoTp_gather`, `wrap_2tp_allGather_gen`, the per-op allGather-commute
   lemmas) uniformly, rather than the L2 1-tp machinery. -/
import denote.yoco_goals.L2Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- 4805 — 2-tp reshape of the L3 attention output `4804 : [4096,16,64]` to
    `[4096,1024]` (SM node 88, PM nodes 237/238). -/
theorem recon_intermediateGoal_4805_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4805
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval04, hs7809, hs7810⟩ := twoTp_gather _ _ intermediateGoal_4804 4804 7809 7810
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4804_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4805
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4804) :=
    ringAttn_reshape_reduce_pm sm initSM 88 0 4804 4805 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7811
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7809) :=
    ringAttn_reshape_reduce_pm pm initPM 237 0 7809 7811 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7812
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7810) :=
    ringAttn_reshape_reduce_pm pm initPM 238 1 7810 7812 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4805
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7811, denoteGraph_ringAttn pm initPM 7812] := by
    rw [rSM, hval04, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs7809 hs7810
  have hs7811 : (denoteGraph_ringAttn pm initPM 7811).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs7812 : (denoteGraph_ringAttn pm initPM 7812).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4805 : (denoteGraph_ringAttn sm initSM 4805).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4805 4805 7811 7812 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4805 hs7811 hs7812

/-- 4806 — 2-tp identity reshape `[4096,1024]→[4096,1024]` (SM node 89, PM
    nodes 239/240). -/
theorem recon_intermediateGoal_4806_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4806
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval05, hs7811, hs7812⟩ := twoTp_gather _ _ intermediateGoal_4805 4805 7811 7812
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4805_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4805 : (denoteGraph_ringAttn sm initSM 4805).shape = [4096, 1024] := by
    rw [hval05, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs7811])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4806
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4805) :=
    ringAttn_reshape_reduce_pm sm initSM 89 0 4805 4806 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7817
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7811) :=
    ringAttn_reshape_reduce_pm pm initPM 239 0 7811 7817 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7818
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7812) :=
    ringAttn_reshape_reduce_pm pm initPM 240 1 7812 7818 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 7817 = denoteGraph_ringAttn pm initPM 7811 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs7811]
  have h18 : denoteGraph_ringAttn pm initPM 7818 = denoteGraph_ringAttn pm initPM 7812 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs7812]
  have hval : denoteGraph_ringAttn sm initSM 4806
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7817, denoteGraph_ringAttn pm initPM 7818] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4805, hval05, hnr, ← h17, ← h18]
  have hs7817 : (denoteGraph_ringAttn pm initPM 7817).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs7818 : (denoteGraph_ringAttn pm initPM 7818).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4806 : (denoteGraph_ringAttn sm initSM 4806).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4806 4806 7817 7818 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4806 hs7817 hs7818

/-- 4808 — 2-tp down-projection `fw_linear(4806, 4807)` (weight `4807 : [1024,1024]`,
    SM node 90, PM nodes 241/242). -/
theorem recon_intermediateGoal_4808_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4808
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval06, hs7817, hs7818⟩ := twoTp_gather _ _ intermediateGoal_4806 4806 7817 7818
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4806_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4807 : denoteGraph_ringAttn sm initSM 4807 = denoteGraph_ringAttn pm initPM 4807 :=
    veq_weight_ring initSM initPM hInit initGoal_4807 (by native_decide) 4807
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4807 : (denoteGraph_ringAttn sm initSM 4807).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4807 (by native_decide) 4807 [1024, 1024]
      rfl rfl (by native_decide)
  have hpw4807 : (denoteGraph_ringAttn pm initPM 4807).shape = [1024, 1024] := by
    rw [← hw4807]; exact hsw4807
  have rSM : denoteGraph_ringAttn sm initSM 4808
      = fw_linear (denoteGraph_ringAttn sm initSM 4806) (denoteGraph_ringAttn sm initSM 4807) :=
    ringAttn_reduce2_pm_opaque sm initSM 90
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4806, 4807], outs := [4808] }
      4806 4807 4808 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4806 4807 4808)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7821
      = fw_linear (denoteGraph_ringAttn pm initPM 7817) (denoteGraph_ringAttn pm initPM 4807) :=
    ringAttn_reduce2_pm_opaque pm initPM 241
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7817, 4807], outs := [7821] }
      7817 4807 7821 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 7817 4807 7821)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7822
      = fw_linear (denoteGraph_ringAttn pm initPM 7818) (denoteGraph_ringAttn pm initPM 4807) :=
    ringAttn_reduce2_pm_opaque pm initPM 242
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7818, 4807], outs := [7822] }
      7818 4807 7822 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 7818 4807 7822)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4808
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7821, denoteGraph_ringAttn pm initPM 7822] := by
    rw [rSM, hval06, hw4807, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
          (by omega) (by omega) (by omega) hs7817 hs7818 hpw4807,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7821).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs7817 hpw4807
  have hsp1 : (denoteGraph_ringAttn pm initPM 7822).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ hs7818 hpw4807
  have hshape : (denoteGraph_ringAttn sm initSM 4808).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4808 4808 7821 7822 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4809 — 2-tp identity view of `4808` (SM node 91, PM nodes 243/244). -/
theorem recon_intermediateGoal_4809_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4809
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval08, hs7821, hs7822⟩ := twoTp_gather _ _ intermediateGoal_4808 4808 7821 7822
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4808_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4808 : (denoteGraph_ringAttn sm initSM 4808).shape = [4096, 1024] := by
    rw [hval08, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs7821])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4809
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4808) :=
    ringAttn_reduce1_pm_opaque sm initSM 91
      { rank := 0, op := "OpName.FW_view", ins := [4808], outs := [4809], params := [4096, 1024] }
      4808 4809 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4808 4809)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7831
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7821) :=
    ringAttn_reduce1_pm_opaque pm initPM 243
      { rank := 0, op := "OpName.FW_view", ins := [7821], outs := [7831], params := [2048, 1024] }
      7821 7831 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 7821 7831)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7832
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7822) :=
    ringAttn_reduce1_pm_opaque pm initPM 244
      { rank := 1, op := "OpName.FW_view", ins := [7822], outs := [7832], params := [2048, 1024] }
      7822 7832 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 7822 7832)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h31 : denoteGraph_ringAttn pm initPM 7831 = denoteGraph_ringAttn pm initPM 7821 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs7821]
  have h32 : denoteGraph_ringAttn pm initPM 7832 = denoteGraph_ringAttn pm initPM 7822 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs7822]
  have hval : denoteGraph_ringAttn sm initSM 4809
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7831, denoteGraph_ringAttn pm initPM 7832] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4808, hval08, hnr, ← h31, ← h32]
  have hs7831 : (denoteGraph_ringAttn pm initPM 7831).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs7832 : (denoteGraph_ringAttn pm initPM 7832).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4809 : (denoteGraph_ringAttn sm initSM 4809).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4809 4809 7831 7832 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4809 hs7831 hs7832

/-- 4810 — 2-tp `FW_float(4809)` (identity, SM node 92, PM nodes 245/246). -/
theorem recon_intermediateGoal_4810_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4810
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr09, hs7831, hs7832⟩ := twoTp_gather _ _ intermediateGoal_4809 4809 7831 7832
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4809_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4810 = id (denoteGraph_ringAttn sm initSM 4809) :=
    ringAttn_reduce1_pm_opaque sm initSM 92
      { rank := 0, op := "OpName.FW_float", ins := [4809], outs := [4810] }
      4809 4810 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4809 4810 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7835 = id (denoteGraph_ringAttn pm initPM 7831) :=
    ringAttn_reduce1_pm_opaque pm initPM 245
      { rank := 0, op := "OpName.FW_float", ins := [7831], outs := [7835] }
      7831 7835 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 7831 7835 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7836 = id (denoteGraph_ringAttn pm initPM 7832) :=
    ringAttn_reduce1_pm_opaque pm initPM 246
      { rank := 1, op := "OpName.FW_float", ins := [7832], outs := [7836] }
      7832 7836 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 7832 7836 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 4810
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7835, denoteGraph_ringAttn pm initPM 7836] := by
    rw [rSM, hbr09, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7835).shape = [2048, 1024] := by rw [rP0]; exact hs7831
  have hsp1 : (denoteGraph_ringAttn pm initPM 7836).shape = [2048, 1024] := by rw [rP1]; exact hs7832
  have hshape : (denoteGraph_ringAttn sm initSM 4810).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4810 4810 7835 7836 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 7491 — 2-tp `mref2`-second copy of the L2 residual `4790` (SM node 80,
    PM nodes 221/222), carried into the L3 residual add. -/
theorem recon_intermediateGoal_7491_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7491
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr90, hs7765, hs7766⟩ := twoTp_gather _ _ intermediateGoal_4790 4790 7765 7766
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4790_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7491 : denoteGraph_ringAttn sm initSM 7491 = id (denoteGraph_ringAttn sm initSM 4790) :=
    ringAttn_reduce1_pm_opaque sm initSM 80
      { rank := 0, op := "OpName.FW_multiref", ins := [4790], outs := [7487, 7491], params := [2] }
      4790 7491 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4790 7487 7491 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14705 : denoteGraph_ringAttn pm initPM 14705 = id (denoteGraph_ringAttn pm initPM 7765) :=
    ringAttn_reduce1_pm_opaque pm initPM 221
      { rank := 0, op := "OpName.FW_multiref", ins := [7765], outs := [14701, 14705], params := [2] }
      7765 14705 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 7765 14701 14705 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14713 : denoteGraph_ringAttn pm initPM 14713 = id (denoteGraph_ringAttn pm initPM 7766) :=
    ringAttn_reduce1_pm_opaque pm initPM 222
      { rank := 1, op := "OpName.FW_multiref", ins := [7766], outs := [14709, 14713], params := [2] }
      7766 14713 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 7766 14709 14713 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7491 p14705 p14713
  have hsp0 : (denoteGraph_ringAttn pm initPM 14705).shape = [2048, 1024] := by
    rw [p14705]; exact hs7765
  have hsp1 : (denoteGraph_ringAttn pm initPM 14713).shape = [2048, 1024] := by
    rw [p14713]; exact hs7766
  have hval : denoteGraph_ringAttn sm initSM 7491
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14705, denoteGraph_ringAttn pm initPM 14713] := by
    rw [s7491, hbr90, ← p14705, ← p14713]
  have hshape : (denoteGraph_ringAttn sm initSM 7491).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7491 7491 14705 14713 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4811 — 2-tp L3 residual add `7491 + 4810` (SM node 93, PM nodes 247/248). -/
theorem recon_intermediateGoal_4811_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4811
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr91, hs14705, hs14713⟩ := twoTp_gather _ _ intermediateGoal_7491 7491 14705 14713
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7491_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr10, hs7835, hs7836⟩ := twoTp_gather _ _ intermediateGoal_4810 4810 7835 7836
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4810_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4811
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7491) (denoteGraph_ringAttn sm initSM 4810) :=
    ringAttn_reduce2_pm_opaque sm initSM 93
      { rank := 0, op := "OpName.FW_add", ins := [7491, 4810], outs := [4811] }
      7491 4810 4811 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7491 4810 4811)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7839
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14705) (denoteGraph_ringAttn pm initPM 7835) :=
    ringAttn_reduce2_pm_opaque pm initPM 247
      { rank := 0, op := "OpName.FW_add", ins := [14705, 7835], outs := [7839] }
      14705 7835 7839 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 14705 7835 7839)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7840
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14713) (denoteGraph_ringAttn pm initPM 7836) :=
    ringAttn_reduce2_pm_opaque pm initPM 248
      { rank := 1, op := "OpName.FW_add", ins := [14713, 7836], outs := [7840] }
      14713 7836 7840 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14713 7836 7840)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4811
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7839, denoteGraph_ringAttn pm initPM 7840] := by
    rw [rSM, hbr91, hbr10, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs14705 hs14713 hs7835 hs7836,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7839).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14705 hs7835
  have hsp1 : (denoteGraph_ringAttn pm initPM 7840).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14713 hs7836
  have hshape : (denoteGraph_ringAttn sm initSM 4811).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4811 4811 7839 7840 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4813 — 2-tp RMSNorm of `mref2-first(4811)` with replicated weight
    `4812 : [1024]` (SM node 95, PM nodes 251/252). -/
theorem recon_intermediateGoal_4813_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4813
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs7839, hs7840⟩ := twoTp_gather _ _ intermediateGoal_4811 4811 7839 7840
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4811_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7508 : denoteGraph_ringAttn sm initSM 7508 = id (denoteGraph_ringAttn sm initSM 4811) :=
    ringAttn_reduce1_pm_opaque sm initSM 94
      { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512], params := [2] }
      4811 7508 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4811 7508 7512)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14743 : denoteGraph_ringAttn pm initPM 14743 = id (denoteGraph_ringAttn pm initPM 7839) :=
    ringAttn_reduce1_pm_opaque pm initPM 249
      { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747], params := [2] }
      7839 14743 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 7839 14743 14747)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14751 : denoteGraph_ringAttn pm initPM 14751 = id (denoteGraph_ringAttn pm initPM 7840) :=
    ringAttn_reduce1_pm_opaque pm initPM 250
      { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755], params := [2] }
      7840 14751 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 7840 14751 14755)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7508 p14743 p14751
  have hs14743 : (denoteGraph_ringAttn pm initPM 14743).shape = [2048, 1024] := by
    rw [p14743]; exact hs7839
  have hs14751 : (denoteGraph_ringAttn pm initPM 14751).shape = [2048, 1024] := by
    rw [p14751]; exact hs7840
  have hbr08 : denoteGraph_ringAttn sm initSM 7508
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14743, denoteGraph_ringAttn pm initPM 14751] := by
    rw [s7508, hbr11, ← p14743, ← p14751]
  have hw4812 : denoteGraph_ringAttn sm initSM 4812 = denoteGraph_ringAttn pm initPM 4812 :=
    veq_weight_ring initSM initPM hInit initGoal_4812 (by native_decide) 4812
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4813
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7508) (denoteGraph_ringAttn sm initSM 4812) :=
    ringAttn_reduce2_pm_opaque sm initSM 95
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7508, 4812], outs := [4813] }
      7508 4812 4813 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7508 4812 4813)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7843
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14743) (denoteGraph_ringAttn pm initPM 4812) :=
    ringAttn_reduce2_pm_opaque pm initPM 251
      { rank := 0, op := "OpName.FW_rms_norm", ins := [14743, 4812], outs := [7843] }
      14743 4812 7843 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 14743 4812 7843)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7844
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14751) (denoteGraph_ringAttn pm initPM 4812) :=
    ringAttn_reduce2_pm_opaque pm initPM 252
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14751, 4812], outs := [7844] }
      14751 4812 7844 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14751 4812 7844)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4813
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7843, denoteGraph_ringAttn pm initPM 7844] := by
    rw [rSM, hbr08, hw4812, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs14743 hs14751,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7843).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14743
  have hsp1 : (denoteGraph_ringAttn pm initPM 7844).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14751
  have hshape : (denoteGraph_ringAttn sm initSM 4813).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4813 4813 7843 7844 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4814 — 2-tp `FW_float(mref5-first(4813))` (identity, SM node 97,
    PM nodes 255/259; mref5-first via SM node 96, PM 253/254). -/
theorem recon_intermediateGoal_4814_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4814
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs7843, hs7844⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7519 : denoteGraph_ringAttn sm initSM 7519 = id (denoteGraph_ringAttn sm initSM 4813) :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813],
        outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7519 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 4813 7519 [7523, 7527, 7531, 7535])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14762 : denoteGraph_ringAttn pm initPM 14762 = id (denoteGraph_ringAttn pm initPM 7843) :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843],
        outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14762 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 0 4 7843 14762 [14766, 14770, 14774, 14778])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14785 : denoteGraph_ringAttn pm initPM 14785 = id (denoteGraph_ringAttn pm initPM 7844) :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844],
        outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14785 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 7844 14785 [14789, 14793, 14797, 14801])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7519 p14762 p14785
  have hbrm : denoteGraph_ringAttn sm initSM 7519
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14762, denoteGraph_ringAttn pm initPM 14785] := by
    rw [s7519, hbr13, ← p14762, ← p14785]
  have rSM : denoteGraph_ringAttn sm initSM 4814 = id (denoteGraph_ringAttn sm initSM 7519) :=
    ringAttn_reduce1_pm_opaque sm initSM 97
      { rank := 0, op := "OpName.FW_float", ins := [7519], outs := [4814] }
      7519 4814 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7519 4814 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7845 = id (denoteGraph_ringAttn pm initPM 14762) :=
    ringAttn_reduce1_pm_opaque pm initPM 255
      { rank := 0, op := "OpName.FW_float", ins := [14762], outs := [7845] }
      14762 7845 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 14762 7845 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7846 = id (denoteGraph_ringAttn pm initPM 14785) :=
    ringAttn_reduce1_pm_opaque pm initPM 259
      { rank := 1, op := "OpName.FW_float", ins := [14785], outs := [7846] }
      14785 7846 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 14785 7846 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hs14762 : (denoteGraph_ringAttn pm initPM 14762).shape = [2048, 1024] := by
    rw [p14762]; exact hs7843
  have hs14785 : (denoteGraph_ringAttn pm initPM 14785).shape = [2048, 1024] := by
    rw [p14785]; exact hs7844
  have hval : denoteGraph_ringAttn sm initSM 4814
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7845, denoteGraph_ringAttn pm initPM 7846] := by
    rw [rSM, hbrm, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7845).shape = [2048, 1024] := by
    rw [rP0]; exact hs14762
  have hsp1 : (denoteGraph_ringAttn pm initPM 7846).shape = [2048, 1024] := by
    rw [rP1]; exact hs14785
  have hshape : (denoteGraph_ringAttn sm initSM 4814).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4814 4814 7845 7846 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4816 — 2-tp router logits `fw_norm_linear(4814, 4815)` with weight
    `4815 : [64, 1024]` → `[4096, 64]` (SM node 101, PM nodes 263/267). -/
theorem recon_intermediateGoal_4816_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4816
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval14, hs7845, hs7846⟩ := twoTp_gather _ _ intermediateGoal_4814 4814 7845 7846
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4814_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4815 : denoteGraph_ringAttn sm initSM 4815 = denoteGraph_ringAttn pm initPM 4815 :=
    veq_weight_ring initSM initPM hInit initGoal_4815 (by native_decide) 4815
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4815 : (denoteGraph_ringAttn sm initSM 4815).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4815 (by native_decide) 4815 [64, 1024]
      rfl rfl (by native_decide)
  have hpw4815 : (denoteGraph_ringAttn pm initPM 4815).shape = [64, 1024] := by
    rw [← hw4815]; exact hsw4815
  have rSM : denoteGraph_ringAttn sm initSM 4816
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 4814) (denoteGraph_ringAttn sm initSM 4815) :=
    ringAttn_reduce2_pm_opaque sm initSM 101
      { rank := 0, op := "OpName.FW_norm_linear", ins := [4814, 4815], outs := [4816] }
      4814 4815 4816 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 4814 4815 4816)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7851
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 7845) (denoteGraph_ringAttn pm initPM 4815) :=
    ringAttn_reduce2_pm_opaque pm initPM 263
      { rank := 0, op := "OpName.FW_norm_linear", ins := [7845, 4815], outs := [7851] }
      7845 4815 7851 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 0 7845 4815 7851)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7852
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 7846) (denoteGraph_ringAttn pm initPM 4815) :=
    ringAttn_reduce2_pm_opaque pm initPM 267
      { rank := 1, op := "OpName.FW_norm_linear", ins := [7846, 4815], outs := [7852] }
      7846 4815 7852 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 7846 4815 7852)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4816
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7851, denoteGraph_ringAttn pm initPM 7852] := by
    rw [rSM, hval14, hw4815, hnr,
        fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
          (by omega) (by omega) (by omega) hs7845 hs7846 hpw4815,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7851).shape = [2048, 64] := by
    rw [rP0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs7845 hpw4815
  have hsp1 : (denoteGraph_ringAttn pm initPM 7852).shape = [2048, 64] := by
    rw [rP1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) hs7846 hpw4815
  have hshape : (denoteGraph_ringAttn sm initSM 4816).shape = [4096, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4816 4816 7851 7852 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L3 top-k routing (`4817`/`4818`) — token-sharded 2-tp.
    Unlike L2 there is no gather-to-full/chunk step: each rank runs `topk` on
    its `[2048, 64]` router-logit shard (`7851`/`7852`) directly. -/

/-- Shared L3 top-k core: `4816` (full logits) is the dim-0 gather of the two
    per-rank shards `7851`/`7852`, plus the shape + trailing-dim prefix facts the
    `applyNode_topk81_*` gears require. -/
theorem moe_topk_common_L3 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 4816
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 7851, denoteGraph_ringAttn pm initPM 7852]
      ∧ (denoteGraph_ringAttn sm initSM 4816).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 7851).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 7852).shape = [2048, 64]
      ∧ ((sm.nodes.take 105).foldl (applyNodeRingAttn sm) initSM 4816).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 271).foldl (applyNodeRingAttn pm) initPM 7851).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 275).foldl (applyNodeRingAttn pm) initPM 7852).shape.reverse.head? = some 64 := by
  obtain ⟨hbr16, hs7851, hs7852⟩ := twoTp_gather _ _ intermediateGoal_4816 4816 7851 7852
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4816_ringAttn initSM initPM hSM hPM hInit hWF)
  have hnr : pm.numRanks = 2 := rfl
  have hs4816sm : (denoteGraph_ringAttn sm initSM 4816).shape = [4096, 64] := by
    rw [hbr16, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 64] (by simp [hs7851])]
    simp [List.set, List.getD]
  have hpre4816sm : denoteGraph_ringAttn sm initSM 4816
      = (sm.nodes.take 105).foldl (applyNodeRingAttn sm) initSM 4816 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 4816 105 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 105).foldl (applyNodeRingAttn sm) initSM 4816).shape.reverse.head? = some 64 := by
    rw [← hpre4816sm, hs4816sm]; rfl
  have hpre7851 : denoteGraph_ringAttn pm initPM 7851
      = (pm.nodes.take 271).foldl (applyNodeRingAttn pm) initPM 7851 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 7851 271 (by native_decide) (by native_decide)
  have hlast271 : ((pm.nodes.take 271).foldl (applyNodeRingAttn pm) initPM 7851).shape.reverse.head? = some 64 := by
    rw [← hpre7851, hs7851]; rfl
  have hpre7852 : denoteGraph_ringAttn pm initPM 7852
      = (pm.nodes.take 275).foldl (applyNodeRingAttn pm) initPM 7852 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 7852 275 (by native_decide) (by native_decide)
  have hlast275 : ((pm.nodes.take 275).foldl (applyNodeRingAttn pm) initPM 7852).shape.reverse.head? = some 64 := by
    rw [← hpre7852, hs7852]; rfl
  exact ⟨hbr16, hs4816sm, hs7851, hs7852, hlastSM, hlast271, hlast275⟩

/-- 4817 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4817_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4817
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4816sm, hs7851, hs7852, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L3 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4817
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4816) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 105
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4816], outs := [4817, 4818, 4819], params := [8, 1] }
      4816 4817 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 105).foldl (applyNodeRingAttn sm) initSM) 0 4816 4817 4818 4819 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7853
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7851) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 271
      { rank := 0, op := "OpName.FW_topk_routing", ins := [7851], outs := [7853, 7855, 7857], params := [8, 1] }
      7851 7853 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 271).foldl (applyNodeRingAttn pm) initPM) 0 7851 7853 7855 7857 hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7854
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7852) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 275
      { rank := 1, op := "OpName.FW_topk_routing", ins := [7852], outs := [7854, 7856, 7858], params := [8, 1] }
      7852 7854 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 275).foldl (applyNodeRingAttn pm) initPM) 1 7852 7854 7856 7858 hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4817
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7853, denoteGraph_ringAttn pm initPM 7854] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs7851 hs7852,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4817).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs4816sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 7853).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs7851]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 7854).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs7852]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4817 4817 7853 7854 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4818 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4818_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4818
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4816sm, hs7851, hs7852, hlastSM, hlast271, hlast275⟩ :=
    moe_topk_common_L3 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4818
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4816) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 105
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4816], outs := [4817, 4818, 4819], params := [8, 1] }
      4816 4818 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 105).foldl (applyNodeRingAttn sm) initSM) 0 4816 4817 4818 4819 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7855
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7851) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 271
      { rank := 0, op := "OpName.FW_topk_routing", ins := [7851], outs := [7853, 7855, 7857], params := [8, 1] }
      7851 7855 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 271).foldl (applyNodeRingAttn pm) initPM) 0 7851 7853 7855 7857 (by decide) hlast271)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7856
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7852) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 275
      { rank := 1, op := "OpName.FW_topk_routing", ins := [7852], outs := [7854, 7856, 7858], params := [8, 1] }
      7852 7856 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 275).foldl (applyNodeRingAttn pm) initPM) 1 7852 7854 7856 7858 (by decide) hlast275)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4818
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7855, denoteGraph_ringAttn pm initPM 7856] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs7851 hs7852,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4818).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs4816sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 7855).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs7851]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 7856).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs7852]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4818 4818 7855 7856 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L3 router expert branches — reshape (`4823`/`4828`/`4832`) of the
    `mref5` copies (positions 2/3/4) of `4813`, all identity 2-tp views. -/

/-- 4823 — 2-tp identity reshape of `mref5-pos2(4813)` (SM node 98, PM 256/260). -/
theorem recon_intermediateGoal_4823_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4823
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs7843, hs7844⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4813sm : (denoteGraph_ringAttn sm initSM 4813).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs7843])]
    simp [List.set, List.getD]
  have s7527 : denoteGraph_ringAttn sm initSM 7527 = id (denoteGraph_ringAttn sm initSM 4813) :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813],
        outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7527 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14770 : denoteGraph_ringAttn pm initPM 14770 = id (denoteGraph_ringAttn pm initPM 7843) :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843],
        outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14770 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14793 : denoteGraph_ringAttn pm initPM 14793 = id (denoteGraph_ringAttn pm initPM 7844) :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844],
        outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14793 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7527 p14770 p14793
  have hs7527 : (denoteGraph_ringAttn sm initSM 7527).shape = [4096, 1024] := by rw [s7527]; exact hs4813sm
  have hs14770 : (denoteGraph_ringAttn pm initPM 14770).shape = [2048, 1024] := by rw [p14770]; exact hs7843
  have hs14793 : (denoteGraph_ringAttn pm initPM 14793).shape = [2048, 1024] := by rw [p14793]; exact hs7844
  have hbrm : denoteGraph_ringAttn sm initSM 7527
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14770, denoteGraph_ringAttn pm initPM 14793] := by
    rw [s7527, hbr13, ← p14770, ← p14793]
  have rSM : denoteGraph_ringAttn sm initSM 4823
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7527) :=
    ringAttn_reduce1_pm_opaque sm initSM 98
      { rank := 0, op := "OpName.FW_reshape", ins := [7527], outs := [4823], params := [4096, 1024] }
      7527 4823 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7527 4823)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7865
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14770) :=
    ringAttn_reduce1_pm_opaque pm initPM 256
      { rank := 0, op := "OpName.FW_reshape", ins := [14770], outs := [7865], params := [2048, 1024] }
      14770 7865 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14770 7865)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7866
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14793) :=
    ringAttn_reduce1_pm_opaque pm initPM 260
      { rank := 1, op := "OpName.FW_reshape", ins := [14793], outs := [7866], params := [2048, 1024] }
      14793 7866 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 14793 7866)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h65 : denoteGraph_ringAttn pm initPM 7865 = denoteGraph_ringAttn pm initPM 14770 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14770]
  have h66 : denoteGraph_ringAttn pm initPM 7866 = denoteGraph_ringAttn pm initPM 14793 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs14793]
  have hval : denoteGraph_ringAttn sm initSM 4823
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7865, denoteGraph_ringAttn pm initPM 7866] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7527, hbrm, hnr, ← h65, ← h66]
  have hs7865 : (denoteGraph_ringAttn pm initPM 7865).shape = [2048, 1024] := by rw [h65]; exact hs14770
  have hs7866 : (denoteGraph_ringAttn pm initPM 7866).shape = [2048, 1024] := by rw [h66]; exact hs14793
  have hs4823 : (denoteGraph_ringAttn sm initSM 4823).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7527]; exact hs7527
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4823 4823 7865 7866 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4823 hs7865 hs7866

/-- 4828 — 2-tp identity reshape of `mref5-pos3(4813)` (SM node 99, PM 257/261). -/
theorem recon_intermediateGoal_4828_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4828
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs7843, hs7844⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4813sm : (denoteGraph_ringAttn sm initSM 4813).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs7843])]
    simp [List.set, List.getD]
  have s7531 : denoteGraph_ringAttn sm initSM 7531 = id (denoteGraph_ringAttn sm initSM 4813) :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813],
        outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7531 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14774 : denoteGraph_ringAttn pm initPM 14774 = id (denoteGraph_ringAttn pm initPM 7843) :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843],
        outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14774 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14797 : denoteGraph_ringAttn pm initPM 14797 = id (denoteGraph_ringAttn pm initPM 7844) :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844],
        outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14797 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7531 p14774 p14797
  have hs7531 : (denoteGraph_ringAttn sm initSM 7531).shape = [4096, 1024] := by rw [s7531]; exact hs4813sm
  have hs14774 : (denoteGraph_ringAttn pm initPM 14774).shape = [2048, 1024] := by rw [p14774]; exact hs7843
  have hs14797 : (denoteGraph_ringAttn pm initPM 14797).shape = [2048, 1024] := by rw [p14797]; exact hs7844
  have hbrm : denoteGraph_ringAttn sm initSM 7531
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14774, denoteGraph_ringAttn pm initPM 14797] := by
    rw [s7531, hbr13, ← p14774, ← p14797]
  have rSM : denoteGraph_ringAttn sm initSM 4828
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7531) :=
    ringAttn_reduce1_pm_opaque sm initSM 99
      { rank := 0, op := "OpName.FW_reshape", ins := [7531], outs := [4828], params := [4096, 1024] }
      7531 4828 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7531 4828)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7879
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14774) :=
    ringAttn_reduce1_pm_opaque pm initPM 257
      { rank := 0, op := "OpName.FW_reshape", ins := [14774], outs := [7879], params := [2048, 1024] }
      14774 7879 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14774 7879)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7880
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14797) :=
    ringAttn_reduce1_pm_opaque pm initPM 261
      { rank := 1, op := "OpName.FW_reshape", ins := [14797], outs := [7880], params := [2048, 1024] }
      14797 7880 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 14797 7880)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h79 : denoteGraph_ringAttn pm initPM 7879 = denoteGraph_ringAttn pm initPM 14774 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14774]
  have h80 : denoteGraph_ringAttn pm initPM 7880 = denoteGraph_ringAttn pm initPM 14797 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs14797]
  have hval : denoteGraph_ringAttn sm initSM 4828
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7879, denoteGraph_ringAttn pm initPM 7880] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7531, hbrm, hnr, ← h79, ← h80]
  have hs7879 : (denoteGraph_ringAttn pm initPM 7879).shape = [2048, 1024] := by rw [h79]; exact hs14774
  have hs7880 : (denoteGraph_ringAttn pm initPM 7880).shape = [2048, 1024] := by rw [h80]; exact hs14797
  have hs4828 : (denoteGraph_ringAttn sm initSM 4828).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7531]; exact hs7531
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4828 4828 7879 7880 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4828 hs7879 hs7880

/-- 4832 — 2-tp identity reshape of `mref5-pos4(4813)` (SM node 100, PM 258/262). -/
theorem recon_intermediateGoal_4832_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4832
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr13, hs7843, hs7844⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4813sm : (denoteGraph_ringAttn sm initSM 4813).shape = [4096, 1024] := by
    rw [hbr13, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs7843])]
    simp [List.set, List.getD]
  have s7535 : denoteGraph_ringAttn sm initSM 7535 = id (denoteGraph_ringAttn sm initSM 4813) :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813],
        outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7535 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14778 : denoteGraph_ringAttn pm initPM 14778 = id (denoteGraph_ringAttn pm initPM 7843) :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843],
        outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14778 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14801 : denoteGraph_ringAttn pm initPM 14801 = id (denoteGraph_ringAttn pm initPM 7844) :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844],
        outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14801 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7535 p14778 p14801
  have hs7535 : (denoteGraph_ringAttn sm initSM 7535).shape = [4096, 1024] := by rw [s7535]; exact hs4813sm
  have hs14778 : (denoteGraph_ringAttn pm initPM 14778).shape = [2048, 1024] := by rw [p14778]; exact hs7843
  have hs14801 : (denoteGraph_ringAttn pm initPM 14801).shape = [2048, 1024] := by rw [p14801]; exact hs7844
  have hbrm : denoteGraph_ringAttn sm initSM 7535
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14778, denoteGraph_ringAttn pm initPM 14801] := by
    rw [s7535, hbr13, ← p14778, ← p14801]
  have rSM : denoteGraph_ringAttn sm initSM 4832
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7535) :=
    ringAttn_reduce1_pm_opaque sm initSM 100
      { rank := 0, op := "OpName.FW_reshape", ins := [7535], outs := [4832], params := [4096, 1024] }
      7535 4832 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 7535 4832)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7897
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14778) :=
    ringAttn_reduce1_pm_opaque pm initPM 258
      { rank := 0, op := "OpName.FW_reshape", ins := [14778], outs := [7897], params := [2048, 1024] }
      14778 7897 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 14778 7897)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7898
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 14801) :=
    ringAttn_reduce1_pm_opaque pm initPM 262
      { rank := 1, op := "OpName.FW_reshape", ins := [14801], outs := [7898], params := [2048, 1024] }
      14801 7898 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 14801 7898)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h97 : denoteGraph_ringAttn pm initPM 7897 = denoteGraph_ringAttn pm initPM 14778 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs14778]
  have h98 : denoteGraph_ringAttn pm initPM 7898 = denoteGraph_ringAttn pm initPM 14801 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs14801]
  have hval : denoteGraph_ringAttn sm initSM 4832
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7897, denoteGraph_ringAttn pm initPM 7898] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7535, hbrm, hnr, ← h97, ← h98]
  have hs7897 : (denoteGraph_ringAttn pm initPM 7897).shape = [2048, 1024] := by rw [h97]; exact hs14778
  have hs7898 : (denoteGraph_ringAttn pm initPM 7898).shape = [2048, 1024] := by rw [h98]; exact hs14801
  have hs4832 : (denoteGraph_ringAttn sm initSM 4832).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7535]; exact hs7535
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4832 4832 7897 7898 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4832 hs7897 hs7898

/-! ### L3 router expert mixlins (`4825`/`4830`/`4834`), 2-tp. -/

/-- 4825 — 2-tp `fw_linear(4823, 4824)`, weight `4824 : [1, 1024]` → `[4096, 1]`
    (SM node 102, PM nodes 264/268). -/
theorem recon_intermediateGoal_4825_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4825
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval23, hs7865, hs7866⟩ := twoTp_gather _ _ intermediateGoal_4823 4823 7865 7866
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4823_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4824 : denoteGraph_ringAttn sm initSM 4824 = denoteGraph_ringAttn pm initPM 4824 :=
    veq_weight_ring initSM initPM hInit initGoal_4824 (by native_decide) 4824
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4824 : (denoteGraph_ringAttn pm initPM 4824).shape = [1, 1024] := by
    rw [← hw4824]
    exact shape_weight_ring initSM initPM hInit initGoal_4824 (by native_decide) 4824 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4825
      = fw_linear (denoteGraph_ringAttn sm initSM 4823) (denoteGraph_ringAttn sm initSM 4824) :=
    ringAttn_reduce2_pm_opaque sm initSM 102
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4823, 4824], outs := [4825] }
      4823 4824 4825 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4823 4824 4825)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7869
      = fw_linear (denoteGraph_ringAttn pm initPM 7865) (denoteGraph_ringAttn pm initPM 4824) :=
    ringAttn_reduce2_pm_opaque pm initPM 264
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7865, 4824], outs := [7869] }
      7865 4824 7869 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 7865 4824 7869)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7870
      = fw_linear (denoteGraph_ringAttn pm initPM 7866) (denoteGraph_ringAttn pm initPM 4824) :=
    ringAttn_reduce2_pm_opaque pm initPM 268
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7866, 4824], outs := [7870] }
      7866 4824 7870 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 7866 4824 7870)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4825
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7869, denoteGraph_ringAttn pm initPM 7870] := by
    rw [rSM, hval23, hw4824, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
          (by omega) (by omega) (by omega) hs7865 hs7866 hpw4824,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7869).shape = [2048, 1] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs7865 hpw4824
  have hsp1 : (denoteGraph_ringAttn pm initPM 7870).shape = [2048, 1] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 1 _ _ hs7866 hpw4824
  have hshape : (denoteGraph_ringAttn sm initSM 4825).shape = [4096, 1] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4825 4825 7869 7870 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4830 — 2-tp `fw_linear(4828, 4829)`, weight `4829 : [512, 1024]` → `[4096, 512]`
    (SM node 103, PM nodes 265/269). -/
theorem recon_intermediateGoal_4830_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4830
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval28, hs7879, hs7880⟩ := twoTp_gather _ _ intermediateGoal_4828 4828 7879 7880
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4828_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4829 : denoteGraph_ringAttn sm initSM 4829 = denoteGraph_ringAttn pm initPM 4829 :=
    veq_weight_ring initSM initPM hInit initGoal_4829 (by native_decide) 4829
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4829 : (denoteGraph_ringAttn pm initPM 4829).shape = [512, 1024] := by
    rw [← hw4829]
    exact shape_weight_ring initSM initPM hInit initGoal_4829 (by native_decide) 4829 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4830
      = fw_linear (denoteGraph_ringAttn sm initSM 4828) (denoteGraph_ringAttn sm initSM 4829) :=
    ringAttn_reduce2_pm_opaque sm initSM 103
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4828, 4829], outs := [4830] }
      4828 4829 4830 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4828 4829 4830)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7883
      = fw_linear (denoteGraph_ringAttn pm initPM 7879) (denoteGraph_ringAttn pm initPM 4829) :=
    ringAttn_reduce2_pm_opaque pm initPM 265
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7879, 4829], outs := [7883] }
      7879 4829 7883 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 7879 4829 7883)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7884
      = fw_linear (denoteGraph_ringAttn pm initPM 7880) (denoteGraph_ringAttn pm initPM 4829) :=
    ringAttn_reduce2_pm_opaque pm initPM 269
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7880, 4829], outs := [7884] }
      7880 4829 7884 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 7880 4829 7884)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4830
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7883, denoteGraph_ringAttn pm initPM 7884] := by
    rw [rSM, hval28, hw4829, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs7879 hs7880 hpw4829,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7883).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs7879 hpw4829
  have hsp1 : (denoteGraph_ringAttn pm initPM 7884).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs7880 hpw4829
  have hshape : (denoteGraph_ringAttn sm initSM 4830).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4830 4830 7883 7884 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4834 — 2-tp `fw_linear(4832, 4833)`, weight `4833 : [512, 1024]` → `[4096, 512]`
    (SM node 104, PM nodes 266/270). -/
theorem recon_intermediateGoal_4834_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4834
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval32, hs7897, hs7898⟩ := twoTp_gather _ _ intermediateGoal_4832 4832 7897 7898
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4832_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4833 : denoteGraph_ringAttn sm initSM 4833 = denoteGraph_ringAttn pm initPM 4833 :=
    veq_weight_ring initSM initPM hInit initGoal_4833 (by native_decide) 4833
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4833 : (denoteGraph_ringAttn pm initPM 4833).shape = [512, 1024] := by
    rw [← hw4833]
    exact shape_weight_ring initSM initPM hInit initGoal_4833 (by native_decide) 4833 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4834
      = fw_linear (denoteGraph_ringAttn sm initSM 4832) (denoteGraph_ringAttn sm initSM 4833) :=
    ringAttn_reduce2_pm_opaque sm initSM 104
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4832, 4833], outs := [4834] }
      4832 4833 4834 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4832 4833 4834)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7901
      = fw_linear (denoteGraph_ringAttn pm initPM 7897) (denoteGraph_ringAttn pm initPM 4833) :=
    ringAttn_reduce2_pm_opaque pm initPM 266
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7897, 4833], outs := [7901] }
      7897 4833 7901 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 7897 4833 7901)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7902
      = fw_linear (denoteGraph_ringAttn pm initPM 7898) (denoteGraph_ringAttn pm initPM 4833) :=
    ringAttn_reduce2_pm_opaque pm initPM 270
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7898, 4833], outs := [7902] }
      7898 4833 7902 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 7898 4833 7902)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4834
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7901, denoteGraph_ringAttn pm initPM 7902] := by
    rw [rSM, hval32, hw4833, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
          (by omega) (by omega) (by omega) hs7897 hs7898 hpw4833,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7901).shape = [2048, 512] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs7897 hpw4833
  have hsp1 : (denoteGraph_ringAttn pm initPM 7902).shape = [2048, 512] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 1024 512 _ _ hs7898 hpw4833
  have hshape : (denoteGraph_ringAttn sm initSM 4834).shape = [4096, 512] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4834 4834 7901 7902 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### L3 router expert views (`4826`/`4831`/`4835`), identity 2-tp views. -/

/-- 4826 — 2-tp identity view of `4825` → `[4096, 1]` (SM node 106, PM 272/276). -/
theorem recon_intermediateGoal_4826_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4826
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval25, hs7869, hs7870⟩ := twoTp_gather _ _ intermediateGoal_4825 4825 7869 7870
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4825_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4825 : (denoteGraph_ringAttn sm initSM 4825).shape = [4096, 1] := by
    rw [hval25, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs7869])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4826
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 4825) :=
    ringAttn_reduce1_pm_opaque sm initSM 106
      { rank := 0, op := "OpName.FW_view", ins := [4825], outs := [4826], params := [4096, 1] }
      4825 4826 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 4825 4826)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7875
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 7869) :=
    ringAttn_reduce1_pm_opaque pm initPM 272
      { rank := 0, op := "OpName.FW_view", ins := [7869], outs := [7875], params := [2048, 1] }
      7869 7875 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1] 7869 7875)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7876
      = fw_view [2048, 1] (denoteGraph_ringAttn pm initPM 7870) :=
    ringAttn_reduce1_pm_opaque pm initPM 276
      { rank := 1, op := "OpName.FW_view", ins := [7870], outs := [7876], params := [2048, 1] }
      7870 7876 (fw_view [2048, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1] 7870 7876)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h75 : denoteGraph_ringAttn pm initPM 7875 = denoteGraph_ringAttn pm initPM 7869 := by
    rw [rP0, fw_view_id_shape [2048, 1] _ hs7869]
  have h76 : denoteGraph_ringAttn pm initPM 7876 = denoteGraph_ringAttn pm initPM 7870 := by
    rw [rP1, fw_view_id_shape [2048, 1] _ hs7870]
  have hval : denoteGraph_ringAttn sm initSM 4826
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7875, denoteGraph_ringAttn pm initPM 7876] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4825, hval25, hnr, ← h75, ← h76]
  have hs7875 : (denoteGraph_ringAttn pm initPM 7875).shape = [2048, 1] := by rw [h75]; exact hs7869
  have hs7876 : (denoteGraph_ringAttn pm initPM 7876).shape = [2048, 1] := by rw [h76]; exact hs7870
  have hs4826 : (denoteGraph_ringAttn sm initSM 4826).shape = [4096, 1] := by
    rw [rSM, fw_view_id_shape [4096, 1] _ hs4825]; exact hs4825
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4826 4826 7875 7876 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4826 hs7875 hs7876

/-- 4831 — 2-tp identity view of `4830` → `[4096, 512]` (SM node 107, PM 273/277). -/
theorem recon_intermediateGoal_4831_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4831
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval30, hs7883, hs7884⟩ := twoTp_gather _ _ intermediateGoal_4830 4830 7883 7884
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4830_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4830 : (denoteGraph_ringAttn sm initSM 4830).shape = [4096, 512] := by
    rw [hval30, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs7883])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4831
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4830) :=
    ringAttn_reduce1_pm_opaque sm initSM 107
      { rank := 0, op := "OpName.FW_view", ins := [4830], outs := [4831], params := [4096, 512] }
      4830 4831 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4830 4831)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7893
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7883) :=
    ringAttn_reduce1_pm_opaque pm initPM 273
      { rank := 0, op := "OpName.FW_view", ins := [7883], outs := [7893], params := [2048, 512] }
      7883 7893 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 7883 7893)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7894
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7884) :=
    ringAttn_reduce1_pm_opaque pm initPM 277
      { rank := 1, op := "OpName.FW_view", ins := [7884], outs := [7894], params := [2048, 512] }
      7884 7894 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 7884 7894)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h93 : denoteGraph_ringAttn pm initPM 7893 = denoteGraph_ringAttn pm initPM 7883 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs7883]
  have h94 : denoteGraph_ringAttn pm initPM 7894 = denoteGraph_ringAttn pm initPM 7884 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs7884]
  have hval : denoteGraph_ringAttn sm initSM 4831
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7893, denoteGraph_ringAttn pm initPM 7894] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4830, hval30, hnr, ← h93, ← h94]
  have hs7893 : (denoteGraph_ringAttn pm initPM 7893).shape = [2048, 512] := by rw [h93]; exact hs7883
  have hs7894 : (denoteGraph_ringAttn pm initPM 7894).shape = [2048, 512] := by rw [h94]; exact hs7884
  have hs4831 : (denoteGraph_ringAttn sm initSM 4831).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4830]; exact hs4830
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4831 4831 7893 7894 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4831 hs7893 hs7894

/-- 4835 — 2-tp identity view of `4834` → `[4096, 512]` (SM node 108, PM 274/278). -/
theorem recon_intermediateGoal_4835_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4835
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval34, hs7901, hs7902⟩ := twoTp_gather _ _ intermediateGoal_4834 4834 7901 7902
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4834_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4834 : (denoteGraph_ringAttn sm initSM 4834).shape = [4096, 512] := by
    rw [hval34, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs7901])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4835
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4834) :=
    ringAttn_reduce1_pm_opaque sm initSM 108
      { rank := 0, op := "OpName.FW_view", ins := [4834], outs := [4835], params := [4096, 512] }
      4834 4835 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4834 4835)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7911
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7901) :=
    ringAttn_reduce1_pm_opaque pm initPM 274
      { rank := 0, op := "OpName.FW_view", ins := [7901], outs := [7911], params := [2048, 512] }
      7901 7911 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 7901 7911)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7912
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7902) :=
    ringAttn_reduce1_pm_opaque pm initPM 278
      { rank := 1, op := "OpName.FW_view", ins := [7902], outs := [7912], params := [2048, 512] }
      7902 7912 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 7902 7912)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h11 : denoteGraph_ringAttn pm initPM 7911 = denoteGraph_ringAttn pm initPM 7901 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs7901]
  have h12 : denoteGraph_ringAttn pm initPM 7912 = denoteGraph_ringAttn pm initPM 7902 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs7902]
  have hval : denoteGraph_ringAttn sm initSM 4835
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7911, denoteGraph_ringAttn pm initPM 7912] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4834, hval34, hnr, ← h11, ← h12]
  have hs7911 : (denoteGraph_ringAttn pm initPM 7911).shape = [2048, 512] := by rw [h11]; exact hs7901
  have hs7912 : (denoteGraph_ringAttn pm initPM 7912).shape = [2048, 512] := by rw [h12]; exact hs7902
  have hs4835 : (denoteGraph_ringAttn sm initSM 4835).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4834]; exact hs4834
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4835 4835 7911 7912 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4835 hs7911 hs7912

end TrainVerify.Denote.GeneratedPatterns
