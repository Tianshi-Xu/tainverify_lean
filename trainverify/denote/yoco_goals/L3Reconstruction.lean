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

end TrainVerify.Denote.GeneratedPatterns
