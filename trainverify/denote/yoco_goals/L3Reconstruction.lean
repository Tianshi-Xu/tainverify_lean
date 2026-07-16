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

/-! ### L3 MoE gate/expert branch (`4827` sigmoid, `4836` swiglu, `4837` reshape,
    `4839` mixlin, `4840` view, `4841` broadcast-mul), all 2-tp shard-direct. -/

/-- 4827 — 2-tp `fw_sigmoid(4826)` → `[4096, 1]` (SM node 110, PM 280/283). -/
theorem recon_intermediateGoal_4827_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4827
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval26, hs7875, hs7876⟩ := twoTp_gather _ _ intermediateGoal_4826 4826 7875 7876
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4826_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4827 = fw_sigmoid (denoteGraph_ringAttn sm initSM 4826) :=
    ringAttn_reduce1_pm_opaque sm initSM 110
      { rank := 0, op := "OpName.FW_sigmoid", ins := [4826], outs := [4827] }
      4826 4827 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out sm s 0 4826 4827 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7877 = fw_sigmoid (denoteGraph_ringAttn pm initPM 7875) :=
    ringAttn_reduce1_pm_opaque pm initPM 280
      { rank := 0, op := "OpName.FW_sigmoid", ins := [7875], outs := [7877] }
      7875 7877 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 0 7875 7877 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7878 = fw_sigmoid (denoteGraph_ringAttn pm initPM 7876) :=
    ringAttn_reduce1_pm_opaque pm initPM 283
      { rank := 1, op := "OpName.FW_sigmoid", ins := [7876], outs := [7878] }
      7876 7878 fw_sigmoid (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_sigmoid_out pm s 1 7876 7878 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4827
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7877, denoteGraph_ringAttn pm initPM 7878] := by
    rw [rSM, hval26, hnr, fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs7875 hs7876, rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4827).shape = [4096, 1] := by
    rw [rSM, fw_sigmoid_shape]
    rw [hval26, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hs7875])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7877).shape = [2048, 1] := by
    rw [rP0, fw_sigmoid_shape]; exact hs7875
  have hsp1 : (denoteGraph_ringAttn pm initPM 7878).shape = [2048, 1] := by
    rw [rP1, fw_sigmoid_shape]; exact hs7876
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4827 4827 7877 7878 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4836 — 2-tp `fw_swiglu(4831, 4835)` → `[4096, 512]` (SM node 111, PM 281/284). -/
theorem recon_intermediateGoal_4836_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4836
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval31, hs7893, hs7894⟩ := twoTp_gather _ _ intermediateGoal_4831 4831 7893 7894
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4831_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hval35, hs7911, hs7912⟩ := twoTp_gather _ _ intermediateGoal_4835 4835 7911 7912
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4835_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4836
      = fw_swiglu (denoteGraph_ringAttn sm initSM 4831) (denoteGraph_ringAttn sm initSM 4835) :=
    ringAttn_reduce2_pm_opaque sm initSM 111
      { rank := 0, op := "OpName.FW_swiglu", ins := [4831, 4835], outs := [4836] }
      4831 4835 4836 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 4831 4835 4836 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7915
      = fw_swiglu (denoteGraph_ringAttn pm initPM 7893) (denoteGraph_ringAttn pm initPM 7911) :=
    ringAttn_reduce2_pm_opaque pm initPM 281
      { rank := 0, op := "OpName.FW_swiglu", ins := [7893, 7911], outs := [7915] }
      7893 7911 7915 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 7893 7911 7915 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7916
      = fw_swiglu (denoteGraph_ringAttn pm initPM 7894) (denoteGraph_ringAttn pm initPM 7912) :=
    ringAttn_reduce2_pm_opaque pm initPM 284
      { rank := 1, op := "OpName.FW_swiglu", ins := [7894, 7912], outs := [7916] }
      7894 7912 7916 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 7894 7912 7916 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4836
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7915, denoteGraph_ringAttn pm initPM 7916] := by
    rw [rSM, hval31, hval35, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega) hs7893 hs7894 hs7911 hs7912,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4836).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []
    rw [hval35, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs7911])]; simp [List.set, List.getD]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7915).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs7911
  have hsp1 : (denoteGraph_ringAttn pm initPM 7916).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs7912
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4836 4836 7915 7916 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4837 — 2-tp identity reshape of `4836` → `[4096, 512]` (SM node 112, PM 285/286). -/
theorem recon_intermediateGoal_4837_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4837
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval36, hs7915, hs7916⟩ := twoTp_gather _ _ intermediateGoal_4836 4836 7915 7916
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4836_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4836 : (denoteGraph_ringAttn sm initSM 4836).shape = [4096, 512] := by
    rw [hval36, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 512] (by simp [hs7915])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4837
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4836) :=
    ringAttn_reduce1_pm_opaque sm initSM 112
      { rank := 0, op := "OpName.FW_reshape", ins := [4836], outs := [4837], params := [4096, 512] }
      4836 4837 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4836 4837)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7917
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7915) :=
    ringAttn_reduce1_pm_opaque pm initPM 285
      { rank := 0, op := "OpName.FW_reshape", ins := [7915], outs := [7917], params := [2048, 512] }
      7915 7917 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [512] 7915 7917)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7918
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7916) :=
    ringAttn_reduce1_pm_opaque pm initPM 286
      { rank := 1, op := "OpName.FW_reshape", ins := [7916], outs := [7918], params := [2048, 512] }
      7916 7918 (fw_view [2048, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [512] 7916 7918)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h17 : denoteGraph_ringAttn pm initPM 7917 = denoteGraph_ringAttn pm initPM 7915 := by
    rw [rP0, fw_view_id_shape [2048, 512] _ hs7915]
  have h18 : denoteGraph_ringAttn pm initPM 7918 = denoteGraph_ringAttn pm initPM 7916 := by
    rw [rP1, fw_view_id_shape [2048, 512] _ hs7916]
  have hval : denoteGraph_ringAttn sm initSM 4837
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7917, denoteGraph_ringAttn pm initPM 7918] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4836, hval36, hnr, ← h17, ← h18]
  have hs7917 : (denoteGraph_ringAttn pm initPM 7917).shape = [2048, 512] := by rw [h17]; exact hs7915
  have hs7918 : (denoteGraph_ringAttn pm initPM 7918).shape = [2048, 512] := by rw [h18]; exact hs7916
  have hs4837 : (denoteGraph_ringAttn sm initSM 4837).shape = [4096, 512] := by
    rw [rSM, fw_view_id_shape [4096, 512] _ hs4836]; exact hs4836
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4837 4837 7917 7918 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4837 hs7917 hs7918

/-- 4839 — 2-tp `fw_linear(4837, 4838)`, weight `4838 : [1024, 512]` → `[4096, 1024]`
    (SM node 113, PM 287/288). -/
theorem recon_intermediateGoal_4839_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4839
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval37, hs7917, hs7918⟩ := twoTp_gather _ _ intermediateGoal_4837 4837 7917 7918
    [2048, 512] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4837_ringAttn initSM initPM hSM hPM hInit hWF)
  have hw4838 : denoteGraph_ringAttn sm initSM 4838 = denoteGraph_ringAttn pm initPM 4838 :=
    veq_weight_ring initSM initPM hInit initGoal_4838 (by native_decide) 4838
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpw4838 : (denoteGraph_ringAttn pm initPM 4838).shape = [1024, 512] := by
    rw [← hw4838]
    exact shape_weight_ring initSM initPM hInit initGoal_4838 (by native_decide) 4838 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4839
      = fw_linear (denoteGraph_ringAttn sm initSM 4837) (denoteGraph_ringAttn sm initSM 4838) :=
    ringAttn_reduce2_pm_opaque sm initSM 113
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4837, 4838], outs := [4839] }
      4837 4838 4839 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4837 4838 4839)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7923
      = fw_linear (denoteGraph_ringAttn pm initPM 7917) (denoteGraph_ringAttn pm initPM 4838) :=
    ringAttn_reduce2_pm_opaque pm initPM 287
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7917, 4838], outs := [7923] }
      7917 4838 7923 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 0 7917 4838 7923)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7924
      = fw_linear (denoteGraph_ringAttn pm initPM 7918) (denoteGraph_ringAttn pm initPM 4838) :=
    ringAttn_reduce2_pm_opaque pm initPM 288
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7918, 4838], outs := [7924] }
      7918 4838 7924 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 7918 4838 7924)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4839
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7923, denoteGraph_ringAttn pm initPM 7924] := by
    rw [rSM, hval37, hw4838, hnr,
        fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 512 1024
          (by omega) (by omega) (by omega) hs7917 hs7918 hpw4838,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7923).shape = [2048, 1024] := by
    rw [rP0]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs7917 hpw4838
  have hsp1 : (denoteGraph_ringAttn pm initPM 7924).shape = [2048, 1024] := by
    rw [rP1]; exact fw_linear_2d_shape 2048 512 1024 _ _ hs7918 hpw4838
  have hshape : (denoteGraph_ringAttn sm initSM 4839).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4839 4839 7923 7924 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4840 — 2-tp identity view of `4839` → `[4096, 1024]` (SM node 114, PM 289/290). -/
theorem recon_intermediateGoal_4840_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4840
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hval39, hs7923, hs7924⟩ := twoTp_gather _ _ intermediateGoal_4839 4839 7923 7924
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4839_ringAttn initSM initPM hSM hPM hInit hWF)
  have hs4839 : (denoteGraph_ringAttn sm initSM 4839).shape = [4096, 1024] := by
    rw [hval39, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hs7923])]
    simp [List.set, List.getD]
  have rSM : denoteGraph_ringAttn sm initSM 4840
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4839) :=
    ringAttn_reduce1_pm_opaque sm initSM 114
      { rank := 0, op := "OpName.FW_view", ins := [4839], outs := [4840], params := [4096, 1024] }
      4839 4840 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4839 4840)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7933
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7923) :=
    ringAttn_reduce1_pm_opaque pm initPM 289
      { rank := 0, op := "OpName.FW_view", ins := [7923], outs := [7933], params := [2048, 1024] }
      7923 7933 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 0 2048 [1024] 7923 7933)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7934
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7924) :=
    ringAttn_reduce1_pm_opaque pm initPM 290
      { rank := 1, op := "OpName.FW_view", ins := [7924], outs := [7934], params := [2048, 1024] }
      7924 7934 (fw_view [2048, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 2048 [1024] 7924 7934)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have h33 : denoteGraph_ringAttn pm initPM 7933 = denoteGraph_ringAttn pm initPM 7923 := by
    rw [rP0, fw_view_id_shape [2048, 1024] _ hs7923]
  have h34 : denoteGraph_ringAttn pm initPM 7934 = denoteGraph_ringAttn pm initPM 7924 := by
    rw [rP1, fw_view_id_shape [2048, 1024] _ hs7924]
  have hval : denoteGraph_ringAttn sm initSM 4840
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7933, denoteGraph_ringAttn pm initPM 7934] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4839, hval39, hnr, ← h33, ← h34]
  have hs7933 : (denoteGraph_ringAttn pm initPM 7933).shape = [2048, 1024] := by rw [h33]; exact hs7923
  have hs7934 : (denoteGraph_ringAttn pm initPM 7934).shape = [2048, 1024] := by rw [h34]; exact hs7924
  have hs4840 : (denoteGraph_ringAttn sm initSM 4840).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4839]; exact hs4839
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4840 4840 7933 7934 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hs4840 hs7933 hs7934

/-- 4841 — 2-tp broadcast `mul(4827, 4840)` → `[4096, 1024]` (SM node 115, PM 291/292). -/
theorem recon_intermediateGoal_4841_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4841
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hvalS, hsS0, hsS1⟩ := twoTp_gather _ _ intermediateGoal_4827 4827 7877 7878
    [2048, 1] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4827_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hvalV, hsV0, hsV1⟩ := twoTp_gather _ _ intermediateGoal_4840 4840 7933 7934
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4840_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4841
      = elemwiseMul (denoteGraph_ringAttn sm initSM 4827) (denoteGraph_ringAttn sm initSM 4840) :=
    ringAttn_reduce2_pm_opaque sm initSM 115
      { rank := 0, op := "OpName.FW_mul", ins := [4827, 4840], outs := [4841] }
      4827 4840 4841 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 4827 4840 4841)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7937
      = elemwiseMul (denoteGraph_ringAttn pm initPM 7877) (denoteGraph_ringAttn pm initPM 7933) :=
    ringAttn_reduce2_pm_opaque pm initPM 291
      { rank := 0, op := "OpName.FW_mul", ins := [7877, 7933], outs := [7937] }
      7877 7933 7937 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 0 7877 7933 7937)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7938
      = elemwiseMul (denoteGraph_ringAttn pm initPM 7878) (denoteGraph_ringAttn pm initPM 7934) :=
    ringAttn_reduce2_pm_opaque pm initPM 292
      { rank := 1, op := "OpName.FW_mul", ins := [7878, 7934], outs := [7938] }
      7878 7934 7938 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 7878 7934 7938)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4841
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7937, denoteGraph_ringAttn pm initPM 7938] := by
    rw [rSM, hvalS, hvalV, hnr,
        fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide) hsS0 hsS1 hsV0 hsV1,
        rP0, rP1]
  have mulBShape : ∀ (x y : Tensor) (a : Nat),
      x.shape = [a, 1] → y.shape = [a, 1024] → (elemwiseMul x y).shape = [a, 1024] := by
    intro x y a hx hy
    show outShape2 x y = [a, 1024]
    unfold outShape2
    rw [hx, hy]
    show (max a a) :: (1024 : Nat) :: [] = [a, 1024]
    rw [Nat.max_self]
  have hshape : (denoteGraph_ringAttn sm initSM 4841).shape = [4096, 1024] := by
    rw [rSM]
    have hsSfull : (denoteGraph_ringAttn sm initSM 4827).shape = [4096, 1] := by
      rw [hvalS, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1] (by simp [hsS0])]; simp [List.set, List.getD]
    have hsVfull : (denoteGraph_ringAttn sm initSM 4840).shape = [4096, 1024] := by
      rw [hvalV, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsV0])]; simp [List.set, List.getD]
    exact mulBShape _ _ 4096 hsSfull hsVfull
  have hsp0 : (denoteGraph_ringAttn pm initPM 7937).shape = [2048, 1024] := by
    rw [rP0]; exact mulBShape _ _ 2048 hsS0 hsV0
  have hsp1 : (denoteGraph_ringAttn pm initPM 7938).shape = [2048, 1024] := by
    rw [rP1]; exact mulBShape _ _ 2048 hsS1 hsV1
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4841 4841 7937 7938 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-! ### 4822 — layer-3 expert-parallel MoE all2all (2-tp, expert-sharded)

    `SM 4822 = fw_all2all_moe_gmm` over experts `[0, 64)` (params `[64, 0, 64, 8]`).
    PM shards experts across 2 ranks: rank 0 → `[0, 32)` (`7863`), rank 1 →
    `[32, 64)` (`7864`), reconstructed via `fw_all2all_moe_gmm_split_commute_2_of`
    given the per-rank routing maps `7855`/`7856` are expert-local (the
    `wf4822_hdisjA/B` fields).  Token input `7523 = mref5-pos1(4813)`; unlike L2
    there is no gather-to-full/chunk, so the token bridge is a direct mref5
    position bridge (SM node 109, PM nodes 279/282). -/
theorem recon_intermediateGoal_4822_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4822
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  -- Token bridge: 7523 = mref5-pos1(4813).
  obtain ⟨hbr13, hs7843, hs7844⟩ := twoTp_gather _ _ intermediateGoal_4813 4813 7843 7844
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4813_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7523 : denoteGraph_ringAttn sm initSM 7523 = id (denoteGraph_ringAttn sm initSM 4813) :=
    ringAttn_reduce1_pm_opaque sm initSM 96
      { rank := 0, op := "OpName.FW_multiref", ins := [4813],
        outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
      4813 7523 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out sm s 0 4813 7519 7523 7527 7531 7535 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14766 : denoteGraph_ringAttn pm initPM 14766 = id (denoteGraph_ringAttn pm initPM 7843) :=
    ringAttn_reduce1_pm_opaque pm initPM 253
      { rank := 0, op := "OpName.FW_multiref", ins := [7843],
        outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
      7843 14766 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 0 7843 14762 14766 14770 14774 14778 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14789 : denoteGraph_ringAttn pm initPM 14789 = id (denoteGraph_ringAttn pm initPM 7844) :=
    ringAttn_reduce1_pm_opaque pm initPM 254
      { rank := 1, op := "OpName.FW_multiref", ins := [7844],
        outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
      7844 14789 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos1_out pm s 1 7844 14785 14789 14793 14797 14801 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7523 p14766 p14789
  have hsInA : (denoteGraph_ringAttn pm initPM 14766).shape = [2048, 1024] := by
    rw [p14766]; exact hs7843
  have hsInB : (denoteGraph_ringAttn pm initPM 14789).shape = [2048, 1024] := by
    rw [p14789]; exact hs7844
  have hbrIn : denoteGraph_ringAttn sm initSM 7523
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 14766, denoteGraph_ringAttn pm initPM 14789] := by
    rw [s7523, hbr13, hnr, ← p14766, ← p14789]
  -- Routing-probs / routing-map bridges (already 2-tp, no chunk).
  obtain ⟨hbrRp0, hsRpA, hsRpB⟩ := twoTp_gather _ _ intermediateGoal_4817 4817 7853 7854
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4817_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbrRm0, hsRmA, hsRmB⟩ := twoTp_gather _ _ intermediateGoal_4818 4818 7855 7856
    [2048, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4818_ringAttn initSM initPM hSM hPM hInit hWF)
  have hbrRp : denoteGraph_ringAttn sm initSM 4817
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7853, denoteGraph_ringAttn pm initPM 7854] := by
    rw [hbrRp0, hnr]
  have hbrRm : denoteGraph_ringAttn sm initSM 4818
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7855, denoteGraph_ringAttn pm initPM 7856] := by
    rw [hbrRm0, hnr]
  -- Weight bridges (dual-tp init goals, expert-axis gatherDim 0).
  have hbrW13 := veq_weight_dual_ring initSM initPM hInit initGoal_4820
    (by native_decide) 4820 7859 7860 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2 := veq_weight_dual_ring initSM initPM hInit initGoal_4821
    (by native_decide) 4821 7861 7862 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- Weight shard shapes from the init goals.
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraph_ringAttn pm initPM 7859).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4820 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4820, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7859 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraph_ringAttn pm initPM 7860).shape = [32, 1024, 1024] := by
    have h := hpres initGoal_4820 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4820, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7860 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraph_ringAttn pm initPM 7861).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4821 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4821, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7861 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraph_ringAttn pm initPM 7862).shape = [32, 1024, 512] := by
    have h := hpres initGoal_4821 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4821, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7862 (by native_decide)]; exact hs.2
  -- SM 4822 = full-range all2all (SM node 109).
  have hSMout : denoteGraph_ringAttn sm initSM 4822
      = fw_all2all_moe_gmm (denoteGraph_ringAttn sm initSM 7523)
          (denoteGraph_ringAttn sm initSM 4817) (denoteGraph_ringAttn sm initSM 4818)
          (denoteGraph_ringAttn sm initSM 4820) (denoteGraph_ringAttn sm initSM 4821)
          64 0 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque sm initSM 109
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7523, 4817, 4818, 4820, 4821],
        outs := [4822], params := [64, 0, 64, 8] }
      7523 4817 4818 4820 4821 4822
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm s 0 7523 4817 4818 4820 4821 4822 [64, 0, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 7863 = rank-0 sharded-range all2all (PM node 279).
  have hP0 : denoteGraph_ringAttn pm initPM 7863
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 14766)
          (denoteGraph_ringAttn pm initPM 7853) (denoteGraph_ringAttn pm initPM 7855)
          (denoteGraph_ringAttn pm initPM 7859) (denoteGraph_ringAttn pm initPM 7861)
          64 0 32 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 279
      { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14766, 7853, 7855, 7859, 7861],
        outs := [7863], params := [64, 0, 32, 8] }
      14766 7853 7855 7859 7861 7863
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 0 32 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 0 14766 7853 7855 7859 7861 7863 [64, 0, 32, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM 7864 = rank-1 sharded-range all2all (PM node 282).
  have hP1 : denoteGraph_ringAttn pm initPM 7864
      = fw_all2all_moe_gmm (denoteGraph_ringAttn pm initPM 14789)
          (denoteGraph_ringAttn pm initPM 7854) (denoteGraph_ringAttn pm initPM 7856)
          (denoteGraph_ringAttn pm initPM 7860) (denoteGraph_ringAttn pm initPM 7862)
          64 32 64 8 (((10 : Nat) : Scalar)) :=
    ringAttn_reduce5_pm_opaque pm initPM 282
      { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14789, 7854, 7856, 7860, 7862],
        outs := [7864], params := [64, 32, 64, 8] }
      14789 7854 7856 7860 7862 7864
      (fun a b c d e => fw_all2all_moe_gmm a b c d e 64 32 64 8 (((10 : Nat) : Scalar)))
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_all2all_moe_gmm_out_1p pm s 1 14789 7854 7856 7860 7862 7864 [64, 32, 64, 8])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := fw_all2all_moe_gmm_split_commute_2_of
      (denoteGraph_ringAttn pm initPM 14766) (denoteGraph_ringAttn pm initPM 14789)
      (denoteGraph_ringAttn pm initPM 7853) (denoteGraph_ringAttn pm initPM 7854)
      (denoteGraph_ringAttn pm initPM 7855) (denoteGraph_ringAttn pm initPM 7856)
      (denoteGraph_ringAttn pm initPM 7859) (denoteGraph_ringAttn pm initPM 7860)
      (denoteGraph_ringAttn pm initPM 7861) (denoteGraph_ringAttn pm initPM 7862)
      2048 1024 1024 512 32 8
      (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
      hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
      (fun l hl e he hge => hWF.wf4822_hdisjA l hl e he (Or.inr hge))
      (fun l hl e he hlt => hWF.wf4822_hdisjB l hl e he (Or.inl hlt))
      (((10 : Nat) : Scalar))
  have hval : denoteGraph_ringAttn sm initSM 4822
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7863, denoteGraph_ringAttn pm initPM 7864] := by
    rw [hSMout, hbrIn, hbrRp, hbrRm, hbrW13, hbrW2, hc, ← hP0, ← hP1, hnr]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7863).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInA]; rfl) (by rw [hsInA]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 7864).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_shape _ _ _ _ _ _ _ _ _ _ 2048 1024
      (by rw [hsInB]; rfl) (by rw [hsInB]; rfl)
  have hshape : (denoteGraph_ringAttn sm initSM 4822).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4822 4822 7863 7864 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ## L3 residual tail (add/float/add) + RMSNorm + per-head Q/K/V + rotary (2-tp) -/

/-- 7512 — second position of the L3 pre-MoE residual `mref2(4811)` (2-tp, PM
    shards `14747`/`14755`).  Unlike L2's `7460` there is no gather-to-full/chunk
    because `4811` is already 2-tp; the bridge is a direct `mref2`-second position
    bridge (SM node 94, PM nodes 243/244). -/
theorem recon_intermediateGoal_7512_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7512
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr11, hs7839, hs7840⟩ := twoTp_gather _ _ intermediateGoal_4811 4811 7839 7840
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4811_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7512 : denoteGraph_ringAttn sm initSM 7512 = id (denoteGraph_ringAttn sm initSM 4811) :=
    ringAttn_reduce1_pm_opaque sm initSM 94
      { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512], params := [2] }
      4811 7512 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4811 7508 7512 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14747 : denoteGraph_ringAttn pm initPM 14747 = id (denoteGraph_ringAttn pm initPM 7839) :=
    ringAttn_reduce1_pm_opaque pm initPM 249
      { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747], params := [2] }
      7839 14747 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 0 7839 14743 14747 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14755 : denoteGraph_ringAttn pm initPM 14755 = id (denoteGraph_ringAttn pm initPM 7840) :=
    ringAttn_reduce1_pm_opaque pm initPM 250
      { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755], params := [2] }
      7840 14755 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 7840 14751 14755 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7512 p14747 p14755
  have hsp0 : (denoteGraph_ringAttn pm initPM 14747).shape = [2048, 1024] := by
    rw [p14747]; exact hs7839
  have hsp1 : (denoteGraph_ringAttn pm initPM 14755).shape = [2048, 1024] := by
    rw [p14755]; exact hs7840
  have hval : denoteGraph_ringAttn sm initSM 7512
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14747, denoteGraph_ringAttn pm initPM 14755] := by
    rw [s7512, hbr11, ← p14747, ← p14755]
  have hshape : (denoteGraph_ringAttn sm initSM 7512).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_7512 7512 14747 14755 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4842 — post-MoE residual add `4822 + 4841` (2-tp, PM `7941`/`7942`). -/
theorem recon_intermediateGoal_4842_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4842
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr22, hs7863, hs7864⟩ := twoTp_gather _ _ intermediateGoal_4822 4822 7863 7864
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4822_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr41, hs7937, hs7938⟩ := twoTp_gather _ _ intermediateGoal_4841 4841 7937 7938
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4841_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4842
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 4822) (denoteGraph_ringAttn sm initSM 4841) :=
    ringAttn_reduce2_pm_opaque sm initSM 116
      { rank := 0, op := "OpName.FW_add", ins := [4822, 4841], outs := [4842] }
      4822 4841 4842 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 4822 4841 4842)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7941
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 7863) (denoteGraph_ringAttn pm initPM 7937) :=
    ringAttn_reduce2_pm_opaque pm initPM 293
      { rank := 0, op := "OpName.FW_add", ins := [7863, 7937], outs := [7941] }
      7863 7937 7941 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 7863 7937 7941)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7942
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 7864) (denoteGraph_ringAttn pm initPM 7938) :=
    ringAttn_reduce2_pm_opaque pm initPM 294
      { rank := 1, op := "OpName.FW_add", ins := [7864, 7938], outs := [7942] }
      7864 7938 7942 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 7864 7938 7942)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4842
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7941, denoteGraph_ringAttn pm initPM 7942] := by
    rw [rSM, hbr22, hbr41, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs7863 hs7864 hs7937 hs7938,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7941).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs7863 hs7937
  have hsp1 : (denoteGraph_ringAttn pm initPM 7942).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs7864 hs7938
  have hshape : (denoteGraph_ringAttn sm initSM 4842).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4842 4842 7941 7942 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4843 — `FW_float(4842)` (identity, 2-tp PM `7947`/`7948`). -/
theorem recon_intermediateGoal_4843_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4843
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr42, hs7941, hs7942⟩ := twoTp_gather _ _ intermediateGoal_4842 4842 7941 7942
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4842_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4843 = id (denoteGraph_ringAttn sm initSM 4842) :=
    ringAttn_reduce1_pm_opaque sm initSM 117
      { rank := 0, op := "OpName.FW_float", ins := [4842], outs := [4843] }
      4842 4843 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4842 4843 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7947 = id (denoteGraph_ringAttn pm initPM 7941) :=
    ringAttn_reduce1_pm_opaque pm initPM 295
      { rank := 0, op := "OpName.FW_float", ins := [7941], outs := [7947] }
      7941 7947 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 0 7941 7947 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7948 = id (denoteGraph_ringAttn pm initPM 7942) :=
    ringAttn_reduce1_pm_opaque pm initPM 296
      { rank := 1, op := "OpName.FW_float", ins := [7942], outs := [7948] }
      7942 7948 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 7942 7948 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rP0 rP1
  have hval : denoteGraph_ringAttn sm initSM 4843
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7947, denoteGraph_ringAttn pm initPM 7948] := by
    rw [rSM, hbr42, ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7947).shape = [2048, 1024] := by rw [rP0]; exact hs7941
  have hsp1 : (denoteGraph_ringAttn pm initPM 7948).shape = [2048, 1024] := by rw [rP1]; exact hs7942
  have hshape : (denoteGraph_ringAttn sm initSM 4843).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4843 4843 7947 7948 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4844 — cross-block residual add `7512 + 4843` (2-tp, PM `7951`/`7952`). -/
theorem recon_intermediateGoal_4844_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4844
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr12, hs14747, hs14755⟩ := twoTp_gather _ _ intermediateGoal_7512 7512 14747 14755
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7512_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr43, hs7947, hs7948⟩ := twoTp_gather _ _ intermediateGoal_4843 4843 7947 7948
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4843_ringAttn initSM initPM hSM hPM hInit hWF)
  have rSM : denoteGraph_ringAttn sm initSM 4844
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7512) (denoteGraph_ringAttn sm initSM 4843) :=
    ringAttn_reduce2_pm_opaque sm initSM 118
      { rank := 0, op := "OpName.FW_add", ins := [7512, 4843], outs := [4844] }
      7512 4843 4844 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7512 4843 4844)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7951
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14747) (denoteGraph_ringAttn pm initPM 7947) :=
    ringAttn_reduce2_pm_opaque pm initPM 297
      { rank := 0, op := "OpName.FW_add", ins := [14747, 7947], outs := [7951] }
      14747 7947 7951 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 0 14747 7947 7951)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7952
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14755) (denoteGraph_ringAttn pm initPM 7948) :=
    ringAttn_reduce2_pm_opaque pm initPM 298
      { rank := 1, op := "OpName.FW_add", ins := [14755, 7948], outs := [7952] }
      14755 7948 7952 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14755 7948 7952)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4844
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7951, denoteGraph_ringAttn pm initPM 7952] := by
    rw [rSM, hbr12, hbr43, hnr,
        fw_add_allGather0_commute_2_2048_1024 _ _ _ _ hs14747 hs14755 hs7947 hs7948,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7951).shape = [2048, 1024] := by
    rw [rP0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14747 hs7947
  have hsp1 : (denoteGraph_ringAttn pm initPM 7952).shape = [2048, 1024] := by
    rw [rP1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] hs14755 hs7948
  have hshape : (denoteGraph_ringAttn sm initSM 4844).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4844 4844 7951 7952 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4846 — RMSNorm of `mref2-first(4844)` with replicated weight `4845`
    (2-tp, PM `7955`/`7956`). -/
theorem recon_intermediateGoal_4846_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4846
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr44, hs7951, hs7952⟩ := twoTp_gather _ _ intermediateGoal_4844 4844 7951 7952
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4844_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7539 : denoteGraph_ringAttn sm initSM 7539 = id (denoteGraph_ringAttn sm initSM 4844) :=
    ringAttn_reduce1_pm_opaque sm initSM 119
      { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543], params := [2] }
      4844 7539 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4844 7539 7543)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14805 : denoteGraph_ringAttn pm initPM 14805 = id (denoteGraph_ringAttn pm initPM 7951) :=
    ringAttn_reduce1_pm_opaque pm initPM 299
      { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809], params := [2] }
      7951 14805 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 0 7951 14805 14809)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14813 : denoteGraph_ringAttn pm initPM 14813 = id (denoteGraph_ringAttn pm initPM 7952) :=
    ringAttn_reduce1_pm_opaque pm initPM 300
      { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817], params := [2] }
      7952 14813 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 7952 14813 14817)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7539 p14805 p14813
  have hs14805 : (denoteGraph_ringAttn pm initPM 14805).shape = [2048, 1024] := by
    rw [p14805]; exact hs7951
  have hs14813 : (denoteGraph_ringAttn pm initPM 14813).shape = [2048, 1024] := by
    rw [p14813]; exact hs7952
  have hbr39 : denoteGraph_ringAttn sm initSM 7539
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14805, denoteGraph_ringAttn pm initPM 14813] := by
    rw [s7539, hbr44, ← p14805, ← p14813]
  have hw4845 : denoteGraph_ringAttn sm initSM 4845 = denoteGraph_ringAttn pm initPM 4845 :=
    veq_weight_ring initSM initPM hInit initGoal_4845 (by native_decide) 4845
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4846
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7539) (denoteGraph_ringAttn sm initSM 4845) :=
    ringAttn_reduce2_pm_opaque sm initSM 120
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7539, 4845], outs := [4846] }
      7539 4845 4846 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7539 4845 4846)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7955
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14805) (denoteGraph_ringAttn pm initPM 4845) :=
    ringAttn_reduce2_pm_opaque pm initPM 301
      { rank := 0, op := "OpName.FW_rms_norm", ins := [14805, 4845], outs := [7955] }
      14805 4845 7955 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 0 14805 4845 7955)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7956
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14813) (denoteGraph_ringAttn pm initPM 4845) :=
    ringAttn_reduce2_pm_opaque pm initPM 302
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14813, 4845], outs := [7956] }
      14813 4845 7956 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14813 4845 7956)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4846
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7955, denoteGraph_ringAttn pm initPM 7956] := by
    rw [rSM, hbr39, hw4845, hnr,
        fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs14805 hs14813,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7955).shape = [2048, 1024] := by
    rw [rP0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14805
  have hsp1 : (denoteGraph_ringAttn pm initPM 7956).shape = [2048, 1024] := by
    rw [rP1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs14813
  have hshape : (denoteGraph_ringAttn sm initSM 4846).shape = [4096, 1024] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4846 4846 7955 7956 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4848 — per-head Q projection `fw_per_head_linear(mref3₀(4846), 4847)`
    (2-tp, PM `7957`/`7958`, weight `4847 : [16,64,1024]`). -/
theorem recon_intermediateGoal_4848_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4848
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs7955, hs7956⟩ := twoTp_gather _ _ intermediateGoal_4846 4846 7955 7956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4846_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7548 : denoteGraph_ringAttn sm initSM 7548 = id (denoteGraph_ringAttn sm initSM 4846) :=
    ringAttn_reduce1_pm_opaque sm initSM 121
      { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
      4846 7548 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4846 7548 7552 7556)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14822 : denoteGraph_ringAttn pm initPM 14822 = id (denoteGraph_ringAttn pm initPM 7955) :=
    ringAttn_reduce1_pm_opaque pm initPM 303
      { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
      7955 14822 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 0 7955 14822 14826 14830)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14835 : denoteGraph_ringAttn pm initPM 14835 = id (denoteGraph_ringAttn pm initPM 7956) :=
    ringAttn_reduce1_pm_opaque pm initPM 304
      { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
      7956 14835 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 7956 14835 14839 14843)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7548 p14822 p14835
  have hs14822 : (denoteGraph_ringAttn pm initPM 14822).shape = [2048, 1024] := by
    rw [p14822]; exact hs7955
  have hs14835 : (denoteGraph_ringAttn pm initPM 14835).shape = [2048, 1024] := by
    rw [p14835]; exact hs7956
  have hbr48 : denoteGraph_ringAttn sm initSM 7548
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14822, denoteGraph_ringAttn pm initPM 14835] := by
    rw [s7548, hbr46, ← p14822, ← p14835]
  have hw4847 : denoteGraph_ringAttn sm initSM 4847 = denoteGraph_ringAttn pm initPM 4847 :=
    veq_weight_ring initSM initPM hInit initGoal_4847 (by native_decide) 4847
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4847 : (denoteGraph_ringAttn sm initSM 4847).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4847 (by native_decide) 4847 [16, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4847 : (denoteGraph_ringAttn pm initPM 4847).shape = [16, 64, 1024] := by
    rw [← hw4847]; exact hsw4847
  have rSM : denoteGraph_ringAttn sm initSM 4848
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7548) (denoteGraph_ringAttn sm initSM 4847) :=
    ringAttn_reduce2_pm_opaque sm initSM 122
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7548, 4847], outs := [4848] }
      7548 4847 4848 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7548 4847 4848 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7957
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14822) (denoteGraph_ringAttn pm initPM 4847) :=
    ringAttn_reduce2_pm_opaque pm initPM 305
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14822, 4847], outs := [7957] }
      14822 4847 7957 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 14822 4847 7957 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7958
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14835) (denoteGraph_ringAttn pm initPM 4847) :=
    ringAttn_reduce2_pm_opaque pm initPM 308
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14835, 4847], outs := [7958] }
      14835 4847 7958 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14835 4847 7958 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4848
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7957, denoteGraph_ringAttn pm initPM 7958] := by
    rw [rSM, hbr48, hw4847, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
          (by omega) (by omega) (by omega) (by omega) hs14822 hs14835 hpw4847,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7957).shape = [2048, 16, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs14822 hpw4847
  have hsp1 : (denoteGraph_ringAttn pm initPM 7958).shape = [2048, 16, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs14835 hpw4847
  have hshape : (denoteGraph_ringAttn sm initSM 4848).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4848 4848 7957 7958 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4850 — per-head K projection `fw_per_head_linear(mref3₁(4846), 4849)`
    (2-tp, PM `7969`/`7970`, weight `4849 : [4,64,1024]`). -/
theorem recon_intermediateGoal_4850_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4850
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs7955, hs7956⟩ := twoTp_gather _ _ intermediateGoal_4846 4846 7955 7956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4846_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7552 : denoteGraph_ringAttn sm initSM 7552 = id (denoteGraph_ringAttn sm initSM 4846) :=
    ringAttn_reduce1_pm_opaque sm initSM 121
      { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
      4846 7552 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4846 7548 7552 7556 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14826 : denoteGraph_ringAttn pm initPM 14826 = id (denoteGraph_ringAttn pm initPM 7955) :=
    ringAttn_reduce1_pm_opaque pm initPM 303
      { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
      7955 14826 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 0 7955 14822 14826 14830 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14839 : denoteGraph_ringAttn pm initPM 14839 = id (denoteGraph_ringAttn pm initPM 7956) :=
    ringAttn_reduce1_pm_opaque pm initPM 304
      { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
      7956 14839 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 7956 14835 14839 14843 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7552 p14826 p14839
  have hs14826 : (denoteGraph_ringAttn pm initPM 14826).shape = [2048, 1024] := by
    rw [p14826]; exact hs7955
  have hs14839 : (denoteGraph_ringAttn pm initPM 14839).shape = [2048, 1024] := by
    rw [p14839]; exact hs7956
  have hbr52 : denoteGraph_ringAttn sm initSM 7552
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14826, denoteGraph_ringAttn pm initPM 14839] := by
    rw [s7552, hbr46, ← p14826, ← p14839]
  have hw4849 : denoteGraph_ringAttn sm initSM 4849 = denoteGraph_ringAttn pm initPM 4849 :=
    veq_weight_ring initSM initPM hInit initGoal_4849 (by native_decide) 4849
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4849 : (denoteGraph_ringAttn sm initSM 4849).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4849 (by native_decide) 4849 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4849 : (denoteGraph_ringAttn pm initPM 4849).shape = [4, 64, 1024] := by
    rw [← hw4849]; exact hsw4849
  have rSM : denoteGraph_ringAttn sm initSM 4850
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7552) (denoteGraph_ringAttn sm initSM 4849) :=
    ringAttn_reduce2_pm_opaque sm initSM 123
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7552, 4849], outs := [4850] }
      7552 4849 4850 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7552 4849 4850 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7969
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14826) (denoteGraph_ringAttn pm initPM 4849) :=
    ringAttn_reduce2_pm_opaque pm initPM 306
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14826, 4849], outs := [7969] }
      14826 4849 7969 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 14826 4849 7969 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7970
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14839) (denoteGraph_ringAttn pm initPM 4849) :=
    ringAttn_reduce2_pm_opaque pm initPM 309
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14839, 4849], outs := [7970] }
      14839 4849 7970 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14839 4849 7970 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4850
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7969, denoteGraph_ringAttn pm initPM 7970] := by
    rw [rSM, hbr52, hw4849, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs14826 hs14839 hpw4849,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7969).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14826 hpw4849
  have hsp1 : (denoteGraph_ringAttn pm initPM 7970).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14839 hpw4849
  have hshape : (denoteGraph_ringAttn sm initSM 4850).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4850 4850 7969 7970 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4852 — per-head V projection `fw_per_head_linear(mref3₂(4846), 4851)`
    (2-tp, PM `7979`/`7980`, weight `4851 : [4,64,1024]`). -/
theorem recon_intermediateGoal_4852_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4852
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr46, hs7955, hs7956⟩ := twoTp_gather _ _ intermediateGoal_4846 4846 7955 7956
    [2048, 1024] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4846_ringAttn initSM initPM hSM hPM hInit hWF)
  have s7556 : denoteGraph_ringAttn sm initSM 7556 = id (denoteGraph_ringAttn sm initSM 4846) :=
    ringAttn_reduce1_pm_opaque sm initSM 121
      { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
      4846 7556 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4846 7548 7552 7556 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14830 : denoteGraph_ringAttn pm initPM 14830 = id (denoteGraph_ringAttn pm initPM 7955) :=
    ringAttn_reduce1_pm_opaque pm initPM 303
      { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
      7955 14830 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 0 7955 14822 14826 14830 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14843 : denoteGraph_ringAttn pm initPM 14843 = id (denoteGraph_ringAttn pm initPM 7956) :=
    ringAttn_reduce1_pm_opaque pm initPM 304
      { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
      7956 14843 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 7956 14835 14839 14843 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7556 p14830 p14843
  have hs14830 : (denoteGraph_ringAttn pm initPM 14830).shape = [2048, 1024] := by
    rw [p14830]; exact hs7955
  have hs14843 : (denoteGraph_ringAttn pm initPM 14843).shape = [2048, 1024] := by
    rw [p14843]; exact hs7956
  have hbr56 : denoteGraph_ringAttn sm initSM 7556
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 14830, denoteGraph_ringAttn pm initPM 14843] := by
    rw [s7556, hbr46, ← p14830, ← p14843]
  have hw4851 : denoteGraph_ringAttn sm initSM 4851 = denoteGraph_ringAttn pm initPM 4851 :=
    veq_weight_ring initSM initPM hInit initGoal_4851 (by native_decide) 4851
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4851 : (denoteGraph_ringAttn sm initSM 4851).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4851 (by native_decide) 4851 [4, 64, 1024]
      rfl rfl (by native_decide)
  have hpw4851 : (denoteGraph_ringAttn pm initPM 4851).shape = [4, 64, 1024] := by
    rw [← hw4851]; exact hsw4851
  have rSM : denoteGraph_ringAttn sm initSM 4852
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7556) (denoteGraph_ringAttn sm initSM 4851) :=
    ringAttn_reduce2_pm_opaque sm initSM 124
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7556, 4851], outs := [4852] }
      7556 4851 4852 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7556 4851 4852 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7979
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14830) (denoteGraph_ringAttn pm initPM 4851) :=
    ringAttn_reduce2_pm_opaque pm initPM 307
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14830, 4851], outs := [7979] }
      14830 4851 7979 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 0 14830 4851 7979 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7980
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14843) (denoteGraph_ringAttn pm initPM 4851) :=
    ringAttn_reduce2_pm_opaque pm initPM 310
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14843, 4851], outs := [7980] }
      14843 4851 7980 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14843 4851 7980 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4852
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7979, denoteGraph_ringAttn pm initPM 7980] := by
    rw [rSM, hbr56, hw4851, hnr,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega) hs14830 hs14843 hpw4851,
        ← rP0, ← rP1]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7979).shape = [2048, 4, 64] := by
    rw [rP0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14830 hpw4851
  have hsp1 : (denoteGraph_ringAttn pm initPM 7980).shape = [2048, 4, 64] := by
    rw [rP1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs14843 hpw4851
  have hshape : (denoteGraph_ringAttn sm initSM 4852).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4852 4852 7979 7980 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- L3 rotary cos/sin cache agreement: `sm 4691 = pm 11856` (`= 11853 + 3`). -/
theorem hcache_4691_11856 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11856 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11856 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11856 3 (by norm_num) rfl

set_option maxHeartbeats 8000000 in
/-- 4854 — rotary-embedding Q output `rotary(4691, 4853, 4848, 4850).1`
    (2-tp, PM `7991`/`7992`; positions `4853 : [4096]` chunked per rank). -/
theorem recon_intermediateGoal_4854_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4854
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, hs7957, hs7958⟩ := twoTp_gather _ _ intermediateGoal_4848 4848 7957 7958
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4848_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, _, _⟩ := twoTp_gather _ _ intermediateGoal_4850 4850 7969 7970
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4850_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11856 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 4853 = denoteGraph_ringAttn pm initPM 4853 :=
    veq_weight_ring initSM initPM hInit initGoal_4853 (by native_decide) 4853
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp4853 : (denoteGraph_ringAttn sm initSM 4853).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_4853 (by native_decide) 4853 [4096]
      rfl rfl (by native_decide)
  have c7989 : denoteGraph_ringAttn pm initPM 7989
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4853) :=
    ringAttn_reduce1_pm_opaque pm initPM 3
      { rank := 0, op := "OpName.ChunkPrim", ins := [4853], outs := [7989], params := [0] }
      4853 7989 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4853 7989 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c7990 : denoteGraph_ringAttn pm initPM 7990
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4853) :=
    ringAttn_reduce1_pm_opaque pm initPM 16
      { rank := 1, op := "OpName.ChunkPrim", ins := [4853], outs := [7990], params := [0] }
      4853 7990 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4853 7990 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4854
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4853)
          (denoteGraph_ringAttn sm initSM 4848) (denoteGraph_ringAttn sm initSM 4850) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 125
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4853, 4848, 4850], outs := [4854, 4855], params := [16, 4] }
          4854 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 125 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 125 4853 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 125 4848 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 125 4850 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 7991
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11856) (denoteGraph_ringAttn pm initPM 7989)
          (denoteGraph_ringAttn pm initPM 7957) (denoteGraph_ringAttn pm initPM 7969) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 311
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11856, 7989, 7957, 7969], outs := [7991, 7993], params := [16, 4] }
          7991 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 311 11856 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 311 7989 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 311 7957 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 311 7969 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 7992
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11856) (denoteGraph_ringAttn pm initPM 7990)
          (denoteGraph_ringAttn pm initPM 7958) (denoteGraph_ringAttn pm initPM 7970) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 312
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11856, 7990, 7958, 7970], outs := [7992, 7994], params := [16, 4] }
          7992 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 312 11856 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 312 7990 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 312 7958 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 312 7970 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4854
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7991, denoteGraph_ringAttn pm initPM 7992] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr48, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 4853) (denoteGraph_ringAttn pm initPM 7957)
          (denoteGraph_ringAttn pm initPM 7958) 2048 16 64 (by omega) (by omega) (by omega)
          hsp4853 hs7957 hs7958,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 7989
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 4853) from c7989),
        ← (show denoteGraph_ringAttn pm initPM 7990
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 4853) from c7990),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7991).shape = [2048, 16, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs7957
  have hsp1 : (denoteGraph_ringAttn pm initPM 7992).shape = [2048, 16, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hs7958
  have hshape : (denoteGraph_ringAttn sm initSM 4854).shape = [4096, 16, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4854 4854 7991 7992 [4096, 16, 64] [2048, 16, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 8000000 in
/-- 4855 — rotary-embedding K output `rotary(4691, 4853, 4848, 4850).2`
    (2-tp, PM `7993`/`7994`). -/
theorem recon_intermediateGoal_4855_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4855
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hnr : pm.numRanks = 2 := rfl
  obtain ⟨hbr48, _, _⟩ := twoTp_gather _ _ intermediateGoal_4848 4848 7957 7958
    [2048, 16, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4848_ringAttn initSM initPM hSM hPM hInit hWF)
  obtain ⟨hbr50, hs7969, hs7970⟩ := twoTp_gather _ _ intermediateGoal_4850 4850 7969 7970
    [2048, 4, 64] rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4850_ringAttn initSM initPM hSM hPM hInit hWF)
  have hcache := hcache_4691_11856 initSM initPM hInit
  have hpos : denoteGraph_ringAttn sm initSM 4853 = denoteGraph_ringAttn pm initPM 4853 :=
    veq_weight_ring initSM initPM hInit initGoal_4853 (by native_decide) 4853
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsp4853 : (denoteGraph_ringAttn sm initSM 4853).shape = [4096] :=
    shape_weight_ring initSM initPM hInit initGoal_4853 (by native_decide) 4853 [4096]
      rfl rfl (by native_decide)
  have c7989 : denoteGraph_ringAttn pm initPM 7989
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4853) :=
    ringAttn_reduce1_pm_opaque pm initPM 3
      { rank := 0, op := "OpName.ChunkPrim", ins := [4853], outs := [7989], params := [0] }
      4853 7989 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4853 7989 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c7990 : denoteGraph_ringAttn pm initPM 7990
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4853) :=
    ringAttn_reduce1_pm_opaque pm initPM 16
      { rank := 1, op := "OpName.ChunkPrim", ins := [4853], outs := [7990], params := [0] }
      4853 7990 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4853 7990 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4855
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4853)
          (denoteGraph_ringAttn sm initSM 4848) (denoteGraph_ringAttn sm initSM 4850) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 125
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4853, 4848, 4850], outs := [4854, 4855], params := [16, 4] }
          4855 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4853 4848 4850 4854 4855 (by decide),
        ringAttn_prefix_read_pm sm initSM 125 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 125 4853 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 125 4848 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 125 4850 (by native_decide) (by native_decide)]
  have rP0 : denoteGraph_ringAttn pm initPM 7993
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11856) (denoteGraph_ringAttn pm initPM 7989)
          (denoteGraph_ringAttn pm initPM 7957) (denoteGraph_ringAttn pm initPM 7969) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 311
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11856, 7989, 7957, 7969], outs := [7991, 7993], params := [16, 4] }
          7993 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11856 7989 7957 7969 7991 7993 (by decide),
        ringAttn_prefix_read_pm pm initPM 311 11856 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 311 7989 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 311 7957 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 311 7969 (by native_decide) (by native_decide)]
  have rP1 : denoteGraph_ringAttn pm initPM 7994
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11856) (denoteGraph_ringAttn pm initPM 7990)
          (denoteGraph_ringAttn pm initPM 7958) (denoteGraph_ringAttn pm initPM 7970) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 312
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11856, 7990, 7958, 7970], outs := [7992, 7994], params := [16, 4] }
          7994 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11856 7990 7958 7970 7992 7994 (by decide),
        ringAttn_prefix_read_pm pm initPM 312 11856 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 312 7990 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 312 7958 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 312 7970 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4855
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7993, denoteGraph_ringAttn pm initPM 7994] := by
    rw [rSM]
    simp only [fw_rotary_embedding]
    rw [hbr50, hnr,
        fw_rotary_apply_allGather0_commute_2_1d (denoteGraph_ringAttn sm initSM 4691)
          (denoteGraph_ringAttn sm initSM 4853) (denoteGraph_ringAttn pm initPM 7969)
          (denoteGraph_ringAttn pm initPM 7970) 2048 4 64 (by omega) (by omega) (by omega)
          hsp4853 hs7969 hs7970,
        hcache, hpos,
        ← (show denoteGraph_ringAttn pm initPM 7989
              = chunkPrimDimN 0 2 0 (denoteGraph_ringAttn pm initPM 4853) from c7989),
        ← (show denoteGraph_ringAttn pm initPM 7990
              = chunkPrimDimN 0 2 1 (denoteGraph_ringAttn pm initPM 4853) from c7990),
        rP0, rP1]
    simp only [fw_rotary_embedding]
  have hsp0 : (denoteGraph_ringAttn pm initPM 7993).shape = [2048, 4, 64] := by
    rw [rP0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs7969
  have hsp1 : (denoteGraph_ringAttn pm initPM 7994).shape = [2048, 4, 64] := by
    rw [rP1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hs7970
  have hshape : (denoteGraph_ringAttn sm initSM 4855).shape = [4096, 4, 64] := by
    rw [hval, hnr, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [hsp0])]
    simp [List.set, List.getD]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4855 4855 7993 7994 [4096, 4, 64] [2048, 4, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
