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

end TrainVerify.Denote.GeneratedPatterns
