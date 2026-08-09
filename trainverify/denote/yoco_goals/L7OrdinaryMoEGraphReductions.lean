/- Layout-neutral graph reductions and initialized-weight bridge for the L7 ordinary MoE segment. -/
import denote.yoco_goals.Goal_1
import denote.MultirefGeneral
import denote.ChunkGatherDim0
import denote.DenoteMoE

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

def l7OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5342],
    outs := [8129, 8133], params := [2] }
def l7OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8976],
    outs := [15678, 15682], params := [2] }
def l7OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8977],
    outs := [15686, 15690], params := [2] }
def l7OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8129, 5343], outs := [5344] }
def l7OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15678, 5343], outs := [8980] }
def l7OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15686, 5343], outs := [8981] }
def l7OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5344],
    outs := [8140, 8144, 8148, 8152, 8156], params := [5] }
def l7OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8980],
    outs := [15352, 13292, 13302, 13316, 13328], params := [5] }
def l7OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8981],
    outs := [15354, 13293, 13303, 13317, 13329], params := [5] }

theorem l7OMon_red_sm8129 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8129 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5342 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 289 l7OMonSmResidualRef
    5342 8129 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5342 [8129, 8133] 2 rfl 8129 (by decide)

theorem l7OMon_red_pm15678 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15678 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8976 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 651 l7OMonPmResidualRef0
    8976 15678 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8976 [15678, 15682] 2 rfl 15678 (by decide)

theorem l7OMon_red_pm15686 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15686 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8977 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 652 l7OMonPmResidualRef1
    8977 15686 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8977 [15686, 15690] 2 rfl 15686 (by decide)

theorem l7OMon_red_sm5344 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5344 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8129)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5343) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 290 l7OMonSmRms
    8129 5343 5344 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l7OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8129 5343 5344

theorem l7OMon_red_pm8980 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8980 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15678)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5343) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 653 l7OMonPmRms0
    15678 5343 8980 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l7OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15678 5343 8980

theorem l7OMon_red_pm8981 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8981 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15686)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5343) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 654 l7OMonPmRms1
    15686 5343 8981 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l7OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15686 5343 8981

theorem l7OMon_red_sm8144 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8144 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5344 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 291 l7OMonSmNormRef
    5344 8144 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5344 [8140, 8144, 8148, 8152, 8156]
    5 rfl 8144 (by decide)

theorem l7OMon_red_pm13292 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13292 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8980 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 655 l7OMonPmNormRef0
    8980 13292 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8980
    [15352, 13292, 13302, 13316, 13328] 5 rfl 13292 (by decide)

theorem l7OMon_red_pm13293 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13293 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8981 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 656 l7OMonPmNormRef1
    8981 13293 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8981
    [15354, 13293, 13303, 13317, 13329] 5 rfl 13293 (by decide)

theorem l7OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5343 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5343 := by
  have h := hInit initGoal_5343 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5343 pm_goal_1.numRanks _ rfl,
    show initGoal_5343.tps = [{rank := 0, tid := 5343}] from rfl,
    show initGoal_5343.ts = 5343 from rfl,
    show initGoal_5343.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5343
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5343
      (by native_decide) (by native_decide)]
  exact hval

theorem l7OMon_red_sm8133 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8133 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5342 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 289 l7OMonSmResidualRef
    5342 8133 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5342 [8129, 8133] 2 rfl 8133 (by decide)

theorem l7OMon_red_pm15682 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15682 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8976 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 651 l7OMonPmResidualRef0
    8976 15682 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8976 [15678, 15682] 2 rfl 15682 (by decide)

theorem l7OMon_red_pm15690 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15690 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8977 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 652 l7OMonPmResidualRef1
    8977 15690 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8977 [15686, 15690] 2 rfl 15690 (by decide)


/-! Router graph reductions. -/
theorem l7OMr_chunk_gather0 (x0 x1 : Tensor)
    (hx0 : x0.shape = [2048, 64]) (hx1 : x1.shape = [2048, 64]) :
    chunkPrimDimN 0 2 0 (allGatherPrimDimN 0 2 0 [x0, x1]) = x0 := by
  have hhead : (([x0, x1] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [2048, 64] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hx0]
  have hget : ∀ r (_ : r < 2),
      ([x0, x1].getD r (zeroTensor [2048, 64])).shape = [2048, 64] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hx0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hx1
  have hg : (allGatherPrimDimN 0 2 0 [x0, x1]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead]
    rfl
  have hc : (chunkPrimDimN 0 2 0 (allGatherPrimDimN 0 2 0 [x0, x1])).shape =
      [2048, 64] := by
    rw [chunkPrimDimN_shape 0 2 0 _ _ hg (by decide)]
    rfl
  apply Tensor.ext (by rw [hc, hx0])
  intro idx hidx
  rw [hc] at hidx
  simp only [prodShape, List.foldl_cons, List.foldl_nil, Nat.one_mul] at hidx
  let i := idx / 64
  let j := idx % 64
  have hj : j < 64 := Nat.mod_lt _ (by decide)
  have hi : i < 2048 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hidx
  have hij : idx = i * 64 + j := (Nat.div_add_mod' idx 64).symm
  rw [hij]
  rw [chunkPrimDimN0_valAt 2 0 4096 64 _ hg (by decide) (by decide)
    (by decide) i hi j hj]
  rw [allGatherPrimDimN0_valAt 2 2048 64 [x0, x1] (by decide) (by decide)
    (by decide) hhead hget 0 (by decide) i hi j hj]
  simp only [List.getD_cons_zero]

theorem l7OMr_chunk_gather1 (x0 x1 : Tensor)
    (hx0 : x0.shape = [2048, 64]) (hx1 : x1.shape = [2048, 64]) :
    chunkPrimDimN 0 2 1 (allGatherPrimDimN 0 2 0 [x0, x1]) = x1 := by
  have hhead : (([x0, x1] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [2048, 64] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hx0]
  have hget : ∀ r (_ : r < 2),
      ([x0, x1].getD r (zeroTensor [2048, 64])).shape = [2048, 64] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hx0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hx1
  have hg : (allGatherPrimDimN 0 2 0 [x0, x1]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead]
    rfl
  have hc : (chunkPrimDimN 0 2 1 (allGatherPrimDimN 0 2 0 [x0, x1])).shape =
      [2048, 64] := by
    rw [chunkPrimDimN_shape 0 2 1 _ _ hg (by decide)]
    rfl
  apply Tensor.ext (by rw [hc, hx1])
  intro idx hidx
  rw [hc] at hidx
  simp only [prodShape, List.foldl_cons, List.foldl_nil, Nat.one_mul] at hidx
  let i := idx / 64
  let j := idx % 64
  have hj : j < 64 := Nat.mod_lt _ (by decide)
  have hi : i < 2048 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hidx
  have hij : idx = i * 64 + j := (Nat.div_add_mod' idx 64).symm
  rw [hij]
  rw [chunkPrimDimN0_valAt 2 1 4096 64 _ hg (by decide) (by decide)
    (by decide) i hi j hj]
  rw [allGatherPrimDimN0_valAt 2 2048 64 [x0, x1] (by decide) (by decide)
    (by decide) hhead hget 1 (by decide) i hi j hj]
  simp only [List.getD_cons_succ, List.getD_cons_zero]

private def l7OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5344],
    outs := [8140, 8144, 8148, 8152, 8156], params := [5] }
private def l7OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8980],
    outs := [15352, 13292, 13302, 13316, 13328], params := [5] }
private def l7OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8981],
    outs := [15354, 13293, 13303, 13317, 13329], params := [5] }
private def l7OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8140], outs := [5345] }
private def l7OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15352, 15354],
    outs := [11966], params := [0] }
private def l7OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11966], outs := [5345] }
private def l7OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5345, 5346], outs := [5347] }
private def l7OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5345, 5346], outs := [5347] }
private def l7OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5347], outs := [8988], params := [0] }
private def l7OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5347], outs := [8989], params := [0] }
private def l7OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5347],
    outs := [5348, 5349, 5350], params := [8, 1] }
private def l7OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8988],
    outs := [8990, 8992, 8994], params := [8, 1] }
private def l7OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8989],
    outs := [8991, 8993, 8995], params := [8, 1] }

theorem l7OMr_red_sm8140 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8140 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5344 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 291 l7OMrSmRef
    5344 8140 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5344
    [8140, 8144, 8148, 8152, 8156] 5 rfl 8140 (by decide)

theorem l7OMr_red_pm15352 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15352 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8980 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 655 l7OMrPmRef0
    8980 15352 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8980
    [15352, 13292, 13302, 13316, 13328] 5 rfl 15352 (by decide)

theorem l7OMr_red_pm15354 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15354 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8981 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 656 l7OMrPmRef1
    8981 15354 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8981
    [15354, 13293, 13303, 13317, 13329] 5 rfl 15354 (by decide)

theorem l7OMr_red_sm5345 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5345 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8140 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 292 l7OMrSmFloat
    8140 5345 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8140 5345 []

theorem l7OMr_red_pm11966 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11966 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15352,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15354] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 660 l7OMrPmGather
    15352 15354 11966 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15352, 15354] 11966 0]
  rfl

theorem l7OMr_red_pm5345 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5345 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11966 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 668 l7OMrPmFloat1
    11966 5345 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11966 5345 []

theorem l7OMr_red_sm5347 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5347 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5345)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5346) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 296 l7OMrSmNormLinear
    5345 5346 5347 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5345 5346 5347 []

theorem l7OMr_red_pm5347 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5347 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5345)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5346) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 676 l7OMrPmNormLinear1
    5345 5346 5347 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5345 5346 5347 []

theorem l7OMr_red_pm8988 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8988 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5347) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 682 l7OMrPmChunk0
    5347 8988 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5347 8988 0

theorem l7OMr_red_pm8989 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8989 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5347) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 683 l7OMrPmChunk1
    5347 8989 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5347 8989 0

private def l7OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l7OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l7OMrTopkNode rnk logits probs mapTid scores)
    (hsh : (denoteGraphDistributedFaithful g init logits).shape = [2048, 64] ∨
      (denoteGraphDistributedFaithful g init logits).shape = [4096, 64])
    (ha : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (haw : ∀ n ∈ g.nodes.drop (k + 1), probs ∉ n.outs)
    (hp : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, logits ∉ n.outs) :
    denoteGraphDistributedFaithful g init probs =
      (fw_topk_routing (denoteGraphDistributedFaithful g init logits) 8 64).1 := by
  have hr := denoteGraphDistributedFaithful_reduce1 g init k node logits probs
    (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    hk hn (by
      intro s
      rw [hnode]
      unfold l7OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l7OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l7OMrTopkNode rnk logits probs mapTid scores)
    (hne : probs ≠ mapTid)
    (hsh : (denoteGraphDistributedFaithful g init logits).shape = [2048, 64] ∨
      (denoteGraphDistributedFaithful g init logits).shape = [4096, 64])
    (ha : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (haw : ∀ n ∈ g.nodes.drop (k + 1), mapTid ∉ n.outs)
    (hp : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, logits ∉ n.outs) :
    denoteGraphDistributedFaithful g init mapTid =
      (fw_topk_routing (denoteGraphDistributedFaithful g init logits) 8 64).2.1 := by
  have hr := denoteGraphDistributedFaithful_reduce1 g init k node logits mapTid
    (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    hk hn (by
      intro s
      rw [hnode]
      unfold l7OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l7OMr_red_sm5348 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5347).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5348 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5347) 8 64).1 :=
  l7OMr_red_topk_probs sm_goal_1 initSM 300 l7OMrSmTopk 0 5347 5348 5349 5350
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l7OMr_red_pm8990 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8988).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8990 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8988) 8 64).1 :=
  l7OMr_red_topk_probs pm_goal_1 initPM 687 l7OMrPmTopk0 0 8988 8990 8992 8994
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l7OMr_red_pm8991 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8989).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8991 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8989) 8 64).1 :=
  l7OMr_red_topk_probs pm_goal_1 initPM 688 l7OMrPmTopk1 1 8989 8991 8993 8995
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l7OMr_red_sm5349 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5347).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5349 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5347) 8 64).2.1 :=
  l7OMr_red_topk_map sm_goal_1 initSM 300 l7OMrSmTopk 0 5347 5348 5349 5350
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l7OMr_red_pm8992 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8988).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8992 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8988) 8 64).2.1 :=
  l7OMr_red_topk_map pm_goal_1 initPM 687 l7OMrPmTopk0 0 8988 8990 8992 8994
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l7OMr_red_pm8993 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8989).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8993 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8989) 8 64).2.1 :=
  l7OMr_red_topk_map pm_goal_1 initPM 688 l7OMrPmTopk1 1 8989 8991 8993 8995
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l7OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5346 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5346 ∉ n.outs) := by
  native_decide

theorem l7OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5346 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5346 := by
  have hi := (hInit initGoal_5346 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5346 pm_goal_1.numRanks _ rfl,
    show initGoal_5346.tps = [{rank := 0, tid := 5346}] from rfl,
    show initGoal_5346.ts = 5346 from rfl,
    show initGoal_5346.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5346 (by native_decide) l7OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5346 (by native_decide) l7OMr_weight_not_written.2]
  exact hi

theorem l7OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5346).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5346 (by native_decide) l7OMr_weight_not_written.2]
  exact hPM 5346 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l7OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5344],
    outs := [8140, 8144, 8148, 8152, 8156], params := [5] }
private def l7OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8980],
    outs := [15352, 13292, 13302, 13316, 13328], params := [5] }
private def l7OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8981],
    outs := [15354, 13293, 13303, 13317, 13329], params := [5] }
private def l7OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8148], outs := [5354],
    params := [4096, 1024] }
private def l7OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13302], outs := [9002],
    params := [2048, 1024] }
private def l7OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13303], outs := [9003],
    params := [2048, 1024] }
private def l7OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5354, 5355],
    outs := [5356] }
private def l7OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9002, 5355],
    outs := [9006] }
private def l7OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9003, 5355],
    outs := [9007] }
private def l7OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5356], outs := [5357],
    params := [4096, 1] }
private def l7OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9006], outs := [9008],
    params := [2048, 1] }
private def l7OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9007], outs := [9009],
    params := [2048, 1] }
private def l7OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5357], outs := [5358] }
private def l7OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9008], outs := [9010] }
private def l7OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9009], outs := [9011] }

theorem l7OMrg_red_sm8148 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8148 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5344 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 291 l7OMrgSmRef
    5344 8148 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5344 [8140, 8144, 8148, 8152, 8156]
    5 rfl 8148 (by decide)

theorem l7OMrg_red_pm13302 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13302 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8980 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 655 l7OMrgPmRef0
    8980 13302 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8980
    [15352, 13292, 13302, 13316, 13328] 5 rfl 13302 (by decide)

theorem l7OMrg_red_pm13303 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13303 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8981 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 656 l7OMrgPmRef1
    8981 13303 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8981
    [15354, 13293, 13303, 13317, 13329] 5 rfl 13303 (by decide)

theorem l7OMrg_red_sm5354 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5354 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8148) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 293 l7OMrgSmReshape
    8148 5354 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8148 5354 [4096, 1024]

theorem l7OMrg_red_pm9002 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9002 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13302) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 657 l7OMrgPmReshape0
    13302 9002 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13302 9002 [2048, 1024]

theorem l7OMrg_red_pm9003 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9003 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13303) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 661 l7OMrgPmReshape1
    13303 9003 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13303 9003 [2048, 1024]

theorem l7OMrg_red_sm5356 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5356 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5354)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5355) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 297 l7OMrgSmLinear
    5354 5355 5356 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5354 5355 5356

theorem l7OMrg_red_pm9006 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9006 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9002)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5355) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 664 l7OMrgPmLinear0
    9002 5355 9006 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9002 5355 9006

theorem l7OMrg_red_pm9007 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9007 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9003)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5355) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 669 l7OMrgPmLinear1
    9003 5355 9007 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9003 5355 9007

theorem l7OMrg_red_sm5357 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5357 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5356) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 301 l7OMrgSmView
    5356 5357 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5356 5357

theorem l7OMrg_red_pm9008 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9008 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9006) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 672 l7OMrgPmView0
    9006 9008 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9006 9008

theorem l7OMrg_red_pm9009 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9009 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9007) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 677 l7OMrgPmView1
    9007 9009 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9007 9009

theorem l7OMrg_red_sm5358 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5358 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5357) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 305 l7OMrgSmSigmoid
    5357 5358 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5357 5358

theorem l7OMrg_red_pm9010 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9010 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9008) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 680 l7OMrgPmSigmoid0
    9008 9010 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9008 9010

theorem l7OMrg_red_pm9011 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9011 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9009) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 684 l7OMrgPmSigmoid1
    9009 9011 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l7OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9009 9011

theorem l7OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5355 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5355 ∉ n.outs) := by
  native_decide

theorem l7OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5355 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5355 := by
  have hi := (hInit initGoal_5355 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5355 pm_goal_1.numRanks _ rfl,
    show initGoal_5355.tps = [{rank := 0, tid := 5355}] from rfl,
    show initGoal_5355.ts = 5355 from rfl,
    show initGoal_5355.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5355
      (by native_decide) l7OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5355
      (by native_decide) l7OMrg_weight_not_written.2]
  exact hi

theorem l7OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5355).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5355 = initPM 5355 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5355
      (by native_decide) l7OMrg_weight_not_written.2
  rw [e]
  exact hPM 5355 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
