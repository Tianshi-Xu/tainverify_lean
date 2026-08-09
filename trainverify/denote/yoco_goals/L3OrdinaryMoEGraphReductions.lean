/- Layout-neutral graph reductions and initialized-weight bridge for the L3 ordinary MoE segment. -/
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

def l3OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5122],
    outs := [7921, 7925], params := [2] }
def l3OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8320],
    outs := [15550, 15554], params := [2] }
def l3OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8321],
    outs := [15558, 15562], params := [2] }
def l3OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [7921, 5123], outs := [5124] }
def l3OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15550, 5123], outs := [8324] }
def l3OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15558, 5123], outs := [8325] }
def l3OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5124],
    outs := [7932, 7936, 7940, 7944, 7948], params := [5] }
def l3OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8324],
    outs := [15320, 12788, 12798, 12812, 12824], params := [5] }
def l3OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8325],
    outs := [15322, 12789, 12799, 12813, 12825], params := [5] }

theorem l3OMon_red_sm7921 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7921 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5122 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 133 l3OMonSmResidualRef
    5122 7921 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5122 [7921, 7925] 2 rfl 7921 (by decide)

theorem l3OMon_red_pm15550 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15550 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8320 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 315 l3OMonPmResidualRef0
    8320 15550 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8320 [15550, 15554] 2 rfl 15550 (by decide)

theorem l3OMon_red_pm15558 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15558 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8321 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 316 l3OMonPmResidualRef1
    8321 15558 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8321 [15558, 15562] 2 rfl 15558 (by decide)

theorem l3OMon_red_sm5124 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5124 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7921)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5123) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 134 l3OMonSmRms
    7921 5123 5124 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l3OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 7921 5123 5124

theorem l3OMon_red_pm8324 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8324 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15550)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5123) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 317 l3OMonPmRms0
    15550 5123 8324 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l3OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15550 5123 8324

theorem l3OMon_red_pm8325 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8325 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15558)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5123) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 318 l3OMonPmRms1
    15558 5123 8325 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l3OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15558 5123 8325

theorem l3OMon_red_sm7936 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7936 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5124 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 135 l3OMonSmNormRef
    5124 7936 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5124 [7932, 7936, 7940, 7944, 7948]
    5 rfl 7936 (by decide)

theorem l3OMon_red_pm12788 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12788 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8324 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 319 l3OMonPmNormRef0
    8324 12788 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8324
    [15320, 12788, 12798, 12812, 12824] 5 rfl 12788 (by decide)

theorem l3OMon_red_pm12789 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12789 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8325 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 320 l3OMonPmNormRef1
    8325 12789 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8325
    [15322, 12789, 12799, 12813, 12825] 5 rfl 12789 (by decide)

theorem l3OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5123 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5123 := by
  have h := hInit initGoal_5123 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5123 pm_goal_1.numRanks _ rfl,
    show initGoal_5123.tps = [{rank := 0, tid := 5123}] from rfl,
    show initGoal_5123.ts = 5123 from rfl,
    show initGoal_5123.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5123
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5123
      (by native_decide) (by native_decide)]
  exact hval

theorem l3OMon_red_sm7925 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7925 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5122 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 133 l3OMonSmResidualRef
    5122 7925 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5122 [7921, 7925] 2 rfl 7925 (by decide)

theorem l3OMon_red_pm15554 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15554 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8320 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 315 l3OMonPmResidualRef0
    8320 15554 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8320 [15550, 15554] 2 rfl 15554 (by decide)

theorem l3OMon_red_pm15562 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15562 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8321 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 316 l3OMonPmResidualRef1
    8321 15562 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8321 [15558, 15562] 2 rfl 15562 (by decide)


/-! Router graph reductions. -/
theorem l3OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l3OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l3OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5124],
    outs := [7932, 7936, 7940, 7944, 7948], params := [5] }
private def l3OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8324],
    outs := [15320, 12788, 12798, 12812, 12824], params := [5] }
private def l3OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8325],
    outs := [15322, 12789, 12799, 12813, 12825], params := [5] }
private def l3OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [7932], outs := [5125] }
private def l3OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15320, 15322],
    outs := [11838], params := [0] }
private def l3OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11838], outs := [5125] }
private def l3OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5125, 5126], outs := [5127] }
private def l3OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5125, 5126], outs := [5127] }
private def l3OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5127], outs := [8332], params := [0] }
private def l3OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5127], outs := [8333], params := [0] }
private def l3OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5127],
    outs := [5128, 5129, 5130], params := [8, 1] }
private def l3OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8332],
    outs := [8334, 8336, 8338], params := [8, 1] }
private def l3OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8333],
    outs := [8335, 8337, 8339], params := [8, 1] }

theorem l3OMr_red_sm7932 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7932 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5124 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 135 l3OMrSmRef
    5124 7932 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5124
    [7932, 7936, 7940, 7944, 7948] 5 rfl 7932 (by decide)

theorem l3OMr_red_pm15320 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15320 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8324 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 319 l3OMrPmRef0
    8324 15320 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8324
    [15320, 12788, 12798, 12812, 12824] 5 rfl 15320 (by decide)

theorem l3OMr_red_pm15322 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15322 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8325 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 320 l3OMrPmRef1
    8325 15322 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8325
    [15322, 12789, 12799, 12813, 12825] 5 rfl 15322 (by decide)

theorem l3OMr_red_sm5125 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5125 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 7932 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 136 l3OMrSmFloat
    7932 5125 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 7932 5125 []

theorem l3OMr_red_pm11838 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11838 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15320,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15322] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 324 l3OMrPmGather
    15320 15322 11838 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15320, 15322] 11838 0]
  rfl

theorem l3OMr_red_pm5125 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5125 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11838 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 332 l3OMrPmFloat1
    11838 5125 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11838 5125 []

theorem l3OMr_red_sm5127 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5127 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5125)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5126) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 140 l3OMrSmNormLinear
    5125 5126 5127 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5125 5126 5127 []

theorem l3OMr_red_pm5127 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5127 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5125)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5126) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 340 l3OMrPmNormLinear1
    5125 5126 5127 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5125 5126 5127 []

theorem l3OMr_red_pm8332 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8332 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5127) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 346 l3OMrPmChunk0
    5127 8332 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5127 8332 0

theorem l3OMr_red_pm8333 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8333 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5127) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 347 l3OMrPmChunk1
    5127 8333 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5127 8333 0

private def l3OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l3OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l3OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l3OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l3OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l3OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l3OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l3OMr_red_sm5128 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5127).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5128 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5127) 8 64).1 :=
  l3OMr_red_topk_probs sm_goal_1 initSM 144 l3OMrSmTopk 0 5127 5128 5129 5130
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l3OMr_red_pm8334 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8332).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8334 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8332) 8 64).1 :=
  l3OMr_red_topk_probs pm_goal_1 initPM 351 l3OMrPmTopk0 0 8332 8334 8336 8338
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l3OMr_red_pm8335 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8333).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8335 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8333) 8 64).1 :=
  l3OMr_red_topk_probs pm_goal_1 initPM 352 l3OMrPmTopk1 1 8333 8335 8337 8339
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l3OMr_red_sm5129 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5127).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5129 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5127) 8 64).2.1 :=
  l3OMr_red_topk_map sm_goal_1 initSM 144 l3OMrSmTopk 0 5127 5128 5129 5130
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l3OMr_red_pm8336 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8332).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8336 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8332) 8 64).2.1 :=
  l3OMr_red_topk_map pm_goal_1 initPM 351 l3OMrPmTopk0 0 8332 8334 8336 8338
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l3OMr_red_pm8337 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8333).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8337 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8333) 8 64).2.1 :=
  l3OMr_red_topk_map pm_goal_1 initPM 352 l3OMrPmTopk1 1 8333 8335 8337 8339
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l3OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5126 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5126 ∉ n.outs) := by
  native_decide

theorem l3OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5126 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5126 := by
  have hi := (hInit initGoal_5126 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5126 pm_goal_1.numRanks _ rfl,
    show initGoal_5126.tps = [{rank := 0, tid := 5126}] from rfl,
    show initGoal_5126.ts = 5126 from rfl,
    show initGoal_5126.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5126 (by native_decide) l3OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5126 (by native_decide) l3OMr_weight_not_written.2]
  exact hi

theorem l3OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5126).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5126 (by native_decide) l3OMr_weight_not_written.2]
  exact hPM 5126 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l3OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5124],
    outs := [7932, 7936, 7940, 7944, 7948], params := [5] }
private def l3OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8324],
    outs := [15320, 12788, 12798, 12812, 12824], params := [5] }
private def l3OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8325],
    outs := [15322, 12789, 12799, 12813, 12825], params := [5] }
private def l3OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7940], outs := [5134],
    params := [4096, 1024] }
private def l3OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12798], outs := [8346],
    params := [2048, 1024] }
private def l3OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12799], outs := [8347],
    params := [2048, 1024] }
private def l3OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5134, 5135],
    outs := [5136] }
private def l3OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8346, 5135],
    outs := [8350] }
private def l3OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8347, 5135],
    outs := [8351] }
private def l3OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5136], outs := [5137],
    params := [4096, 1] }
private def l3OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8350], outs := [8352],
    params := [2048, 1] }
private def l3OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8351], outs := [8353],
    params := [2048, 1] }
private def l3OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5137], outs := [5138] }
private def l3OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [8352], outs := [8354] }
private def l3OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [8353], outs := [8355] }

theorem l3OMrg_red_sm7940 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7940 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5124 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 135 l3OMrgSmRef
    5124 7940 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5124 [7932, 7936, 7940, 7944, 7948]
    5 rfl 7940 (by decide)

theorem l3OMrg_red_pm12798 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12798 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8324 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 319 l3OMrgPmRef0
    8324 12798 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8324
    [15320, 12788, 12798, 12812, 12824] 5 rfl 12798 (by decide)

theorem l3OMrg_red_pm12799 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12799 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8325 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 320 l3OMrgPmRef1
    8325 12799 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8325
    [15322, 12789, 12799, 12813, 12825] 5 rfl 12799 (by decide)

theorem l3OMrg_red_sm5134 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5134 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 7940) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 137 l3OMrgSmReshape
    7940 5134 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7940 5134 [4096, 1024]

theorem l3OMrg_red_pm8346 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8346 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12798) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 321 l3OMrgPmReshape0
    12798 8346 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12798 8346 [2048, 1024]

theorem l3OMrg_red_pm8347 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8347 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12799) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 325 l3OMrgPmReshape1
    12799 8347 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12799 8347 [2048, 1024]

theorem l3OMrg_red_sm5136 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5136 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5134)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5135) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 141 l3OMrgSmLinear
    5134 5135 5136 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5134 5135 5136

theorem l3OMrg_red_pm8350 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8350 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8346)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5135) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 328 l3OMrgPmLinear0
    8346 5135 8350 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8346 5135 8350

theorem l3OMrg_red_pm8351 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8351 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8347)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5135) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 333 l3OMrgPmLinear1
    8347 5135 8351 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8347 5135 8351

theorem l3OMrg_red_sm5137 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5137 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5136) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 145 l3OMrgSmView
    5136 5137 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5136 5137

theorem l3OMrg_red_pm8352 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8352 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8350) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 336 l3OMrgPmView0
    8350 8352 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 8350 8352

theorem l3OMrg_red_pm8353 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8353 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8351) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 341 l3OMrgPmView1
    8351 8353 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 8351 8353

theorem l3OMrg_red_sm5138 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5138 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5137) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 149 l3OMrgSmSigmoid
    5137 5138 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5137 5138

theorem l3OMrg_red_pm8354 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8354 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8352) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 344 l3OMrgPmSigmoid0
    8352 8354 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 8352 8354

theorem l3OMrg_red_pm8355 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8355 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8353) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 348 l3OMrgPmSigmoid1
    8353 8355 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l3OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 8353 8355

theorem l3OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5135 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5135 ∉ n.outs) := by
  native_decide

theorem l3OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5135 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5135 := by
  have hi := (hInit initGoal_5135 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5135 pm_goal_1.numRanks _ rfl,
    show initGoal_5135.tps = [{rank := 0, tid := 5135}] from rfl,
    show initGoal_5135.ts = 5135 from rfl,
    show initGoal_5135.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5135
      (by native_decide) l3OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5135
      (by native_decide) l3OMrg_weight_not_written.2]
  exact hi

theorem l3OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5135).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5135 = initPM 5135 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5135
      (by native_decide) l3OMrg_weight_not_written.2
  rw [e]
  exact hPM 5135 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
