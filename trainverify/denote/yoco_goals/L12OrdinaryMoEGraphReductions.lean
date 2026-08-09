/- Layout-neutral graph reductions and initialized-weight bridge for the L12 ordinary MoE segment. -/
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

def l12OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5620],
    outs := [8508, 8512], params := [2] }
def l12OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9812],
    outs := [16102, 16106], params := [2] }
def l12OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9813],
    outs := [16110, 16114], params := [2] }
def l12OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8508, 5621], outs := [5622] }
def l12OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [16102, 5621], outs := [9818] }
def l12OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [16110, 5621], outs := [9819] }
def l12OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622],
    outs := [8519, 8523, 8527, 8531, 8535], params := [5] }
def l12OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818],
    outs := [15388, 13932, 13942, 13956, 13968], params := [5] }
def l12OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819],
    outs := [15390, 13933, 13943, 13957, 13969], params := [5] }

theorem l12OMon_red_sm8508 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8508 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5620 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 512 l12OMonSmResidualRef
    5620 8508 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5620 [8508, 8512] 2 rfl 8508 (by decide)

theorem l12OMon_red_pm16102 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16102 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9812 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1127 l12OMonPmResidualRef0
    9812 16102 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9812 [16102, 16106] 2 rfl 16102 (by decide)

theorem l12OMon_red_pm16110 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16110 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9813 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1128 l12OMonPmResidualRef1
    9813 16110 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9813 [16110, 16114] 2 rfl 16110 (by decide)

theorem l12OMon_red_sm5622 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5622 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8508)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 513 l12OMonSmRms
    8508 5621 5622 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l12OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8508 5621 5622

theorem l12OMon_red_pm9818 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9818 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16102)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1129 l12OMonPmRms0
    16102 5621 9818 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l12OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 16102 5621 9818

theorem l12OMon_red_pm9819 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9819 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 16110)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5621) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1130 l12OMonPmRms1
    16110 5621 9819 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l12OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 16110 5621 9819

theorem l12OMon_red_sm8523 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8523 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 514 l12OMonSmNormRef
    5622 8523 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8519, 8523, 8527, 8531, 8535]
    5 rfl 8523 (by decide)

theorem l12OMon_red_pm13932 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13932 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1131 l12OMonPmNormRef0
    9818 13932 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818
    [15388, 13932, 13942, 13956, 13968] 5 rfl 13932 (by decide)

theorem l12OMon_red_pm13933 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13933 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1132 l12OMonPmNormRef1
    9819 13933 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819
    [15390, 13933, 13943, 13957, 13969] 5 rfl 13933 (by decide)

theorem l12OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5621 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5621 := by
  have h := hInit initGoal_5621 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5621 pm_goal_1.numRanks _ rfl,
    show initGoal_5621.tps = [{rank := 0, tid := 5621}] from rfl,
    show initGoal_5621.ts = 5621 from rfl,
    show initGoal_5621.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5621
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5621
      (by native_decide) (by native_decide)]
  exact hval

theorem l12OMon_red_sm8512 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8512 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5620 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 512 l12OMonSmResidualRef
    5620 8512 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5620 [8508, 8512] 2 rfl 8512 (by decide)

theorem l12OMon_red_pm16106 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16106 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9812 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1127 l12OMonPmResidualRef0
    9812 16106 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9812 [16102, 16106] 2 rfl 16106 (by decide)

theorem l12OMon_red_pm16114 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16114 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9813 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1128 l12OMonPmResidualRef1
    9813 16114 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9813 [16110, 16114] 2 rfl 16114 (by decide)


/-! Router graph reductions. -/
theorem l12OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l12OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l12OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622],
    outs := [8519, 8523, 8527, 8531, 8535], params := [5] }
private def l12OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818],
    outs := [15388, 13932, 13942, 13956, 13968], params := [5] }
private def l12OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819],
    outs := [15390, 13933, 13943, 13957, 13969], params := [5] }
private def l12OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8519], outs := [5623] }
private def l12OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15388, 15390],
    outs := [12114], params := [0] }
private def l12OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12114], outs := [5623] }
private def l12OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5623, 5624], outs := [5625] }
private def l12OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5623, 5624], outs := [5625] }
private def l12OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5625], outs := [9826], params := [0] }
private def l12OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5625], outs := [9827], params := [0] }
private def l12OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5625],
    outs := [5626, 5627, 5628], params := [8, 1] }
private def l12OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9826],
    outs := [9828, 9830, 9832], params := [8, 1] }
private def l12OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9827],
    outs := [9829, 9831, 9833], params := [8, 1] }

theorem l12OMr_red_sm8519 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8519 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 514 l12OMrSmRef
    5622 8519 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622
    [8519, 8523, 8527, 8531, 8535] 5 rfl 8519 (by decide)

theorem l12OMr_red_pm15388 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15388 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1131 l12OMrPmRef0
    9818 15388 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818
    [15388, 13932, 13942, 13956, 13968] 5 rfl 15388 (by decide)

theorem l12OMr_red_pm15390 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15390 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1132 l12OMrPmRef1
    9819 15390 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819
    [15390, 13933, 13943, 13957, 13969] 5 rfl 15390 (by decide)

theorem l12OMr_red_sm5623 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5623 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8519 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 515 l12OMrSmFloat
    8519 5623 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8519 5623 []

theorem l12OMr_red_pm12114 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12114 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15388,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15390] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1136 l12OMrPmGather
    15388 15390 12114 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15388, 15390] 12114 0]
  rfl

theorem l12OMr_red_pm5623 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5623 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12114 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1144 l12OMrPmFloat1
    12114 5623 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12114 5623 []

theorem l12OMr_red_sm5625 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5625 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5623)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5624) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 519 l12OMrSmNormLinear
    5623 5624 5625 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5623 5624 5625 []

theorem l12OMr_red_pm5625 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5625 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5623)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5624) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1152 l12OMrPmNormLinear1
    5623 5624 5625 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5623 5624 5625 []

theorem l12OMr_red_pm9826 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9826 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5625) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1158 l12OMrPmChunk0
    5625 9826 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5625 9826 0

theorem l12OMr_red_pm9827 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9827 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5625) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1159 l12OMrPmChunk1
    5625 9827 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5625 9827 0

private def l12OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l12OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l12OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l12OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l12OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l12OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l12OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l12OMr_red_sm5626 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5625).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5626 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5625) 8 64).1 :=
  l12OMr_red_topk_probs sm_goal_1 initSM 523 l12OMrSmTopk 0 5625 5626 5627 5628
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l12OMr_red_pm9828 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9826).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9828 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9826) 8 64).1 :=
  l12OMr_red_topk_probs pm_goal_1 initPM 1163 l12OMrPmTopk0 0 9826 9828 9830 9832
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l12OMr_red_pm9829 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9827).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9829 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9827) 8 64).1 :=
  l12OMr_red_topk_probs pm_goal_1 initPM 1164 l12OMrPmTopk1 1 9827 9829 9831 9833
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l12OMr_red_sm5627 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5625).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5627 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5625) 8 64).2.1 :=
  l12OMr_red_topk_map sm_goal_1 initSM 523 l12OMrSmTopk 0 5625 5626 5627 5628
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l12OMr_red_pm9830 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9826).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9830 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9826) 8 64).2.1 :=
  l12OMr_red_topk_map pm_goal_1 initPM 1163 l12OMrPmTopk0 0 9826 9828 9830 9832
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l12OMr_red_pm9831 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9827).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9831 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9827) 8 64).2.1 :=
  l12OMr_red_topk_map pm_goal_1 initPM 1164 l12OMrPmTopk1 1 9827 9829 9831 9833
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l12OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5624 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5624 ∉ n.outs) := by
  native_decide

theorem l12OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5624 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5624 := by
  have hi := (hInit initGoal_5624 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5624 pm_goal_1.numRanks _ rfl,
    show initGoal_5624.tps = [{rank := 0, tid := 5624}] from rfl,
    show initGoal_5624.ts = 5624 from rfl,
    show initGoal_5624.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5624 (by native_decide) l12OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5624 (by native_decide) l12OMr_weight_not_written.2]
  exact hi

theorem l12OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5624).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5624 (by native_decide) l12OMr_weight_not_written.2]
  exact hPM 5624 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l12OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622],
    outs := [8519, 8523, 8527, 8531, 8535], params := [5] }
private def l12OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818],
    outs := [15388, 13932, 13942, 13956, 13968], params := [5] }
private def l12OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819],
    outs := [15390, 13933, 13943, 13957, 13969], params := [5] }
private def l12OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8527], outs := [5632],
    params := [4096, 1024] }
private def l12OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13942], outs := [9840],
    params := [2048, 1024] }
private def l12OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13943], outs := [9841],
    params := [2048, 1024] }
private def l12OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5632, 5633],
    outs := [5634] }
private def l12OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9840, 5633],
    outs := [9844] }
private def l12OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9841, 5633],
    outs := [9845] }
private def l12OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5634], outs := [5635],
    params := [4096, 1] }
private def l12OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9844], outs := [9846],
    params := [2048, 1] }
private def l12OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9845], outs := [9847],
    params := [2048, 1] }
private def l12OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5635], outs := [5636] }
private def l12OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9846], outs := [9848] }
private def l12OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9847], outs := [9849] }

theorem l12OMrg_red_sm8527 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8527 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 514 l12OMrgSmRef
    5622 8527 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622 [8519, 8523, 8527, 8531, 8535]
    5 rfl 8527 (by decide)

theorem l12OMrg_red_pm13942 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13942 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1131 l12OMrgPmRef0
    9818 13942 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818
    [15388, 13932, 13942, 13956, 13968] 5 rfl 13942 (by decide)

theorem l12OMrg_red_pm13943 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13943 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1132 l12OMrgPmRef1
    9819 13943 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819
    [15390, 13933, 13943, 13957, 13969] 5 rfl 13943 (by decide)

theorem l12OMrg_red_sm5632 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5632 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8527) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 516 l12OMrgSmReshape
    8527 5632 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8527 5632 [4096, 1024]

theorem l12OMrg_red_pm9840 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9840 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13942) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1133 l12OMrgPmReshape0
    13942 9840 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13942 9840 [2048, 1024]

theorem l12OMrg_red_pm9841 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9841 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13943) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1137 l12OMrgPmReshape1
    13943 9841 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13943 9841 [2048, 1024]

theorem l12OMrg_red_sm5634 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5634 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5632)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 520 l12OMrgSmLinear
    5632 5633 5634 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5632 5633 5634

theorem l12OMrg_red_pm9844 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9844 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9840)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1140 l12OMrgPmLinear0
    9840 5633 9844 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9840 5633 9844

theorem l12OMrg_red_pm9845 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9845 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9841)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5633) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1145 l12OMrgPmLinear1
    9841 5633 9845 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9841 5633 9845

theorem l12OMrg_red_sm5635 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5635 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5634) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 524 l12OMrgSmView
    5634 5635 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5634 5635

theorem l12OMrg_red_pm9846 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9846 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9844) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1148 l12OMrgPmView0
    9844 9846 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9844 9846

theorem l12OMrg_red_pm9847 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9847 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9845) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1153 l12OMrgPmView1
    9845 9847 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9845 9847

theorem l12OMrg_red_sm5636 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5636 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5635) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 528 l12OMrgSmSigmoid
    5635 5636 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5635 5636

theorem l12OMrg_red_pm9848 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9848 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9846) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1156 l12OMrgPmSigmoid0
    9846 9848 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9846 9848

theorem l12OMrg_red_pm9849 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9849 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9847) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1160 l12OMrgPmSigmoid1
    9847 9849 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9847 9849

theorem l12OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5633 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5633 ∉ n.outs) := by
  native_decide

theorem l12OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5633 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5633 := by
  have hi := (hInit initGoal_5633 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5633 pm_goal_1.numRanks _ rfl,
    show initGoal_5633.tps = [{rank := 0, tid := 5633}] from rfl,
    show initGoal_5633.ts = 5633 from rfl,
    show initGoal_5633.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5633
      (by native_decide) l12OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5633
      (by native_decide) l12OMrg_weight_not_written.2]
  exact hi

theorem l12OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5633).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5633 = initPM 5633 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5633
      (by native_decide) l12OMrg_weight_not_written.2
  rw [e]
  exact hPM 5633 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
