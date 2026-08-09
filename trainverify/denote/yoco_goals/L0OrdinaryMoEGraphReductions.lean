/- Layout-neutral graph reductions and initialized-weight bridge for the L0 ordinary MoE segment. -/
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

def l0OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4957],
    outs := [7765, 7769], params := [2] }
def l0OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7828],
    outs := [15454, 15458], params := [2] }
def l0OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7829],
    outs := [15462, 15466], params := [2] }
def l0OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [7765, 4958], outs := [4959] }
def l0OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15454, 4958], outs := [7832] }
def l0OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15462, 4958], outs := [7833] }
def l0OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4959],
    outs := [7776, 7780, 7784, 7788, 7792], params := [5] }
def l0OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7832],
    outs := [15296, 12410, 12420, 12434, 12446], params := [5] }
def l0OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7833],
    outs := [15298, 12411, 12421, 12435, 12447], params := [5] }

theorem l0OMon_red_sm7765 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7765 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 4957 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 16 l0OMonSmResidualRef
    4957 7765 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 4957 [7765, 7769] 2 rfl 7765 (by decide)

theorem l0OMon_red_pm15454 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15454 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7828 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 63 l0OMonPmResidualRef0
    7828 15454 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7828 [15454, 15458] 2 rfl 15454 (by decide)

theorem l0OMon_red_pm15462 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15462 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7829 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 64 l0OMonPmResidualRef1
    7829 15462 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7829 [15462, 15466] 2 rfl 15462 (by decide)

theorem l0OMon_red_sm4959 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4959 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7765)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4958) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 17 l0OMonSmRms
    7765 4958 4959 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l0OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 7765 4958 4959

theorem l0OMon_red_pm7832 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7832 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15454)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 4958) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 65 l0OMonPmRms0
    15454 4958 7832 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l0OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15454 4958 7832

theorem l0OMon_red_pm7833 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7833 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15462)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 4958) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 66 l0OMonPmRms1
    15462 4958 7833 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l0OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15462 4958 7833

theorem l0OMon_red_sm7780 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7780 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 4959 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 18 l0OMonSmNormRef
    4959 7780 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 4959 [7776, 7780, 7784, 7788, 7792]
    5 rfl 7780 (by decide)

theorem l0OMon_red_pm12410 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12410 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7832 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 67 l0OMonPmNormRef0
    7832 12410 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7832
    [15296, 12410, 12420, 12434, 12446] 5 rfl 12410 (by decide)

theorem l0OMon_red_pm12411 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12411 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7833 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 68 l0OMonPmNormRef1
    7833 12411 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7833
    [15298, 12411, 12421, 12435, 12447] 5 rfl 12411 (by decide)

theorem l0OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4958 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 4958 := by
  have h := hInit initGoal_4958 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_4958 pm_goal_1.numRanks _ rfl,
    show initGoal_4958.tps = [{rank := 0, tid := 4958}] from rfl,
    show initGoal_4958.ts = 4958 from rfl,
    show initGoal_4958.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 4958
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 4958
      (by native_decide) (by native_decide)]
  exact hval

theorem l0OMon_red_sm7769 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7769 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 4957 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 16 l0OMonSmResidualRef
    4957 7769 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 4957 [7765, 7769] 2 rfl 7769 (by decide)

theorem l0OMon_red_pm15458 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15458 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7828 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 63 l0OMonPmResidualRef0
    7828 15458 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7828 [15454, 15458] 2 rfl 15458 (by decide)

theorem l0OMon_red_pm15466 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15466 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7829 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 64 l0OMonPmResidualRef1
    7829 15466 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7829 [15462, 15466] 2 rfl 15466 (by decide)


/-! Router graph reductions. -/
theorem l0OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l0OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l0OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4959],
    outs := [7776, 7780, 7784, 7788, 7792], params := [5] }
private def l0OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7832],
    outs := [15296, 12410, 12420, 12434, 12446], params := [5] }
private def l0OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7833],
    outs := [15298, 12411, 12421, 12435, 12447], params := [5] }
private def l0OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [7776], outs := [4960] }
private def l0OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15296, 15298],
    outs := [11742], params := [0] }
private def l0OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11742], outs := [4960] }
private def l0OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [4960, 4961], outs := [4962] }
private def l0OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [4960, 4961], outs := [4962] }
private def l0OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [4962], outs := [7840], params := [0] }
private def l0OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [4962], outs := [7841], params := [0] }
private def l0OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [4962],
    outs := [4963, 4964, 4965], params := [8, 1] }
private def l0OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [7840],
    outs := [7842, 7844, 7846], params := [8, 1] }
private def l0OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [7841],
    outs := [7843, 7845, 7847], params := [8, 1] }

theorem l0OMr_red_sm7776 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7776 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 4959 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 18 l0OMrSmRef
    4959 7776 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 4959
    [7776, 7780, 7784, 7788, 7792] 5 rfl 7776 (by decide)

theorem l0OMr_red_pm15296 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15296 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7832 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 67 l0OMrPmRef0
    7832 15296 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7832
    [15296, 12410, 12420, 12434, 12446] 5 rfl 15296 (by decide)

theorem l0OMr_red_pm15298 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15298 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7833 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 68 l0OMrPmRef1
    7833 15298 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7833
    [15298, 12411, 12421, 12435, 12447] 5 rfl 15298 (by decide)

theorem l0OMr_red_sm4960 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4960 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 7776 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 19 l0OMrSmFloat
    7776 4960 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 7776 4960 []

theorem l0OMr_red_pm11742 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11742 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15296,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15298] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 72 l0OMrPmGather
    15296 15298 11742 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15296, 15298] 11742 0]
  rfl

theorem l0OMr_red_pm4960 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 4960 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11742 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 80 l0OMrPmFloat1
    11742 4960 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11742 4960 []

theorem l0OMr_red_sm4962 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4962 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 4960)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4961) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 23 l0OMrSmNormLinear
    4960 4961 4962 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 4960 4961 4962 []

theorem l0OMr_red_pm4962 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 4962 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 4960)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 4961) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 88 l0OMrPmNormLinear1
    4960 4961 4962 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 4960 4961 4962 []

theorem l0OMr_red_pm7840 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7840 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 4962) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 94 l0OMrPmChunk0
    4962 7840 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 4962 7840 0

theorem l0OMr_red_pm7841 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7841 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 4962) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 95 l0OMrPmChunk1
    4962 7841 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 4962 7841 0

private def l0OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l0OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l0OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l0OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l0OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l0OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l0OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l0OMr_red_sm4963 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 4962).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4963 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 4962) 8 64).1 :=
  l0OMr_red_topk_probs sm_goal_1 initSM 27 l0OMrSmTopk 0 4962 4963 4964 4965
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l0OMr_red_pm7842 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 7840).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7842 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 7840) 8 64).1 :=
  l0OMr_red_topk_probs pm_goal_1 initPM 99 l0OMrPmTopk0 0 7840 7842 7844 7846
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l0OMr_red_pm7843 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 7841).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7843 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 7841) 8 64).1 :=
  l0OMr_red_topk_probs pm_goal_1 initPM 100 l0OMrPmTopk1 1 7841 7843 7845 7847
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l0OMr_red_sm4964 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 4962).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4964 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 4962) 8 64).2.1 :=
  l0OMr_red_topk_map sm_goal_1 initSM 27 l0OMrSmTopk 0 4962 4963 4964 4965
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l0OMr_red_pm7844 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 7840).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7844 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 7840) 8 64).2.1 :=
  l0OMr_red_topk_map pm_goal_1 initPM 99 l0OMrPmTopk0 0 7840 7842 7844 7846
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l0OMr_red_pm7845 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 7841).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7845 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 7841) 8 64).2.1 :=
  l0OMr_red_topk_map pm_goal_1 initPM 100 l0OMrPmTopk1 1 7841 7843 7845 7847
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l0OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 4961 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 4961 ∉ n.outs) := by
  native_decide

theorem l0OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4961 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 4961 := by
  have hi := (hInit initGoal_4961 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_4961 pm_goal_1.numRanks _ rfl,
    show initGoal_4961.tps = [{rank := 0, tid := 4961}] from rfl,
    show initGoal_4961.ts = 4961 from rfl,
    show initGoal_4961.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      4961 (by native_decide) l0OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      4961 (by native_decide) l0OMr_weight_not_written.2]
  exact hi

theorem l0OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 4961).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      4961 (by native_decide) l0OMr_weight_not_written.2]
  exact hPM 4961 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l0OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4959],
    outs := [7776, 7780, 7784, 7788, 7792], params := [5] }
private def l0OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7832],
    outs := [15296, 12410, 12420, 12434, 12446], params := [5] }
private def l0OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7833],
    outs := [15298, 12411, 12421, 12435, 12447], params := [5] }
private def l0OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7784], outs := [4969],
    params := [4096, 1024] }
private def l0OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12420], outs := [7854],
    params := [2048, 1024] }
private def l0OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12421], outs := [7855],
    params := [2048, 1024] }
private def l0OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4969, 4970],
    outs := [4971] }
private def l0OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7854, 4970],
    outs := [7858] }
private def l0OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7855, 4970],
    outs := [7859] }
private def l0OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [4971], outs := [4972],
    params := [4096, 1] }
private def l0OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [7858], outs := [7860],
    params := [2048, 1] }
private def l0OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [7859], outs := [7861],
    params := [2048, 1] }
private def l0OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [4972], outs := [4973] }
private def l0OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [7860], outs := [7862] }
private def l0OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [7861], outs := [7863] }

theorem l0OMrg_red_sm7784 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7784 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 4959 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 18 l0OMrgSmRef
    4959 7784 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 4959 [7776, 7780, 7784, 7788, 7792]
    5 rfl 7784 (by decide)

theorem l0OMrg_red_pm12420 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12420 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7832 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 67 l0OMrgPmRef0
    7832 12420 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7832
    [15296, 12410, 12420, 12434, 12446] 5 rfl 12420 (by decide)

theorem l0OMrg_red_pm12421 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12421 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7833 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 68 l0OMrgPmRef1
    7833 12421 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7833
    [15298, 12411, 12421, 12435, 12447] 5 rfl 12421 (by decide)

theorem l0OMrg_red_sm4969 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4969 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 7784) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 20 l0OMrgSmReshape
    7784 4969 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7784 4969 [4096, 1024]

theorem l0OMrg_red_pm7854 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7854 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12420) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 69 l0OMrgPmReshape0
    12420 7854 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12420 7854 [2048, 1024]

theorem l0OMrg_red_pm7855 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7855 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12421) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 73 l0OMrgPmReshape1
    12421 7855 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12421 7855 [2048, 1024]

theorem l0OMrg_red_sm4971 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4971 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 4969)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4970) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 24 l0OMrgSmLinear
    4969 4970 4971 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 4969 4970 4971

theorem l0OMrg_red_pm7858 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7858 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 7854)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 4970) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 76 l0OMrgPmLinear0
    7854 4970 7858 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 7854 4970 7858

theorem l0OMrg_red_pm7859 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7859 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 7855)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 4970) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 81 l0OMrgPmLinear1
    7855 4970 7859 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 7855 4970 7859

theorem l0OMrg_red_sm4972 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4972 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 4971) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 28 l0OMrgSmView
    4971 4972 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 4971 4972

theorem l0OMrg_red_pm7860 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7860 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 7858) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 84 l0OMrgPmView0
    7858 7860 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 7858 7860

theorem l0OMrg_red_pm7861 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7861 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 7859) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 89 l0OMrgPmView1
    7859 7861 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 7859 7861

theorem l0OMrg_red_sm4973 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4973 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 4972) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 32 l0OMrgSmSigmoid
    4972 4973 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 4972 4973

theorem l0OMrg_red_pm7862 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7862 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 7860) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 92 l0OMrgPmSigmoid0
    7860 7862 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 7860 7862

theorem l0OMrg_red_pm7863 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7863 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 7861) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 96 l0OMrgPmSigmoid1
    7861 7863 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l0OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 7861 7863

theorem l0OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 4970 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 4970 ∉ n.outs) := by
  native_decide

theorem l0OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4970 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 4970 := by
  have hi := (hInit initGoal_4970 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_4970 pm_goal_1.numRanks _ rfl,
    show initGoal_4970.tps = [{rank := 0, tid := 4970}] from rfl,
    show initGoal_4970.ts = 4970 from rfl,
    show initGoal_4970.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 4970
      (by native_decide) l0OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 4970
      (by native_decide) l0OMrg_weight_not_written.2]
  exact hi

theorem l0OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 4970).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 4970 = initPM 4970 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 4970
      (by native_decide) l0OMrg_weight_not_written.2
  rw [e]
  exact hPM 4970 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
