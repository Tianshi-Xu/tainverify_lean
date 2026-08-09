/- Layout-neutral graph reductions and initialized-weight bridge for the L5 ordinary MoE segment. -/
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

def l5OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5232],
    outs := [8025, 8029], params := [2] }
def l5OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8648],
    outs := [15614, 15618], params := [2] }
def l5OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8649],
    outs := [15622, 15626], params := [2] }
def l5OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8025, 5233], outs := [5234] }
def l5OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15614, 5233], outs := [8652] }
def l5OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15622, 5233], outs := [8653] }
def l5OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5234],
    outs := [8036, 8040, 8044, 8048, 8052], params := [5] }
def l5OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8652],
    outs := [15336, 13040, 13050, 13064, 13076], params := [5] }
def l5OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8653],
    outs := [15338, 13041, 13051, 13065, 13077], params := [5] }

theorem l5OMon_red_sm8025 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8025 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5232 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 211 l5OMonSmResidualRef
    5232 8025 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5232 [8025, 8029] 2 rfl 8025 (by decide)

theorem l5OMon_red_pm15614 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15614 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8648 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 483 l5OMonPmResidualRef0
    8648 15614 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8648 [15614, 15618] 2 rfl 15614 (by decide)

theorem l5OMon_red_pm15622 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15622 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8649 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 484 l5OMonPmResidualRef1
    8649 15622 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8649 [15622, 15626] 2 rfl 15622 (by decide)

theorem l5OMon_red_sm5234 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5234 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8025)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5233) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 212 l5OMonSmRms
    8025 5233 5234 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l5OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8025 5233 5234

theorem l5OMon_red_pm8652 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8652 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15614)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5233) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 485 l5OMonPmRms0
    15614 5233 8652 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l5OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15614 5233 8652

theorem l5OMon_red_pm8653 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8653 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15622)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5233) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 486 l5OMonPmRms1
    15622 5233 8653 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l5OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15622 5233 8653

theorem l5OMon_red_sm8040 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8040 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5234 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 213 l5OMonSmNormRef
    5234 8040 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5234 [8036, 8040, 8044, 8048, 8052]
    5 rfl 8040 (by decide)

theorem l5OMon_red_pm13040 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13040 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8652 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 487 l5OMonPmNormRef0
    8652 13040 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8652
    [15336, 13040, 13050, 13064, 13076] 5 rfl 13040 (by decide)

theorem l5OMon_red_pm13041 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13041 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8653 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 488 l5OMonPmNormRef1
    8653 13041 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8653
    [15338, 13041, 13051, 13065, 13077] 5 rfl 13041 (by decide)

theorem l5OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5233 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5233 := by
  have h := hInit initGoal_5233 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5233 pm_goal_1.numRanks _ rfl,
    show initGoal_5233.tps = [{rank := 0, tid := 5233}] from rfl,
    show initGoal_5233.ts = 5233 from rfl,
    show initGoal_5233.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5233
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5233
      (by native_decide) (by native_decide)]
  exact hval

theorem l5OMon_red_sm8029 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8029 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5232 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 211 l5OMonSmResidualRef
    5232 8029 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5232 [8025, 8029] 2 rfl 8029 (by decide)

theorem l5OMon_red_pm15618 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15618 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8648 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 483 l5OMonPmResidualRef0
    8648 15618 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8648 [15614, 15618] 2 rfl 15618 (by decide)

theorem l5OMon_red_pm15626 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15626 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8649 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 484 l5OMonPmResidualRef1
    8649 15626 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8649 [15622, 15626] 2 rfl 15626 (by decide)


/-! Router graph reductions. -/
theorem l5OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l5OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l5OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5234],
    outs := [8036, 8040, 8044, 8048, 8052], params := [5] }
private def l5OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8652],
    outs := [15336, 13040, 13050, 13064, 13076], params := [5] }
private def l5OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8653],
    outs := [15338, 13041, 13051, 13065, 13077], params := [5] }
private def l5OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8036], outs := [5235] }
private def l5OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15336, 15338],
    outs := [11902], params := [0] }
private def l5OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11902], outs := [5235] }
private def l5OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5235, 5236], outs := [5237] }
private def l5OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5235, 5236], outs := [5237] }
private def l5OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5237], outs := [8660], params := [0] }
private def l5OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5237], outs := [8661], params := [0] }
private def l5OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5237],
    outs := [5238, 5239, 5240], params := [8, 1] }
private def l5OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8660],
    outs := [8662, 8664, 8666], params := [8, 1] }
private def l5OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8661],
    outs := [8663, 8665, 8667], params := [8, 1] }

theorem l5OMr_red_sm8036 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8036 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5234 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 213 l5OMrSmRef
    5234 8036 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5234
    [8036, 8040, 8044, 8048, 8052] 5 rfl 8036 (by decide)

theorem l5OMr_red_pm15336 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15336 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8652 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 487 l5OMrPmRef0
    8652 15336 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8652
    [15336, 13040, 13050, 13064, 13076] 5 rfl 15336 (by decide)

theorem l5OMr_red_pm15338 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15338 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8653 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 488 l5OMrPmRef1
    8653 15338 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8653
    [15338, 13041, 13051, 13065, 13077] 5 rfl 15338 (by decide)

theorem l5OMr_red_sm5235 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5235 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8036 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 214 l5OMrSmFloat
    8036 5235 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8036 5235 []

theorem l5OMr_red_pm11902 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11902 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15336,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15338] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 492 l5OMrPmGather
    15336 15338 11902 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15336, 15338] 11902 0]
  rfl

theorem l5OMr_red_pm5235 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5235 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11902 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 500 l5OMrPmFloat1
    11902 5235 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11902 5235 []

theorem l5OMr_red_sm5237 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5237 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5235)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5236) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 218 l5OMrSmNormLinear
    5235 5236 5237 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5235 5236 5237 []

theorem l5OMr_red_pm5237 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5237 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5235)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5236) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 508 l5OMrPmNormLinear1
    5235 5236 5237 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5235 5236 5237 []

theorem l5OMr_red_pm8660 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8660 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5237) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 514 l5OMrPmChunk0
    5237 8660 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5237 8660 0

theorem l5OMr_red_pm8661 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8661 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5237) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 515 l5OMrPmChunk1
    5237 8661 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5237 8661 0

private def l5OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l5OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l5OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l5OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l5OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l5OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l5OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l5OMr_red_sm5238 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5237).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5238 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5237) 8 64).1 :=
  l5OMr_red_topk_probs sm_goal_1 initSM 222 l5OMrSmTopk 0 5237 5238 5239 5240
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l5OMr_red_pm8662 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8660).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8662 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8660) 8 64).1 :=
  l5OMr_red_topk_probs pm_goal_1 initPM 519 l5OMrPmTopk0 0 8660 8662 8664 8666
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l5OMr_red_pm8663 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8661).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8663 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8661) 8 64).1 :=
  l5OMr_red_topk_probs pm_goal_1 initPM 520 l5OMrPmTopk1 1 8661 8663 8665 8667
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l5OMr_red_sm5239 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5237).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5239 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5237) 8 64).2.1 :=
  l5OMr_red_topk_map sm_goal_1 initSM 222 l5OMrSmTopk 0 5237 5238 5239 5240
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l5OMr_red_pm8664 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8660).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8664 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8660) 8 64).2.1 :=
  l5OMr_red_topk_map pm_goal_1 initPM 519 l5OMrPmTopk0 0 8660 8662 8664 8666
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l5OMr_red_pm8665 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8661).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8665 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8661) 8 64).2.1 :=
  l5OMr_red_topk_map pm_goal_1 initPM 520 l5OMrPmTopk1 1 8661 8663 8665 8667
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l5OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5236 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5236 ∉ n.outs) := by
  native_decide

theorem l5OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5236 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5236 := by
  have hi := (hInit initGoal_5236 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5236 pm_goal_1.numRanks _ rfl,
    show initGoal_5236.tps = [{rank := 0, tid := 5236}] from rfl,
    show initGoal_5236.ts = 5236 from rfl,
    show initGoal_5236.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5236 (by native_decide) l5OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5236 (by native_decide) l5OMr_weight_not_written.2]
  exact hi

theorem l5OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5236).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5236 (by native_decide) l5OMr_weight_not_written.2]
  exact hPM 5236 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l5OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5234],
    outs := [8036, 8040, 8044, 8048, 8052], params := [5] }
private def l5OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8652],
    outs := [15336, 13040, 13050, 13064, 13076], params := [5] }
private def l5OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8653],
    outs := [15338, 13041, 13051, 13065, 13077], params := [5] }
private def l5OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8044], outs := [5244],
    params := [4096, 1024] }
private def l5OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13050], outs := [8674],
    params := [2048, 1024] }
private def l5OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13051], outs := [8675],
    params := [2048, 1024] }
private def l5OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5244, 5245],
    outs := [5246] }
private def l5OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8674, 5245],
    outs := [8678] }
private def l5OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8675, 5245],
    outs := [8679] }
private def l5OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5246], outs := [5247],
    params := [4096, 1] }
private def l5OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8678], outs := [8680],
    params := [2048, 1] }
private def l5OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8679], outs := [8681],
    params := [2048, 1] }
private def l5OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5247], outs := [5248] }
private def l5OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [8680], outs := [8682] }
private def l5OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [8681], outs := [8683] }

theorem l5OMrg_red_sm8044 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8044 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5234 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 213 l5OMrgSmRef
    5234 8044 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5234 [8036, 8040, 8044, 8048, 8052]
    5 rfl 8044 (by decide)

theorem l5OMrg_red_pm13050 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13050 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8652 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 487 l5OMrgPmRef0
    8652 13050 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8652
    [15336, 13040, 13050, 13064, 13076] 5 rfl 13050 (by decide)

theorem l5OMrg_red_pm13051 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13051 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8653 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 488 l5OMrgPmRef1
    8653 13051 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8653
    [15338, 13041, 13051, 13065, 13077] 5 rfl 13051 (by decide)

theorem l5OMrg_red_sm5244 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5244 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8044) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 215 l5OMrgSmReshape
    8044 5244 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8044 5244 [4096, 1024]

theorem l5OMrg_red_pm8674 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8674 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13050) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 489 l5OMrgPmReshape0
    13050 8674 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13050 8674 [2048, 1024]

theorem l5OMrg_red_pm8675 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8675 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13051) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 493 l5OMrgPmReshape1
    13051 8675 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13051 8675 [2048, 1024]

theorem l5OMrg_red_sm5246 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5246 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5244)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5245) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 219 l5OMrgSmLinear
    5244 5245 5246 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5244 5245 5246

theorem l5OMrg_red_pm8678 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8678 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8674)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5245) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 496 l5OMrgPmLinear0
    8674 5245 8678 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8674 5245 8678

theorem l5OMrg_red_pm8679 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8679 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8675)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5245) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 501 l5OMrgPmLinear1
    8675 5245 8679 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8675 5245 8679

theorem l5OMrg_red_sm5247 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5247 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5246) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 223 l5OMrgSmView
    5246 5247 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5246 5247

theorem l5OMrg_red_pm8680 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8680 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8678) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 504 l5OMrgPmView0
    8678 8680 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 8678 8680

theorem l5OMrg_red_pm8681 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8681 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8679) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 509 l5OMrgPmView1
    8679 8681 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 8679 8681

theorem l5OMrg_red_sm5248 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5248 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5247) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 227 l5OMrgSmSigmoid
    5247 5248 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5247 5248

theorem l5OMrg_red_pm8682 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8682 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8680) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 512 l5OMrgPmSigmoid0
    8680 8682 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 8680 8682

theorem l5OMrg_red_pm8683 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8683 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8681) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 516 l5OMrgPmSigmoid1
    8681 8683 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l5OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 8681 8683

theorem l5OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5245 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5245 ∉ n.outs) := by
  native_decide

theorem l5OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5245 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5245 := by
  have hi := (hInit initGoal_5245 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5245 pm_goal_1.numRanks _ rfl,
    show initGoal_5245.tps = [{rank := 0, tid := 5245}] from rfl,
    show initGoal_5245.ts = 5245 from rfl,
    show initGoal_5245.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5245
      (by native_decide) l5OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5245
      (by native_decide) l5OMrg_weight_not_written.2]
  exact hi

theorem l5OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5245).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5245 = initPM 5245 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5245
      (by native_decide) l5OMrg_weight_not_written.2
  rw [e]
  exact hPM 5245 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
