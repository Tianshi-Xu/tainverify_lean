/- Layout-neutral graph reductions and initialized-weight bridge for the L1 ordinary MoE segment. -/
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

def l1OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5012],
    outs := [7817, 7821], params := [2] }
def l1OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7992],
    outs := [15486, 15490], params := [2] }
def l1OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7993],
    outs := [15494, 15498], params := [2] }
def l1OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [7817, 5013], outs := [5014] }
def l1OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15486, 5013], outs := [7996] }
def l1OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15494, 5013], outs := [7997] }
def l1OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5014],
    outs := [7828, 7832, 7836, 7840, 7844], params := [5] }
def l1OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7996],
    outs := [15304, 12536, 12546, 12560, 12572], params := [5] }
def l1OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7997],
    outs := [15306, 12537, 12547, 12561, 12573], params := [5] }

theorem l1OMon_red_sm7817 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7817 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5012 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 55 l1OMonSmResidualRef
    5012 7817 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5012 [7817, 7821] 2 rfl 7817 (by decide)

theorem l1OMon_red_pm15486 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15486 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7992 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 147 l1OMonPmResidualRef0
    7992 15486 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7992 [15486, 15490] 2 rfl 15486 (by decide)

theorem l1OMon_red_pm15494 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15494 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7993 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 148 l1OMonPmResidualRef1
    7993 15494 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7993 [15494, 15498] 2 rfl 15494 (by decide)

theorem l1OMon_red_sm5014 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5014 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7817)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5013) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 56 l1OMonSmRms
    7817 5013 5014 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l1OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 7817 5013 5014

theorem l1OMon_red_pm7996 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7996 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15486)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5013) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 149 l1OMonPmRms0
    15486 5013 7996 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l1OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15486 5013 7996

theorem l1OMon_red_pm7997 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7997 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15494)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5013) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 150 l1OMonPmRms1
    15494 5013 7997 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l1OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15494 5013 7997

theorem l1OMon_red_sm7832 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7832 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5014 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 57 l1OMonSmNormRef
    5014 7832 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5014 [7828, 7832, 7836, 7840, 7844]
    5 rfl 7832 (by decide)

theorem l1OMon_red_pm12536 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12536 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7996 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 151 l1OMonPmNormRef0
    7996 12536 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7996
    [15304, 12536, 12546, 12560, 12572] 5 rfl 12536 (by decide)

theorem l1OMon_red_pm12537 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12537 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7997 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 152 l1OMonPmNormRef1
    7997 12537 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7997
    [15306, 12537, 12547, 12561, 12573] 5 rfl 12537 (by decide)

theorem l1OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5013 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5013 := by
  have h := hInit initGoal_5013 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5013 pm_goal_1.numRanks _ rfl,
    show initGoal_5013.tps = [{rank := 0, tid := 5013}] from rfl,
    show initGoal_5013.ts = 5013 from rfl,
    show initGoal_5013.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5013
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5013
      (by native_decide) (by native_decide)]
  exact hval

theorem l1OMon_red_sm7821 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7821 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5012 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 55 l1OMonSmResidualRef
    5012 7821 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5012 [7817, 7821] 2 rfl 7821 (by decide)

theorem l1OMon_red_pm15490 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15490 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7992 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 147 l1OMonPmResidualRef0
    7992 15490 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7992 [15486, 15490] 2 rfl 15490 (by decide)

theorem l1OMon_red_pm15498 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15498 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7993 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 148 l1OMonPmResidualRef1
    7993 15498 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7993 [15494, 15498] 2 rfl 15498 (by decide)


/-! Router graph reductions. -/
theorem l1OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l1OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l1OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5014],
    outs := [7828, 7832, 7836, 7840, 7844], params := [5] }
private def l1OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7996],
    outs := [15304, 12536, 12546, 12560, 12572], params := [5] }
private def l1OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7997],
    outs := [15306, 12537, 12547, 12561, 12573], params := [5] }
private def l1OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [7828], outs := [5015] }
private def l1OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15304, 15306],
    outs := [11774], params := [0] }
private def l1OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11774], outs := [5015] }
private def l1OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5015, 5016], outs := [5017] }
private def l1OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5015, 5016], outs := [5017] }
private def l1OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5017], outs := [8004], params := [0] }
private def l1OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5017], outs := [8005], params := [0] }
private def l1OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5017],
    outs := [5018, 5019, 5020], params := [8, 1] }
private def l1OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8004],
    outs := [8006, 8008, 8010], params := [8, 1] }
private def l1OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8005],
    outs := [8007, 8009, 8011], params := [8, 1] }

theorem l1OMr_red_sm7828 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7828 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5014 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 57 l1OMrSmRef
    5014 7828 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5014
    [7828, 7832, 7836, 7840, 7844] 5 rfl 7828 (by decide)

theorem l1OMr_red_pm15304 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15304 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7996 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 151 l1OMrPmRef0
    7996 15304 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7996
    [15304, 12536, 12546, 12560, 12572] 5 rfl 15304 (by decide)

theorem l1OMr_red_pm15306 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15306 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7997 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 152 l1OMrPmRef1
    7997 15306 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7997
    [15306, 12537, 12547, 12561, 12573] 5 rfl 15306 (by decide)

theorem l1OMr_red_sm5015 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5015 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 7828 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 58 l1OMrSmFloat
    7828 5015 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 7828 5015 []

theorem l1OMr_red_pm11774 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11774 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15304,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15306] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 156 l1OMrPmGather
    15304 15306 11774 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15304, 15306] 11774 0]
  rfl

theorem l1OMr_red_pm5015 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5015 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11774 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 164 l1OMrPmFloat1
    11774 5015 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11774 5015 []

theorem l1OMr_red_sm5017 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5017 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5015)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5016) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 62 l1OMrSmNormLinear
    5015 5016 5017 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5015 5016 5017 []

theorem l1OMr_red_pm5017 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5017 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5015)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5016) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 172 l1OMrPmNormLinear1
    5015 5016 5017 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5015 5016 5017 []

theorem l1OMr_red_pm8004 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8004 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5017) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 178 l1OMrPmChunk0
    5017 8004 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5017 8004 0

theorem l1OMr_red_pm8005 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8005 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5017) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 179 l1OMrPmChunk1
    5017 8005 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5017 8005 0

private def l1OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l1OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l1OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l1OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l1OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l1OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l1OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l1OMr_red_sm5018 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5017).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5018 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5017) 8 64).1 :=
  l1OMr_red_topk_probs sm_goal_1 initSM 66 l1OMrSmTopk 0 5017 5018 5019 5020
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l1OMr_red_pm8006 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8004).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8006 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8004) 8 64).1 :=
  l1OMr_red_topk_probs pm_goal_1 initPM 183 l1OMrPmTopk0 0 8004 8006 8008 8010
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l1OMr_red_pm8007 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8005).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8007 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8005) 8 64).1 :=
  l1OMr_red_topk_probs pm_goal_1 initPM 184 l1OMrPmTopk1 1 8005 8007 8009 8011
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l1OMr_red_sm5019 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5017).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5019 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5017) 8 64).2.1 :=
  l1OMr_red_topk_map sm_goal_1 initSM 66 l1OMrSmTopk 0 5017 5018 5019 5020
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l1OMr_red_pm8008 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8004).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8008 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8004) 8 64).2.1 :=
  l1OMr_red_topk_map pm_goal_1 initPM 183 l1OMrPmTopk0 0 8004 8006 8008 8010
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l1OMr_red_pm8009 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8005).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8009 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8005) 8 64).2.1 :=
  l1OMr_red_topk_map pm_goal_1 initPM 184 l1OMrPmTopk1 1 8005 8007 8009 8011
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l1OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5016 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5016 ∉ n.outs) := by
  native_decide

theorem l1OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5016 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5016 := by
  have hi := (hInit initGoal_5016 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5016 pm_goal_1.numRanks _ rfl,
    show initGoal_5016.tps = [{rank := 0, tid := 5016}] from rfl,
    show initGoal_5016.ts = 5016 from rfl,
    show initGoal_5016.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5016 (by native_decide) l1OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5016 (by native_decide) l1OMr_weight_not_written.2]
  exact hi

theorem l1OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5016).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5016 (by native_decide) l1OMr_weight_not_written.2]
  exact hPM 5016 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l1OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5014],
    outs := [7828, 7832, 7836, 7840, 7844], params := [5] }
private def l1OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [7996],
    outs := [15304, 12536, 12546, 12560, 12572], params := [5] }
private def l1OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [7997],
    outs := [15306, 12537, 12547, 12561, 12573], params := [5] }
private def l1OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7836], outs := [5024],
    params := [4096, 1024] }
private def l1OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12546], outs := [8018],
    params := [2048, 1024] }
private def l1OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12547], outs := [8019],
    params := [2048, 1024] }
private def l1OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5024, 5025],
    outs := [5026] }
private def l1OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8018, 5025],
    outs := [8022] }
private def l1OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8019, 5025],
    outs := [8023] }
private def l1OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5026], outs := [5027],
    params := [4096, 1] }
private def l1OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8022], outs := [8024],
    params := [2048, 1] }
private def l1OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8023], outs := [8025],
    params := [2048, 1] }
private def l1OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5027], outs := [5028] }
private def l1OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [8024], outs := [8026] }
private def l1OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [8025], outs := [8027] }

theorem l1OMrg_red_sm7836 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7836 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5014 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 57 l1OMrgSmRef
    5014 7836 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5014 [7828, 7832, 7836, 7840, 7844]
    5 rfl 7836 (by decide)

theorem l1OMrg_red_pm12546 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12546 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7996 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 151 l1OMrgPmRef0
    7996 12546 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 7996
    [15304, 12536, 12546, 12560, 12572] 5 rfl 12546 (by decide)

theorem l1OMrg_red_pm12547 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12547 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7997 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 152 l1OMrgPmRef1
    7997 12547 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 7997
    [15306, 12537, 12547, 12561, 12573] 5 rfl 12547 (by decide)

theorem l1OMrg_red_sm5024 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5024 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 7836) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 59 l1OMrgSmReshape
    7836 5024 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7836 5024 [4096, 1024]

theorem l1OMrg_red_pm8018 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8018 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12546) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 153 l1OMrgPmReshape0
    12546 8018 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12546 8018 [2048, 1024]

theorem l1OMrg_red_pm8019 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8019 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12547) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 157 l1OMrgPmReshape1
    12547 8019 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12547 8019 [2048, 1024]

theorem l1OMrg_red_sm5026 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5026 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5024)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5025) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 63 l1OMrgSmLinear
    5024 5025 5026 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5024 5025 5026

theorem l1OMrg_red_pm8022 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8022 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8018)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5025) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 160 l1OMrgPmLinear0
    8018 5025 8022 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8018 5025 8022

theorem l1OMrg_red_pm8023 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8023 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8019)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5025) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 165 l1OMrgPmLinear1
    8019 5025 8023 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8019 5025 8023

theorem l1OMrg_red_sm5027 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5027 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5026) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 67 l1OMrgSmView
    5026 5027 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5026 5027

theorem l1OMrg_red_pm8024 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8024 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8022) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 168 l1OMrgPmView0
    8022 8024 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 8022 8024

theorem l1OMrg_red_pm8025 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8025 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8023) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 173 l1OMrgPmView1
    8023 8025 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 8023 8025

theorem l1OMrg_red_sm5028 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5028 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5027) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 71 l1OMrgSmSigmoid
    5027 5028 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5027 5028

theorem l1OMrg_red_pm8026 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8026 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8024) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 176 l1OMrgPmSigmoid0
    8024 8026 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 8024 8026

theorem l1OMrg_red_pm8027 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8027 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8025) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 180 l1OMrgPmSigmoid1
    8025 8027 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l1OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 8025 8027

theorem l1OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5025 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5025 ∉ n.outs) := by
  native_decide

theorem l1OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5025 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5025 := by
  have hi := (hInit initGoal_5025 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5025 pm_goal_1.numRanks _ rfl,
    show initGoal_5025.tps = [{rank := 0, tid := 5025}] from rfl,
    show initGoal_5025.ts = 5025 from rfl,
    show initGoal_5025.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5025
      (by native_decide) l1OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5025
      (by native_decide) l1OMrg_weight_not_written.2]
  exact hi

theorem l1OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5025).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5025 = initPM 5025 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5025
      (by native_decide) l1OMrg_weight_not_written.2
  rw [e]
  exact hPM 5025 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
