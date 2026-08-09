/- Layout-neutral graph reductions and initialized-weight bridge for the L4 ordinary MoE segment. -/
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

def l4OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5177],
    outs := [7973, 7977], params := [2] }
def l4OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8484],
    outs := [15582, 15586], params := [2] }
def l4OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8485],
    outs := [15590, 15594], params := [2] }
def l4OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [7973, 5178], outs := [5179] }
def l4OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15582, 5178], outs := [8488] }
def l4OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15590, 5178], outs := [8489] }
def l4OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5179],
    outs := [7984, 7988, 7992, 7996, 8000], params := [5] }
def l4OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8488],
    outs := [15328, 12914, 12924, 12938, 12950], params := [5] }
def l4OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8489],
    outs := [15330, 12915, 12925, 12939, 12951], params := [5] }

theorem l4OMon_red_sm7973 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7973 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5177 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 172 l4OMonSmResidualRef
    5177 7973 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5177 [7973, 7977] 2 rfl 7973 (by decide)

theorem l4OMon_red_pm15582 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15582 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8484 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 399 l4OMonPmResidualRef0
    8484 15582 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8484 [15582, 15586] 2 rfl 15582 (by decide)

theorem l4OMon_red_pm15590 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15590 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8485 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 400 l4OMonPmResidualRef1
    8485 15590 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8485 [15590, 15594] 2 rfl 15590 (by decide)

theorem l4OMon_red_sm5179 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5179 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7973)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5178) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 173 l4OMonSmRms
    7973 5178 5179 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l4OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 7973 5178 5179

theorem l4OMon_red_pm8488 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8488 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15582)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5178) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 401 l4OMonPmRms0
    15582 5178 8488 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l4OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15582 5178 8488

theorem l4OMon_red_pm8489 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8489 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15590)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5178) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 402 l4OMonPmRms1
    15590 5178 8489 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l4OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15590 5178 8489

theorem l4OMon_red_sm7988 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7988 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5179 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 174 l4OMonSmNormRef
    5179 7988 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5179 [7984, 7988, 7992, 7996, 8000]
    5 rfl 7988 (by decide)

theorem l4OMon_red_pm12914 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12914 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8488 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 403 l4OMonPmNormRef0
    8488 12914 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8488
    [15328, 12914, 12924, 12938, 12950] 5 rfl 12914 (by decide)

theorem l4OMon_red_pm12915 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12915 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8489 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 404 l4OMonPmNormRef1
    8489 12915 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8489
    [15330, 12915, 12925, 12939, 12951] 5 rfl 12915 (by decide)

theorem l4OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5178 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5178 := by
  have h := hInit initGoal_5178 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5178 pm_goal_1.numRanks _ rfl,
    show initGoal_5178.tps = [{rank := 0, tid := 5178}] from rfl,
    show initGoal_5178.ts = 5178 from rfl,
    show initGoal_5178.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5178
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5178
      (by native_decide) (by native_decide)]
  exact hval

theorem l4OMon_red_sm7977 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7977 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5177 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 172 l4OMonSmResidualRef
    5177 7977 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5177 [7973, 7977] 2 rfl 7977 (by decide)

theorem l4OMon_red_pm15586 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15586 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8484 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 399 l4OMonPmResidualRef0
    8484 15586 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8484 [15582, 15586] 2 rfl 15586 (by decide)

theorem l4OMon_red_pm15594 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15594 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8485 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 400 l4OMonPmResidualRef1
    8485 15594 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8485 [15590, 15594] 2 rfl 15594 (by decide)


/-! Router graph reductions. -/
theorem l4OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l4OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l4OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5179],
    outs := [7984, 7988, 7992, 7996, 8000], params := [5] }
private def l4OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8488],
    outs := [15328, 12914, 12924, 12938, 12950], params := [5] }
private def l4OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8489],
    outs := [15330, 12915, 12925, 12939, 12951], params := [5] }
private def l4OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [7984], outs := [5180] }
private def l4OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15328, 15330],
    outs := [11870], params := [0] }
private def l4OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11870], outs := [5180] }
private def l4OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5180, 5181], outs := [5182] }
private def l4OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5180, 5181], outs := [5182] }
private def l4OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5182], outs := [8496], params := [0] }
private def l4OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5182], outs := [8497], params := [0] }
private def l4OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5182],
    outs := [5183, 5184, 5185], params := [8, 1] }
private def l4OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8496],
    outs := [8498, 8500, 8502], params := [8, 1] }
private def l4OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8497],
    outs := [8499, 8501, 8503], params := [8, 1] }

theorem l4OMr_red_sm7984 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7984 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5179 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 174 l4OMrSmRef
    5179 7984 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5179
    [7984, 7988, 7992, 7996, 8000] 5 rfl 7984 (by decide)

theorem l4OMr_red_pm15328 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15328 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8488 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 403 l4OMrPmRef0
    8488 15328 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8488
    [15328, 12914, 12924, 12938, 12950] 5 rfl 15328 (by decide)

theorem l4OMr_red_pm15330 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15330 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8489 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 404 l4OMrPmRef1
    8489 15330 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8489
    [15330, 12915, 12925, 12939, 12951] 5 rfl 15330 (by decide)

theorem l4OMr_red_sm5180 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5180 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 7984 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 175 l4OMrSmFloat
    7984 5180 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 7984 5180 []

theorem l4OMr_red_pm11870 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11870 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15328,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15330] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 408 l4OMrPmGather
    15328 15330 11870 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15328, 15330] 11870 0]
  rfl

theorem l4OMr_red_pm5180 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5180 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11870 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 416 l4OMrPmFloat1
    11870 5180 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11870 5180 []

theorem l4OMr_red_sm5182 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5182 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5180)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5181) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 179 l4OMrSmNormLinear
    5180 5181 5182 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5180 5181 5182 []

theorem l4OMr_red_pm5182 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5182 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5180)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5181) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 424 l4OMrPmNormLinear1
    5180 5181 5182 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5180 5181 5182 []

theorem l4OMr_red_pm8496 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8496 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5182) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 430 l4OMrPmChunk0
    5182 8496 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5182 8496 0

theorem l4OMr_red_pm8497 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8497 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5182) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 431 l4OMrPmChunk1
    5182 8497 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5182 8497 0

private def l4OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l4OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l4OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l4OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l4OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l4OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l4OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l4OMr_red_sm5183 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5182).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5183 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5182) 8 64).1 :=
  l4OMr_red_topk_probs sm_goal_1 initSM 183 l4OMrSmTopk 0 5182 5183 5184 5185
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l4OMr_red_pm8498 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8496).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8498 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8496) 8 64).1 :=
  l4OMr_red_topk_probs pm_goal_1 initPM 435 l4OMrPmTopk0 0 8496 8498 8500 8502
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l4OMr_red_pm8499 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8497).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8499 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8497) 8 64).1 :=
  l4OMr_red_topk_probs pm_goal_1 initPM 436 l4OMrPmTopk1 1 8497 8499 8501 8503
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l4OMr_red_sm5184 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5182).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5184 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5182) 8 64).2.1 :=
  l4OMr_red_topk_map sm_goal_1 initSM 183 l4OMrSmTopk 0 5182 5183 5184 5185
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l4OMr_red_pm8500 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8496).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8500 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8496) 8 64).2.1 :=
  l4OMr_red_topk_map pm_goal_1 initPM 435 l4OMrPmTopk0 0 8496 8498 8500 8502
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l4OMr_red_pm8501 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8497).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8501 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8497) 8 64).2.1 :=
  l4OMr_red_topk_map pm_goal_1 initPM 436 l4OMrPmTopk1 1 8497 8499 8501 8503
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l4OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5181 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5181 ∉ n.outs) := by
  native_decide

theorem l4OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5181 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5181 := by
  have hi := (hInit initGoal_5181 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5181 pm_goal_1.numRanks _ rfl,
    show initGoal_5181.tps = [{rank := 0, tid := 5181}] from rfl,
    show initGoal_5181.ts = 5181 from rfl,
    show initGoal_5181.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5181 (by native_decide) l4OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5181 (by native_decide) l4OMr_weight_not_written.2]
  exact hi

theorem l4OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5181).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5181 (by native_decide) l4OMr_weight_not_written.2]
  exact hPM 5181 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l4OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5179],
    outs := [7984, 7988, 7992, 7996, 8000], params := [5] }
private def l4OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8488],
    outs := [15328, 12914, 12924, 12938, 12950], params := [5] }
private def l4OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8489],
    outs := [15330, 12915, 12925, 12939, 12951], params := [5] }
private def l4OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7992], outs := [5189],
    params := [4096, 1024] }
private def l4OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12924], outs := [8510],
    params := [2048, 1024] }
private def l4OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12925], outs := [8511],
    params := [2048, 1024] }
private def l4OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5189, 5190],
    outs := [5191] }
private def l4OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8510, 5190],
    outs := [8514] }
private def l4OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8511, 5190],
    outs := [8515] }
private def l4OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5191], outs := [5192],
    params := [4096, 1] }
private def l4OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8514], outs := [8516],
    params := [2048, 1] }
private def l4OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8515], outs := [8517],
    params := [2048, 1] }
private def l4OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5192], outs := [5193] }
private def l4OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [8516], outs := [8518] }
private def l4OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [8517], outs := [8519] }

theorem l4OMrg_red_sm7992 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7992 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5179 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 174 l4OMrgSmRef
    5179 7992 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5179 [7984, 7988, 7992, 7996, 8000]
    5 rfl 7992 (by decide)

theorem l4OMrg_red_pm12924 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12924 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8488 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 403 l4OMrgPmRef0
    8488 12924 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8488
    [15328, 12914, 12924, 12938, 12950] 5 rfl 12924 (by decide)

theorem l4OMrg_red_pm12925 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12925 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8489 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 404 l4OMrgPmRef1
    8489 12925 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8489
    [15330, 12915, 12925, 12939, 12951] 5 rfl 12925 (by decide)

theorem l4OMrg_red_sm5189 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5189 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 7992) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 176 l4OMrgSmReshape
    7992 5189 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7992 5189 [4096, 1024]

theorem l4OMrg_red_pm8510 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8510 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12924) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 405 l4OMrgPmReshape0
    12924 8510 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12924 8510 [2048, 1024]

theorem l4OMrg_red_pm8511 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8511 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12925) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 409 l4OMrgPmReshape1
    12925 8511 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12925 8511 [2048, 1024]

theorem l4OMrg_red_sm5191 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5191 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5189)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5190) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 180 l4OMrgSmLinear
    5189 5190 5191 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5189 5190 5191

theorem l4OMrg_red_pm8514 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8514 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8510)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5190) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 412 l4OMrgPmLinear0
    8510 5190 8514 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8510 5190 8514

theorem l4OMrg_red_pm8515 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8515 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8511)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5190) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 417 l4OMrgPmLinear1
    8511 5190 8515 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8511 5190 8515

theorem l4OMrg_red_sm5192 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5192 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5191) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 184 l4OMrgSmView
    5191 5192 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5191 5192

theorem l4OMrg_red_pm8516 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8516 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8514) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 420 l4OMrgPmView0
    8514 8516 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 8514 8516

theorem l4OMrg_red_pm8517 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8517 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8515) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 425 l4OMrgPmView1
    8515 8517 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 8515 8517

theorem l4OMrg_red_sm5193 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5193 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5192) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 188 l4OMrgSmSigmoid
    5192 5193 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5192 5193

theorem l4OMrg_red_pm8518 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8518 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8516) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 428 l4OMrgPmSigmoid0
    8516 8518 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 8516 8518

theorem l4OMrg_red_pm8519 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8519 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8517) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 432 l4OMrgPmSigmoid1
    8517 8519 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l4OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 8517 8519

theorem l4OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5190 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5190 ∉ n.outs) := by
  native_decide

theorem l4OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5190 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5190 := by
  have hi := (hInit initGoal_5190 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5190 pm_goal_1.numRanks _ rfl,
    show initGoal_5190.tps = [{rank := 0, tid := 5190}] from rfl,
    show initGoal_5190.ts = 5190 from rfl,
    show initGoal_5190.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5190
      (by native_decide) l4OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5190
      (by native_decide) l4OMrg_weight_not_written.2]
  exact hi

theorem l4OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5190).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5190 = initPM 5190 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5190
      (by native_decide) l4OMrg_weight_not_written.2
  rw [e]
  exact hPM 5190 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
