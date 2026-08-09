/- Layout-neutral graph reductions and initialized-weight bridge for the L6 ordinary MoE segment. -/
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

def l6OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5287],
    outs := [8077, 8081], params := [2] }
def l6OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8812],
    outs := [15646, 15650], params := [2] }
def l6OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8813],
    outs := [15654, 15658], params := [2] }
def l6OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8077, 5288], outs := [5289] }
def l6OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15646, 5288], outs := [8816] }
def l6OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15654, 5288], outs := [8817] }
def l6OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5289],
    outs := [8088, 8092, 8096, 8100, 8104], params := [5] }
def l6OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8816],
    outs := [15344, 13166, 13176, 13190, 13202], params := [5] }
def l6OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8817],
    outs := [15346, 13167, 13177, 13191, 13203], params := [5] }

theorem l6OMon_red_sm8077 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8077 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5287 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 250 l6OMonSmResidualRef
    5287 8077 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5287 [8077, 8081] 2 rfl 8077 (by decide)

theorem l6OMon_red_pm15646 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15646 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8812 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 567 l6OMonPmResidualRef0
    8812 15646 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8812 [15646, 15650] 2 rfl 15646 (by decide)

theorem l6OMon_red_pm15654 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15654 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8813 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 568 l6OMonPmResidualRef1
    8813 15654 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8813 [15654, 15658] 2 rfl 15654 (by decide)

theorem l6OMon_red_sm5289 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5289 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8077)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5288) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 251 l6OMonSmRms
    8077 5288 5289 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l6OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8077 5288 5289

theorem l6OMon_red_pm8816 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8816 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15646)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5288) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 569 l6OMonPmRms0
    15646 5288 8816 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l6OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15646 5288 8816

theorem l6OMon_red_pm8817 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8817 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15654)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5288) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 570 l6OMonPmRms1
    15654 5288 8817 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l6OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15654 5288 8817

theorem l6OMon_red_sm8092 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8092 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5289 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 252 l6OMonSmNormRef
    5289 8092 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5289 [8088, 8092, 8096, 8100, 8104]
    5 rfl 8092 (by decide)

theorem l6OMon_red_pm13166 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13166 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8816 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 571 l6OMonPmNormRef0
    8816 13166 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8816
    [15344, 13166, 13176, 13190, 13202] 5 rfl 13166 (by decide)

theorem l6OMon_red_pm13167 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13167 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8817 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 572 l6OMonPmNormRef1
    8817 13167 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8817
    [15346, 13167, 13177, 13191, 13203] 5 rfl 13167 (by decide)

theorem l6OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5288 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5288 := by
  have h := hInit initGoal_5288 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5288 pm_goal_1.numRanks _ rfl,
    show initGoal_5288.tps = [{rank := 0, tid := 5288}] from rfl,
    show initGoal_5288.ts = 5288 from rfl,
    show initGoal_5288.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5288
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5288
      (by native_decide) (by native_decide)]
  exact hval

theorem l6OMon_red_sm8081 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8081 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5287 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 250 l6OMonSmResidualRef
    5287 8081 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5287 [8077, 8081] 2 rfl 8081 (by decide)

theorem l6OMon_red_pm15650 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15650 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8812 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 567 l6OMonPmResidualRef0
    8812 15650 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8812 [15646, 15650] 2 rfl 15650 (by decide)

theorem l6OMon_red_pm15658 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15658 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8813 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 568 l6OMonPmResidualRef1
    8813 15658 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8813 [15654, 15658] 2 rfl 15658 (by decide)


/-! Router graph reductions. -/
theorem l6OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l6OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l6OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5289],
    outs := [8088, 8092, 8096, 8100, 8104], params := [5] }
private def l6OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8816],
    outs := [15344, 13166, 13176, 13190, 13202], params := [5] }
private def l6OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8817],
    outs := [15346, 13167, 13177, 13191, 13203], params := [5] }
private def l6OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8088], outs := [5290] }
private def l6OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15344, 15346],
    outs := [11934], params := [0] }
private def l6OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11934], outs := [5290] }
private def l6OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5290, 5291], outs := [5292] }
private def l6OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5290, 5291], outs := [5292] }
private def l6OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5292], outs := [8824], params := [0] }
private def l6OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5292], outs := [8825], params := [0] }
private def l6OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5292],
    outs := [5293, 5294, 5295], params := [8, 1] }
private def l6OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8824],
    outs := [8826, 8828, 8830], params := [8, 1] }
private def l6OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8825],
    outs := [8827, 8829, 8831], params := [8, 1] }

theorem l6OMr_red_sm8088 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8088 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5289 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 252 l6OMrSmRef
    5289 8088 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5289
    [8088, 8092, 8096, 8100, 8104] 5 rfl 8088 (by decide)

theorem l6OMr_red_pm15344 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15344 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8816 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 571 l6OMrPmRef0
    8816 15344 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8816
    [15344, 13166, 13176, 13190, 13202] 5 rfl 15344 (by decide)

theorem l6OMr_red_pm15346 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15346 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8817 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 572 l6OMrPmRef1
    8817 15346 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8817
    [15346, 13167, 13177, 13191, 13203] 5 rfl 15346 (by decide)

theorem l6OMr_red_sm5290 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5290 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8088 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 253 l6OMrSmFloat
    8088 5290 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8088 5290 []

theorem l6OMr_red_pm11934 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11934 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15344,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15346] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 576 l6OMrPmGather
    15344 15346 11934 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15344, 15346] 11934 0]
  rfl

theorem l6OMr_red_pm5290 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5290 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11934 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 584 l6OMrPmFloat1
    11934 5290 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11934 5290 []

theorem l6OMr_red_sm5292 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5292 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5290)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5291) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 257 l6OMrSmNormLinear
    5290 5291 5292 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5290 5291 5292 []

theorem l6OMr_red_pm5292 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5292 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5290)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5291) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 592 l6OMrPmNormLinear1
    5290 5291 5292 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5290 5291 5292 []

theorem l6OMr_red_pm8824 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8824 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5292) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 598 l6OMrPmChunk0
    5292 8824 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5292 8824 0

theorem l6OMr_red_pm8825 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8825 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5292) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 599 l6OMrPmChunk1
    5292 8825 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5292 8825 0

private def l6OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l6OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l6OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l6OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l6OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l6OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l6OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l6OMr_red_sm5293 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5292).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5293 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5292) 8 64).1 :=
  l6OMr_red_topk_probs sm_goal_1 initSM 261 l6OMrSmTopk 0 5292 5293 5294 5295
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l6OMr_red_pm8826 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8824).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8826 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8824) 8 64).1 :=
  l6OMr_red_topk_probs pm_goal_1 initPM 603 l6OMrPmTopk0 0 8824 8826 8828 8830
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l6OMr_red_pm8827 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8825).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8827 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8825) 8 64).1 :=
  l6OMr_red_topk_probs pm_goal_1 initPM 604 l6OMrPmTopk1 1 8825 8827 8829 8831
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l6OMr_red_sm5294 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5292).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5294 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5292) 8 64).2.1 :=
  l6OMr_red_topk_map sm_goal_1 initSM 261 l6OMrSmTopk 0 5292 5293 5294 5295
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l6OMr_red_pm8828 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8824).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8828 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8824) 8 64).2.1 :=
  l6OMr_red_topk_map pm_goal_1 initPM 603 l6OMrPmTopk0 0 8824 8826 8828 8830
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l6OMr_red_pm8829 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8825).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8829 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8825) 8 64).2.1 :=
  l6OMr_red_topk_map pm_goal_1 initPM 604 l6OMrPmTopk1 1 8825 8827 8829 8831
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l6OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5291 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5291 ∉ n.outs) := by
  native_decide

theorem l6OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5291 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5291 := by
  have hi := (hInit initGoal_5291 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5291 pm_goal_1.numRanks _ rfl,
    show initGoal_5291.tps = [{rank := 0, tid := 5291}] from rfl,
    show initGoal_5291.ts = 5291 from rfl,
    show initGoal_5291.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5291 (by native_decide) l6OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5291 (by native_decide) l6OMr_weight_not_written.2]
  exact hi

theorem l6OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5291).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5291 (by native_decide) l6OMr_weight_not_written.2]
  exact hPM 5291 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l6OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5289],
    outs := [8088, 8092, 8096, 8100, 8104], params := [5] }
private def l6OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8816],
    outs := [15344, 13166, 13176, 13190, 13202], params := [5] }
private def l6OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8817],
    outs := [15346, 13167, 13177, 13191, 13203], params := [5] }
private def l6OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8096], outs := [5299],
    params := [4096, 1024] }
private def l6OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13176], outs := [8838],
    params := [2048, 1024] }
private def l6OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13177], outs := [8839],
    params := [2048, 1024] }
private def l6OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5299, 5300],
    outs := [5301] }
private def l6OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8838, 5300],
    outs := [8842] }
private def l6OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8839, 5300],
    outs := [8843] }
private def l6OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5301], outs := [5302],
    params := [4096, 1] }
private def l6OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8842], outs := [8844],
    params := [2048, 1] }
private def l6OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8843], outs := [8845],
    params := [2048, 1] }
private def l6OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5302], outs := [5303] }
private def l6OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [8844], outs := [8846] }
private def l6OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [8845], outs := [8847] }

theorem l6OMrg_red_sm8096 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8096 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5289 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 252 l6OMrgSmRef
    5289 8096 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5289 [8088, 8092, 8096, 8100, 8104]
    5 rfl 8096 (by decide)

theorem l6OMrg_red_pm13176 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13176 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8816 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 571 l6OMrgPmRef0
    8816 13176 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8816
    [15344, 13166, 13176, 13190, 13202] 5 rfl 13176 (by decide)

theorem l6OMrg_red_pm13177 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13177 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8817 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 572 l6OMrgPmRef1
    8817 13177 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8817
    [15346, 13167, 13177, 13191, 13203] 5 rfl 13177 (by decide)

theorem l6OMrg_red_sm5299 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5299 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8096) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 254 l6OMrgSmReshape
    8096 5299 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8096 5299 [4096, 1024]

theorem l6OMrg_red_pm8838 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8838 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13176) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 573 l6OMrgPmReshape0
    13176 8838 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13176 8838 [2048, 1024]

theorem l6OMrg_red_pm8839 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8839 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13177) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 577 l6OMrgPmReshape1
    13177 8839 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13177 8839 [2048, 1024]

theorem l6OMrg_red_sm5301 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5301 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5299)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5300) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 258 l6OMrgSmLinear
    5299 5300 5301 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5299 5300 5301

theorem l6OMrg_red_pm8842 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8842 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8838)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5300) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 580 l6OMrgPmLinear0
    8838 5300 8842 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8838 5300 8842

theorem l6OMrg_red_pm8843 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8843 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8839)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5300) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 585 l6OMrgPmLinear1
    8839 5300 8843 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8839 5300 8843

theorem l6OMrg_red_sm5302 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5302 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5301) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 262 l6OMrgSmView
    5301 5302 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5301 5302

theorem l6OMrg_red_pm8844 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8844 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8842) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 588 l6OMrgPmView0
    8842 8844 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 8842 8844

theorem l6OMrg_red_pm8845 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8845 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8843) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 593 l6OMrgPmView1
    8843 8845 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 8843 8845

theorem l6OMrg_red_sm5303 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5303 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5302) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 266 l6OMrgSmSigmoid
    5302 5303 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5302 5303

theorem l6OMrg_red_pm8846 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8846 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8844) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 596 l6OMrgPmSigmoid0
    8844 8846 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 8844 8846

theorem l6OMrg_red_pm8847 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8847 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8845) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 600 l6OMrgPmSigmoid1
    8845 8847 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l6OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 8845 8847

theorem l6OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5300 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5300 ∉ n.outs) := by
  native_decide

theorem l6OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5300 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5300 := by
  have hi := (hInit initGoal_5300 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5300 pm_goal_1.numRanks _ rfl,
    show initGoal_5300.tps = [{rank := 0, tid := 5300}] from rfl,
    show initGoal_5300.ts = 5300 from rfl,
    show initGoal_5300.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5300
      (by native_decide) l6OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5300
      (by native_decide) l6OMrg_weight_not_written.2]
  exact hi

theorem l6OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5300).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5300 = initPM 5300 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5300
      (by native_decide) l6OMrg_weight_not_written.2
  rw [e]
  exact hPM 5300 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
