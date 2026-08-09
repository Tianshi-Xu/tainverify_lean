/- Layout-neutral graph reductions and initialized-weight bridge for the L8 ordinary MoE segment. -/
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

def l8OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5397],
    outs := [8181, 8185], params := [2] }
def l8OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9140],
    outs := [15710, 15714], params := [2] }
def l8OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9141],
    outs := [15718, 15722], params := [2] }
def l8OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8181, 5398], outs := [5399] }
def l8OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15710, 5398], outs := [9144] }
def l8OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15718, 5398], outs := [9145] }
def l8OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5399],
    outs := [8192, 8196, 8200, 8204, 8208], params := [5] }
def l8OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9144],
    outs := [15360, 13418, 13428, 13442, 13454], params := [5] }
def l8OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9145],
    outs := [15362, 13419, 13429, 13443, 13455], params := [5] }

theorem l8OMon_red_sm8181 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8181 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5397 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 328 l8OMonSmResidualRef
    5397 8181 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5397 [8181, 8185] 2 rfl 8181 (by decide)

theorem l8OMon_red_pm15710 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15710 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9140 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 735 l8OMonPmResidualRef0
    9140 15710 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9140 [15710, 15714] 2 rfl 15710 (by decide)

theorem l8OMon_red_pm15718 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9141 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 736 l8OMonPmResidualRef1
    9141 15718 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9141 [15718, 15722] 2 rfl 15718 (by decide)

theorem l8OMon_red_sm5399 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5399 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8181)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5398) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 329 l8OMonSmRms
    8181 5398 5399 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l8OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8181 5398 5399

theorem l8OMon_red_pm9144 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9144 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15710)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5398) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 737 l8OMonPmRms0
    15710 5398 9144 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l8OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15710 5398 9144

theorem l8OMon_red_pm9145 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9145 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15718)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5398) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 738 l8OMonPmRms1
    15718 5398 9145 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l8OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15718 5398 9145

theorem l8OMon_red_sm8196 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8196 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5399 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 330 l8OMonSmNormRef
    5399 8196 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5399 [8192, 8196, 8200, 8204, 8208]
    5 rfl 8196 (by decide)

theorem l8OMon_red_pm13418 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13418 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9144 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 739 l8OMonPmNormRef0
    9144 13418 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9144
    [15360, 13418, 13428, 13442, 13454] 5 rfl 13418 (by decide)

theorem l8OMon_red_pm13419 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13419 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9145 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 740 l8OMonPmNormRef1
    9145 13419 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9145
    [15362, 13419, 13429, 13443, 13455] 5 rfl 13419 (by decide)

theorem l8OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5398 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5398 := by
  have h := hInit initGoal_5398 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5398 pm_goal_1.numRanks _ rfl,
    show initGoal_5398.tps = [{rank := 0, tid := 5398}] from rfl,
    show initGoal_5398.ts = 5398 from rfl,
    show initGoal_5398.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5398
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5398
      (by native_decide) (by native_decide)]
  exact hval

theorem l8OMon_red_sm8185 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8185 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5397 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 328 l8OMonSmResidualRef
    5397 8185 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5397 [8181, 8185] 2 rfl 8185 (by decide)

theorem l8OMon_red_pm15714 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15714 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9140 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 735 l8OMonPmResidualRef0
    9140 15714 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9140 [15710, 15714] 2 rfl 15714 (by decide)

theorem l8OMon_red_pm15722 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15722 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9141 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 736 l8OMonPmResidualRef1
    9141 15722 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9141 [15718, 15722] 2 rfl 15722 (by decide)


/-! Router graph reductions. -/
theorem l8OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l8OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l8OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5399],
    outs := [8192, 8196, 8200, 8204, 8208], params := [5] }
private def l8OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9144],
    outs := [15360, 13418, 13428, 13442, 13454], params := [5] }
private def l8OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9145],
    outs := [15362, 13419, 13429, 13443, 13455], params := [5] }
private def l8OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8192], outs := [5400] }
private def l8OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15360, 15362],
    outs := [11998], params := [0] }
private def l8OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11998], outs := [5400] }
private def l8OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5400, 5401], outs := [5402] }
private def l8OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5400, 5401], outs := [5402] }
private def l8OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5402], outs := [9152], params := [0] }
private def l8OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5402], outs := [9153], params := [0] }
private def l8OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5402],
    outs := [5403, 5404, 5405], params := [8, 1] }
private def l8OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9152],
    outs := [9154, 9156, 9158], params := [8, 1] }
private def l8OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9153],
    outs := [9155, 9157, 9159], params := [8, 1] }

theorem l8OMr_red_sm8192 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8192 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5399 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 330 l8OMrSmRef
    5399 8192 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5399
    [8192, 8196, 8200, 8204, 8208] 5 rfl 8192 (by decide)

theorem l8OMr_red_pm15360 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15360 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9144 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 739 l8OMrPmRef0
    9144 15360 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9144
    [15360, 13418, 13428, 13442, 13454] 5 rfl 15360 (by decide)

theorem l8OMr_red_pm15362 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15362 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9145 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 740 l8OMrPmRef1
    9145 15362 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9145
    [15362, 13419, 13429, 13443, 13455] 5 rfl 15362 (by decide)

theorem l8OMr_red_sm5400 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5400 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8192 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 331 l8OMrSmFloat
    8192 5400 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8192 5400 []

theorem l8OMr_red_pm11998 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11998 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15360,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15362] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 744 l8OMrPmGather
    15360 15362 11998 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15360, 15362] 11998 0]
  rfl

theorem l8OMr_red_pm5400 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5400 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11998 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 752 l8OMrPmFloat1
    11998 5400 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11998 5400 []

theorem l8OMr_red_sm5402 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5402 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5400)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5401) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 335 l8OMrSmNormLinear
    5400 5401 5402 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5400 5401 5402 []

theorem l8OMr_red_pm5402 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5402 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5400)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5401) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 760 l8OMrPmNormLinear1
    5400 5401 5402 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5400 5401 5402 []

theorem l8OMr_red_pm9152 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9152 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5402) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 766 l8OMrPmChunk0
    5402 9152 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5402 9152 0

theorem l8OMr_red_pm9153 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9153 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5402) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 767 l8OMrPmChunk1
    5402 9153 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5402 9153 0

private def l8OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l8OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l8OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l8OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l8OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l8OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l8OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l8OMr_red_sm5403 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5402).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5403 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5402) 8 64).1 :=
  l8OMr_red_topk_probs sm_goal_1 initSM 339 l8OMrSmTopk 0 5402 5403 5404 5405
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l8OMr_red_pm9154 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9152).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9154 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9152) 8 64).1 :=
  l8OMr_red_topk_probs pm_goal_1 initPM 771 l8OMrPmTopk0 0 9152 9154 9156 9158
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l8OMr_red_pm9155 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9153).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9155 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9153) 8 64).1 :=
  l8OMr_red_topk_probs pm_goal_1 initPM 772 l8OMrPmTopk1 1 9153 9155 9157 9159
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l8OMr_red_sm5404 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5402).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5404 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5402) 8 64).2.1 :=
  l8OMr_red_topk_map sm_goal_1 initSM 339 l8OMrSmTopk 0 5402 5403 5404 5405
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l8OMr_red_pm9156 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9152).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9156 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9152) 8 64).2.1 :=
  l8OMr_red_topk_map pm_goal_1 initPM 771 l8OMrPmTopk0 0 9152 9154 9156 9158
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l8OMr_red_pm9157 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9153).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9157 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9153) 8 64).2.1 :=
  l8OMr_red_topk_map pm_goal_1 initPM 772 l8OMrPmTopk1 1 9153 9155 9157 9159
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l8OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5401 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5401 ∉ n.outs) := by
  native_decide

theorem l8OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5401 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5401 := by
  have hi := (hInit initGoal_5401 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5401 pm_goal_1.numRanks _ rfl,
    show initGoal_5401.tps = [{rank := 0, tid := 5401}] from rfl,
    show initGoal_5401.ts = 5401 from rfl,
    show initGoal_5401.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5401 (by native_decide) l8OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5401 (by native_decide) l8OMr_weight_not_written.2]
  exact hi

theorem l8OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5401).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5401 (by native_decide) l8OMr_weight_not_written.2]
  exact hPM 5401 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l8OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5399],
    outs := [8192, 8196, 8200, 8204, 8208], params := [5] }
private def l8OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9144],
    outs := [15360, 13418, 13428, 13442, 13454], params := [5] }
private def l8OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9145],
    outs := [15362, 13419, 13429, 13443, 13455], params := [5] }
private def l8OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8200], outs := [5409],
    params := [4096, 1024] }
private def l8OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13428], outs := [9166],
    params := [2048, 1024] }
private def l8OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13429], outs := [9167],
    params := [2048, 1024] }
private def l8OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5409, 5410],
    outs := [5411] }
private def l8OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9166, 5410],
    outs := [9170] }
private def l8OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9167, 5410],
    outs := [9171] }
private def l8OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5411], outs := [5412],
    params := [4096, 1] }
private def l8OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9170], outs := [9172],
    params := [2048, 1] }
private def l8OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9171], outs := [9173],
    params := [2048, 1] }
private def l8OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5412], outs := [5413] }
private def l8OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9172], outs := [9174] }
private def l8OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9173], outs := [9175] }

theorem l8OMrg_red_sm8200 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8200 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5399 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 330 l8OMrgSmRef
    5399 8200 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5399 [8192, 8196, 8200, 8204, 8208]
    5 rfl 8200 (by decide)

theorem l8OMrg_red_pm13428 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13428 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9144 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 739 l8OMrgPmRef0
    9144 13428 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9144
    [15360, 13418, 13428, 13442, 13454] 5 rfl 13428 (by decide)

theorem l8OMrg_red_pm13429 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13429 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9145 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 740 l8OMrgPmRef1
    9145 13429 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9145
    [15362, 13419, 13429, 13443, 13455] 5 rfl 13429 (by decide)

theorem l8OMrg_red_sm5409 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5409 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8200) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 332 l8OMrgSmReshape
    8200 5409 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8200 5409 [4096, 1024]

theorem l8OMrg_red_pm9166 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9166 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13428) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 741 l8OMrgPmReshape0
    13428 9166 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13428 9166 [2048, 1024]

theorem l8OMrg_red_pm9167 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9167 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13429) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 745 l8OMrgPmReshape1
    13429 9167 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13429 9167 [2048, 1024]

theorem l8OMrg_red_sm5411 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5411 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5409)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5410) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 336 l8OMrgSmLinear
    5409 5410 5411 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5409 5410 5411

theorem l8OMrg_red_pm9170 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9170 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9166)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5410) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 748 l8OMrgPmLinear0
    9166 5410 9170 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9166 5410 9170

theorem l8OMrg_red_pm9171 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9171 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9167)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5410) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 753 l8OMrgPmLinear1
    9167 5410 9171 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9167 5410 9171

theorem l8OMrg_red_sm5412 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5412 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5411) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 340 l8OMrgSmView
    5411 5412 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5411 5412

theorem l8OMrg_red_pm9172 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9172 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9170) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 756 l8OMrgPmView0
    9170 9172 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9170 9172

theorem l8OMrg_red_pm9173 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9173 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9171) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 761 l8OMrgPmView1
    9171 9173 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9171 9173

theorem l8OMrg_red_sm5413 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5413 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5412) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 344 l8OMrgSmSigmoid
    5412 5413 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5412 5413

theorem l8OMrg_red_pm9174 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9174 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9172) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 764 l8OMrgPmSigmoid0
    9172 9174 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9172 9174

theorem l8OMrg_red_pm9175 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9175 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9173) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 768 l8OMrgPmSigmoid1
    9173 9175 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l8OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9173 9175

theorem l8OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5410 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5410 ∉ n.outs) := by
  native_decide

theorem l8OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5410 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5410 := by
  have hi := (hInit initGoal_5410 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5410 pm_goal_1.numRanks _ rfl,
    show initGoal_5410.tps = [{rank := 0, tid := 5410}] from rfl,
    show initGoal_5410.ts = 5410 from rfl,
    show initGoal_5410.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5410
      (by native_decide) l8OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5410
      (by native_decide) l8OMrg_weight_not_written.2]
  exact hi

theorem l8OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5410).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5410 = initPM 5410 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5410
      (by native_decide) l8OMrg_weight_not_written.2
  rw [e]
  exact hPM 5410 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
