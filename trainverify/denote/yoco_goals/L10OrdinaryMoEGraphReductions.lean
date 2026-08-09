/- Layout-neutral graph reductions and initialized-weight bridge for the L10 ordinary MoE segment. -/
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

def l10OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5507],
    outs := [8285, 8289], params := [2] }
def l10OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9468],
    outs := [15774, 15778], params := [2] }
def l10OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9469],
    outs := [15782, 15786], params := [2] }
def l10OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8285, 5508], outs := [5509] }
def l10OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15774, 5508], outs := [9472] }
def l10OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15782, 5508], outs := [9473] }
def l10OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5509],
    outs := [8296, 8300, 8304, 8308, 8312], params := [5] }
def l10OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9472],
    outs := [15376, 13670, 13680, 13694, 13706], params := [5] }
def l10OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9473],
    outs := [15378, 13671, 13681, 13695, 13707], params := [5] }

theorem l10OMon_red_sm8285 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8285 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5507 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 406 l10OMonSmResidualRef
    5507 8285 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5507 [8285, 8289] 2 rfl 8285 (by decide)

theorem l10OMon_red_pm15774 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15774 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9468 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 903 l10OMonPmResidualRef0
    9468 15774 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9468 [15774, 15778] 2 rfl 15774 (by decide)

theorem l10OMon_red_pm15782 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15782 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9469 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 904 l10OMonPmResidualRef1
    9469 15782 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9469 [15782, 15786] 2 rfl 15782 (by decide)

theorem l10OMon_red_sm5509 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5509 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8285)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5508) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 407 l10OMonSmRms
    8285 5508 5509 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l10OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8285 5508 5509

theorem l10OMon_red_pm9472 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9472 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15774)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5508) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 905 l10OMonPmRms0
    15774 5508 9472 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l10OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15774 5508 9472

theorem l10OMon_red_pm9473 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9473 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15782)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5508) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 906 l10OMonPmRms1
    15782 5508 9473 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l10OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15782 5508 9473

theorem l10OMon_red_sm8300 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8300 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5509 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 408 l10OMonSmNormRef
    5509 8300 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5509 [8296, 8300, 8304, 8308, 8312]
    5 rfl 8300 (by decide)

theorem l10OMon_red_pm13670 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13670 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9472 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 907 l10OMonPmNormRef0
    9472 13670 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9472
    [15376, 13670, 13680, 13694, 13706] 5 rfl 13670 (by decide)

theorem l10OMon_red_pm13671 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13671 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9473 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 908 l10OMonPmNormRef1
    9473 13671 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9473
    [15378, 13671, 13681, 13695, 13707] 5 rfl 13671 (by decide)

theorem l10OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5508 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5508 := by
  have h := hInit initGoal_5508 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5508 pm_goal_1.numRanks _ rfl,
    show initGoal_5508.tps = [{rank := 0, tid := 5508}] from rfl,
    show initGoal_5508.ts = 5508 from rfl,
    show initGoal_5508.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5508
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5508
      (by native_decide) (by native_decide)]
  exact hval

theorem l10OMon_red_sm8289 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8289 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5507 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 406 l10OMonSmResidualRef
    5507 8289 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5507 [8285, 8289] 2 rfl 8289 (by decide)

theorem l10OMon_red_pm15778 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15778 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9468 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 903 l10OMonPmResidualRef0
    9468 15778 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9468 [15774, 15778] 2 rfl 15778 (by decide)

theorem l10OMon_red_pm15786 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15786 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9469 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 904 l10OMonPmResidualRef1
    9469 15786 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9469 [15782, 15786] 2 rfl 15786 (by decide)


/-! Router graph reductions. -/
theorem l10OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l10OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l10OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5509],
    outs := [8296, 8300, 8304, 8308, 8312], params := [5] }
private def l10OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9472],
    outs := [15376, 13670, 13680, 13694, 13706], params := [5] }
private def l10OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9473],
    outs := [15378, 13671, 13681, 13695, 13707], params := [5] }
private def l10OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8296], outs := [5510] }
private def l10OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15376, 15378],
    outs := [12062], params := [0] }
private def l10OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12062], outs := [5510] }
private def l10OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5510, 5511], outs := [5512] }
private def l10OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5510, 5511], outs := [5512] }
private def l10OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5512], outs := [9480], params := [0] }
private def l10OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5512], outs := [9481], params := [0] }
private def l10OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5512],
    outs := [5513, 5514, 5515], params := [8, 1] }
private def l10OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9480],
    outs := [9482, 9484, 9486], params := [8, 1] }
private def l10OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9481],
    outs := [9483, 9485, 9487], params := [8, 1] }

theorem l10OMr_red_sm8296 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8296 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5509 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 408 l10OMrSmRef
    5509 8296 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5509
    [8296, 8300, 8304, 8308, 8312] 5 rfl 8296 (by decide)

theorem l10OMr_red_pm15376 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15376 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9472 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 907 l10OMrPmRef0
    9472 15376 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9472
    [15376, 13670, 13680, 13694, 13706] 5 rfl 15376 (by decide)

theorem l10OMr_red_pm15378 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15378 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9473 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 908 l10OMrPmRef1
    9473 15378 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9473
    [15378, 13671, 13681, 13695, 13707] 5 rfl 15378 (by decide)

theorem l10OMr_red_sm5510 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5510 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8296 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 409 l10OMrSmFloat
    8296 5510 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8296 5510 []

theorem l10OMr_red_pm12062 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12062 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15376,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15378] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 912 l10OMrPmGather
    15376 15378 12062 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15376, 15378] 12062 0]
  rfl

theorem l10OMr_red_pm5510 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5510 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12062 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 920 l10OMrPmFloat1
    12062 5510 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12062 5510 []

theorem l10OMr_red_sm5512 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5512 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5510)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5511) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 413 l10OMrSmNormLinear
    5510 5511 5512 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5510 5511 5512 []

theorem l10OMr_red_pm5512 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5512 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5510)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5511) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 928 l10OMrPmNormLinear1
    5510 5511 5512 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5510 5511 5512 []

theorem l10OMr_red_pm9480 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9480 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5512) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 934 l10OMrPmChunk0
    5512 9480 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5512 9480 0

theorem l10OMr_red_pm9481 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9481 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5512) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 935 l10OMrPmChunk1
    5512 9481 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5512 9481 0

private def l10OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l10OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l10OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l10OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l10OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l10OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l10OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l10OMr_red_sm5513 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5512).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5513 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5512) 8 64).1 :=
  l10OMr_red_topk_probs sm_goal_1 initSM 417 l10OMrSmTopk 0 5512 5513 5514 5515
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l10OMr_red_pm9482 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9480).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9482 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9480) 8 64).1 :=
  l10OMr_red_topk_probs pm_goal_1 initPM 939 l10OMrPmTopk0 0 9480 9482 9484 9486
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l10OMr_red_pm9483 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9481).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9483 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9481) 8 64).1 :=
  l10OMr_red_topk_probs pm_goal_1 initPM 940 l10OMrPmTopk1 1 9481 9483 9485 9487
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l10OMr_red_sm5514 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5512).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5514 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5512) 8 64).2.1 :=
  l10OMr_red_topk_map sm_goal_1 initSM 417 l10OMrSmTopk 0 5512 5513 5514 5515
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l10OMr_red_pm9484 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9480).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9484 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9480) 8 64).2.1 :=
  l10OMr_red_topk_map pm_goal_1 initPM 939 l10OMrPmTopk0 0 9480 9482 9484 9486
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l10OMr_red_pm9485 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9481).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9485 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9481) 8 64).2.1 :=
  l10OMr_red_topk_map pm_goal_1 initPM 940 l10OMrPmTopk1 1 9481 9483 9485 9487
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l10OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5511 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5511 ∉ n.outs) := by
  native_decide

theorem l10OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5511 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5511 := by
  have hi := (hInit initGoal_5511 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5511 pm_goal_1.numRanks _ rfl,
    show initGoal_5511.tps = [{rank := 0, tid := 5511}] from rfl,
    show initGoal_5511.ts = 5511 from rfl,
    show initGoal_5511.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5511 (by native_decide) l10OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5511 (by native_decide) l10OMr_weight_not_written.2]
  exact hi

theorem l10OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5511).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5511 (by native_decide) l10OMr_weight_not_written.2]
  exact hPM 5511 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l10OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5509],
    outs := [8296, 8300, 8304, 8308, 8312], params := [5] }
private def l10OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9472],
    outs := [15376, 13670, 13680, 13694, 13706], params := [5] }
private def l10OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9473],
    outs := [15378, 13671, 13681, 13695, 13707], params := [5] }
private def l10OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8304], outs := [5519],
    params := [4096, 1024] }
private def l10OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13680], outs := [9494],
    params := [2048, 1024] }
private def l10OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13681], outs := [9495],
    params := [2048, 1024] }
private def l10OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5519, 5520],
    outs := [5521] }
private def l10OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9494, 5520],
    outs := [9498] }
private def l10OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9495, 5520],
    outs := [9499] }
private def l10OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5521], outs := [5522],
    params := [4096, 1] }
private def l10OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9498], outs := [9500],
    params := [2048, 1] }
private def l10OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9499], outs := [9501],
    params := [2048, 1] }
private def l10OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5522], outs := [5523] }
private def l10OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9500], outs := [9502] }
private def l10OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9501], outs := [9503] }

theorem l10OMrg_red_sm8304 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8304 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5509 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 408 l10OMrgSmRef
    5509 8304 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5509 [8296, 8300, 8304, 8308, 8312]
    5 rfl 8304 (by decide)

theorem l10OMrg_red_pm13680 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13680 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9472 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 907 l10OMrgPmRef0
    9472 13680 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9472
    [15376, 13670, 13680, 13694, 13706] 5 rfl 13680 (by decide)

theorem l10OMrg_red_pm13681 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13681 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9473 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 908 l10OMrgPmRef1
    9473 13681 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9473
    [15378, 13671, 13681, 13695, 13707] 5 rfl 13681 (by decide)

theorem l10OMrg_red_sm5519 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5519 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8304) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 410 l10OMrgSmReshape
    8304 5519 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8304 5519 [4096, 1024]

theorem l10OMrg_red_pm9494 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9494 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13680) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 909 l10OMrgPmReshape0
    13680 9494 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13680 9494 [2048, 1024]

theorem l10OMrg_red_pm9495 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9495 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13681) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 913 l10OMrgPmReshape1
    13681 9495 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13681 9495 [2048, 1024]

theorem l10OMrg_red_sm5521 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5521 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5519)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5520) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 414 l10OMrgSmLinear
    5519 5520 5521 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5519 5520 5521

theorem l10OMrg_red_pm9498 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9498 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9494)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5520) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 916 l10OMrgPmLinear0
    9494 5520 9498 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9494 5520 9498

theorem l10OMrg_red_pm9499 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9499 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9495)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5520) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 921 l10OMrgPmLinear1
    9495 5520 9499 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9495 5520 9499

theorem l10OMrg_red_sm5522 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5522 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5521) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 418 l10OMrgSmView
    5521 5522 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5521 5522

theorem l10OMrg_red_pm9500 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9500 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9498) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 924 l10OMrgPmView0
    9498 9500 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9498 9500

theorem l10OMrg_red_pm9501 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9501 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9499) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 929 l10OMrgPmView1
    9499 9501 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9499 9501

theorem l10OMrg_red_sm5523 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5523 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5522) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 422 l10OMrgSmSigmoid
    5522 5523 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5522 5523

theorem l10OMrg_red_pm9502 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9502 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9500) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 932 l10OMrgPmSigmoid0
    9500 9502 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9500 9502

theorem l10OMrg_red_pm9503 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9503 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9501) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 936 l10OMrgPmSigmoid1
    9501 9503 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l10OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9501 9503

theorem l10OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5520 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5520 ∉ n.outs) := by
  native_decide

theorem l10OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5520 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5520 := by
  have hi := (hInit initGoal_5520 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5520 pm_goal_1.numRanks _ rfl,
    show initGoal_5520.tps = [{rank := 0, tid := 5520}] from rfl,
    show initGoal_5520.ts = 5520 from rfl,
    show initGoal_5520.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5520
      (by native_decide) l10OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5520
      (by native_decide) l10OMrg_weight_not_written.2]
  exact hi

theorem l10OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5520).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5520 = initPM 5520 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5520
      (by native_decide) l10OMrg_weight_not_written.2
  rw [e]
  exact hPM 5520 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
