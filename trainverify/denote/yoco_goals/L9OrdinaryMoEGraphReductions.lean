/- Layout-neutral graph reductions and initialized-weight bridge for the L9 ordinary MoE segment. -/
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

def l9OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5452],
    outs := [8233, 8237], params := [2] }
def l9OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9304],
    outs := [15742, 15746], params := [2] }
def l9OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9305],
    outs := [15750, 15754], params := [2] }
def l9OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8233, 5453], outs := [5454] }
def l9OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15742, 5453], outs := [9308] }
def l9OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15750, 5453], outs := [9309] }
def l9OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5454],
    outs := [8244, 8248, 8252, 8256, 8260], params := [5] }
def l9OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9308],
    outs := [15368, 13544, 13554, 13568, 13580], params := [5] }
def l9OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9309],
    outs := [15370, 13545, 13555, 13569, 13581], params := [5] }

theorem l9OMon_red_sm8233 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8233 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5452 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 367 l9OMonSmResidualRef
    5452 8233 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5452 [8233, 8237] 2 rfl 8233 (by decide)

theorem l9OMon_red_pm15742 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15742 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9304 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 819 l9OMonPmResidualRef0
    9304 15742 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9304 [15742, 15746] 2 rfl 15742 (by decide)

theorem l9OMon_red_pm15750 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15750 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9305 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 820 l9OMonPmResidualRef1
    9305 15750 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9305 [15750, 15754] 2 rfl 15750 (by decide)

theorem l9OMon_red_sm5454 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5454 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8233)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5453) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 368 l9OMonSmRms
    8233 5453 5454 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l9OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8233 5453 5454

theorem l9OMon_red_pm9308 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9308 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15742)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5453) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 821 l9OMonPmRms0
    15742 5453 9308 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l9OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15742 5453 9308

theorem l9OMon_red_pm9309 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9309 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15750)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5453) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 822 l9OMonPmRms1
    15750 5453 9309 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l9OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15750 5453 9309

theorem l9OMon_red_sm8248 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8248 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 369 l9OMonSmNormRef
    5454 8248 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5454 [8244, 8248, 8252, 8256, 8260]
    5 rfl 8248 (by decide)

theorem l9OMon_red_pm13544 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13544 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9308 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 823 l9OMonPmNormRef0
    9308 13544 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9308
    [15368, 13544, 13554, 13568, 13580] 5 rfl 13544 (by decide)

theorem l9OMon_red_pm13545 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13545 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9309 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 824 l9OMonPmNormRef1
    9309 13545 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9309
    [15370, 13545, 13555, 13569, 13581] 5 rfl 13545 (by decide)

theorem l9OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5453 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5453 := by
  have h := hInit initGoal_5453 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5453 pm_goal_1.numRanks _ rfl,
    show initGoal_5453.tps = [{rank := 0, tid := 5453}] from rfl,
    show initGoal_5453.ts = 5453 from rfl,
    show initGoal_5453.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5453
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5453
      (by native_decide) (by native_decide)]
  exact hval

theorem l9OMon_red_sm8237 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8237 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5452 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 367 l9OMonSmResidualRef
    5452 8237 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5452 [8233, 8237] 2 rfl 8237 (by decide)

theorem l9OMon_red_pm15746 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15746 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9304 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 819 l9OMonPmResidualRef0
    9304 15746 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9304 [15742, 15746] 2 rfl 15746 (by decide)

theorem l9OMon_red_pm15754 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15754 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9305 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 820 l9OMonPmResidualRef1
    9305 15754 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9305 [15750, 15754] 2 rfl 15754 (by decide)


/-! Router graph reductions. -/
theorem l9OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l9OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l9OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5454],
    outs := [8244, 8248, 8252, 8256, 8260], params := [5] }
private def l9OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9308],
    outs := [15368, 13544, 13554, 13568, 13580], params := [5] }
private def l9OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9309],
    outs := [15370, 13545, 13555, 13569, 13581], params := [5] }
private def l9OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8244], outs := [5455] }
private def l9OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15368, 15370],
    outs := [12030], params := [0] }
private def l9OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12030], outs := [5455] }
private def l9OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5455, 5456], outs := [5457] }
private def l9OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5455, 5456], outs := [5457] }
private def l9OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5457], outs := [9316], params := [0] }
private def l9OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5457], outs := [9317], params := [0] }
private def l9OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5457],
    outs := [5458, 5459, 5460], params := [8, 1] }
private def l9OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9316],
    outs := [9318, 9320, 9322], params := [8, 1] }
private def l9OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9317],
    outs := [9319, 9321, 9323], params := [8, 1] }

theorem l9OMr_red_sm8244 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8244 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 369 l9OMrSmRef
    5454 8244 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5454
    [8244, 8248, 8252, 8256, 8260] 5 rfl 8244 (by decide)

theorem l9OMr_red_pm15368 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15368 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9308 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 823 l9OMrPmRef0
    9308 15368 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9308
    [15368, 13544, 13554, 13568, 13580] 5 rfl 15368 (by decide)

theorem l9OMr_red_pm15370 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15370 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9309 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 824 l9OMrPmRef1
    9309 15370 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9309
    [15370, 13545, 13555, 13569, 13581] 5 rfl 15370 (by decide)

theorem l9OMr_red_sm5455 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5455 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8244 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 370 l9OMrSmFloat
    8244 5455 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8244 5455 []

theorem l9OMr_red_pm12030 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12030 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15368,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15370] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 828 l9OMrPmGather
    15368 15370 12030 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15368, 15370] 12030 0]
  rfl

theorem l9OMr_red_pm5455 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5455 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12030 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 836 l9OMrPmFloat1
    12030 5455 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12030 5455 []

theorem l9OMr_red_sm5457 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5457 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5455)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5456) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 374 l9OMrSmNormLinear
    5455 5456 5457 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5455 5456 5457 []

theorem l9OMr_red_pm5457 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5457 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5455)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5456) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 844 l9OMrPmNormLinear1
    5455 5456 5457 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5455 5456 5457 []

theorem l9OMr_red_pm9316 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9316 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5457) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 850 l9OMrPmChunk0
    5457 9316 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5457 9316 0

theorem l9OMr_red_pm9317 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9317 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5457) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 851 l9OMrPmChunk1
    5457 9317 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5457 9317 0

private def l9OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l9OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l9OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l9OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l9OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l9OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l9OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l9OMr_red_sm5458 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5457).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5458 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5457) 8 64).1 :=
  l9OMr_red_topk_probs sm_goal_1 initSM 378 l9OMrSmTopk 0 5457 5458 5459 5460
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l9OMr_red_pm9318 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9316).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9318 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9316) 8 64).1 :=
  l9OMr_red_topk_probs pm_goal_1 initPM 855 l9OMrPmTopk0 0 9316 9318 9320 9322
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l9OMr_red_pm9319 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9317).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9319 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9317) 8 64).1 :=
  l9OMr_red_topk_probs pm_goal_1 initPM 856 l9OMrPmTopk1 1 9317 9319 9321 9323
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l9OMr_red_sm5459 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5457).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5459 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5457) 8 64).2.1 :=
  l9OMr_red_topk_map sm_goal_1 initSM 378 l9OMrSmTopk 0 5457 5458 5459 5460
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l9OMr_red_pm9320 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9316).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9320 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9316) 8 64).2.1 :=
  l9OMr_red_topk_map pm_goal_1 initPM 855 l9OMrPmTopk0 0 9316 9318 9320 9322
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l9OMr_red_pm9321 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9317).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9321 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9317) 8 64).2.1 :=
  l9OMr_red_topk_map pm_goal_1 initPM 856 l9OMrPmTopk1 1 9317 9319 9321 9323
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l9OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5456 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5456 ∉ n.outs) := by
  native_decide

theorem l9OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5456 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5456 := by
  have hi := (hInit initGoal_5456 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5456 pm_goal_1.numRanks _ rfl,
    show initGoal_5456.tps = [{rank := 0, tid := 5456}] from rfl,
    show initGoal_5456.ts = 5456 from rfl,
    show initGoal_5456.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5456 (by native_decide) l9OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5456 (by native_decide) l9OMr_weight_not_written.2]
  exact hi

theorem l9OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5456).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5456 (by native_decide) l9OMr_weight_not_written.2]
  exact hPM 5456 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l9OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5454],
    outs := [8244, 8248, 8252, 8256, 8260], params := [5] }
private def l9OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9308],
    outs := [15368, 13544, 13554, 13568, 13580], params := [5] }
private def l9OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9309],
    outs := [15370, 13545, 13555, 13569, 13581], params := [5] }
private def l9OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8252], outs := [5464],
    params := [4096, 1024] }
private def l9OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13554], outs := [9330],
    params := [2048, 1024] }
private def l9OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13555], outs := [9331],
    params := [2048, 1024] }
private def l9OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5464, 5465],
    outs := [5466] }
private def l9OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9330, 5465],
    outs := [9334] }
private def l9OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9331, 5465],
    outs := [9335] }
private def l9OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5466], outs := [5467],
    params := [4096, 1] }
private def l9OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9334], outs := [9336],
    params := [2048, 1] }
private def l9OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9335], outs := [9337],
    params := [2048, 1] }
private def l9OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5467], outs := [5468] }
private def l9OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9336], outs := [9338] }
private def l9OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9337], outs := [9339] }

theorem l9OMrg_red_sm8252 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8252 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5454 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 369 l9OMrgSmRef
    5454 8252 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5454 [8244, 8248, 8252, 8256, 8260]
    5 rfl 8252 (by decide)

theorem l9OMrg_red_pm13554 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13554 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9308 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 823 l9OMrgPmRef0
    9308 13554 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9308
    [15368, 13544, 13554, 13568, 13580] 5 rfl 13554 (by decide)

theorem l9OMrg_red_pm13555 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13555 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9309 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 824 l9OMrgPmRef1
    9309 13555 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9309
    [15370, 13545, 13555, 13569, 13581] 5 rfl 13555 (by decide)

theorem l9OMrg_red_sm5464 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5464 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8252) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 371 l9OMrgSmReshape
    8252 5464 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8252 5464 [4096, 1024]

theorem l9OMrg_red_pm9330 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9330 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13554) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 825 l9OMrgPmReshape0
    13554 9330 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13554 9330 [2048, 1024]

theorem l9OMrg_red_pm9331 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9331 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13555) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 829 l9OMrgPmReshape1
    13555 9331 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13555 9331 [2048, 1024]

theorem l9OMrg_red_sm5466 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5466 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5464)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5465) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 375 l9OMrgSmLinear
    5464 5465 5466 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5464 5465 5466

theorem l9OMrg_red_pm9334 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9334 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9330)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5465) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 832 l9OMrgPmLinear0
    9330 5465 9334 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9330 5465 9334

theorem l9OMrg_red_pm9335 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9335 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9331)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5465) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 837 l9OMrgPmLinear1
    9331 5465 9335 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9331 5465 9335

theorem l9OMrg_red_sm5467 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5467 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5466) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 379 l9OMrgSmView
    5466 5467 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5466 5467

theorem l9OMrg_red_pm9336 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9336 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9334) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 840 l9OMrgPmView0
    9334 9336 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9334 9336

theorem l9OMrg_red_pm9337 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9337 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9335) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 845 l9OMrgPmView1
    9335 9337 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9335 9337

theorem l9OMrg_red_sm5468 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5468 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5467) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 383 l9OMrgSmSigmoid
    5467 5468 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5467 5468

theorem l9OMrg_red_pm9338 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9338 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9336) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 848 l9OMrgPmSigmoid0
    9336 9338 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9336 9338

theorem l9OMrg_red_pm9339 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9339 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9337) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 852 l9OMrgPmSigmoid1
    9337 9339 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l9OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9337 9339

theorem l9OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5465 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5465 ∉ n.outs) := by
  native_decide

theorem l9OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5465 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5465 := by
  have hi := (hInit initGoal_5465 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5465 pm_goal_1.numRanks _ rfl,
    show initGoal_5465.tps = [{rank := 0, tid := 5465}] from rfl,
    show initGoal_5465.ts = 5465 from rfl,
    show initGoal_5465.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5465
      (by native_decide) l9OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5465
      (by native_decide) l9OMrg_weight_not_written.2]
  exact hi

theorem l9OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5465).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5465 = initPM 5465 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5465
      (by native_decide) l9OMrg_weight_not_written.2
  rw [e]
  exact hPM 5465 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
