/- Layout-neutral graph reductions and initialized-weight bridge for the canonical Goal 1 cache segment. -/
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

def cKVConSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5562],
    outs := [8337, 8341], params := [2] }
def cKVConPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9632],
    outs := [15806, 15810], params := [2] }
def cKVConPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9633],
    outs := [15814, 15818], params := [2] }
def cKVConSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8337, 5563], outs := [5564] }
def cKVConPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15806, 5563], outs := [9636] }
def cKVConPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15814, 5563], outs := [9637] }
def cKVConSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564],
    outs := [8348, 8352, 8356, 8360, 8364], params := [5] }
def cKVConPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636],
    outs := [15384, 13796, 13806, 13820, 13832], params := [5] }
def cKVConPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637],
    outs := [15386, 13797, 13807, 13821, 13833], params := [5] }

theorem cKVCon_red_sm8337 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8337 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5562 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 445 cKVConSmResidualRef
    5562 8337 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5562 [8337, 8341] 2 rfl 8337 (by decide)

theorem cKVCon_red_pm15806 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15806 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9632 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 987 cKVConPmResidualRef0
    9632 15806 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9632 [15806, 15810] 2 rfl 15806 (by decide)

theorem cKVCon_red_pm15814 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15814 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9633 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 988 cKVConPmResidualRef1
    9633 15814 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9633 [15814, 15818] 2 rfl 15814 (by decide)

theorem cKVCon_red_sm5564 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5564 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8337)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 446 cKVConSmRms
    8337 5563 5564 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold cKVConSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 8337 5563 5564

theorem cKVCon_red_pm9636 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9636 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15806)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 989 cKVConPmRms0
    15806 5563 9636 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold cKVConPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15806 5563 9636

theorem cKVCon_red_pm9637 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9637 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15814)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5563) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 990 cKVConPmRms1
    15814 5563 9637 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold cKVConPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15814 5563 9637

theorem cKVCon_red_sm8352 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8352 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 447 cKVConSmNormRef
    5564 8352 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364]
    5 rfl 8352 (by decide)

theorem cKVCon_red_pm13796 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13796 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 991 cKVConPmNormRef0
    9636 13796 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636
    [15384, 13796, 13806, 13820, 13832] 5 rfl 13796 (by decide)

theorem cKVCon_red_pm13797 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13797 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 992 cKVConPmNormRef1
    9637 13797 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637
    [15386, 13797, 13807, 13821, 13833] 5 rfl 13797 (by decide)

theorem cKVCon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5563 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5563 := by
  have h := hInit initGoal_5563 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5563 pm_goal_1.numRanks _ rfl,
    show initGoal_5563.tps = [{rank := 0, tid := 5563}] from rfl,
    show initGoal_5563.ts = 5563 from rfl,
    show initGoal_5563.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5563
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5563
      (by native_decide) (by native_decide)]
  exact hval

theorem cKVCon_red_sm8341 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8341 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5562 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 445 cKVConSmResidualRef
    5562 8341 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5562 [8337, 8341] 2 rfl 8341 (by decide)

theorem cKVCon_red_pm15810 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15810 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9632 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 987 cKVConPmResidualRef0
    9632 15810 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9632 [15806, 15810] 2 rfl 15810 (by decide)

theorem cKVCon_red_pm15818 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15818 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9633 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 988 cKVConPmResidualRef1
    9633 15818 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVConPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9633 [15814, 15818] 2 rfl 15818 (by decide)


/-! Router graph reductions. -/
theorem cKVCr_chunk_gather0 (x0 x1 : Tensor)
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

theorem cKVCr_chunk_gather1 (x0 x1 : Tensor)
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

private def cKVCrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564],
    outs := [8348, 8352, 8356, 8360, 8364], params := [5] }
private def cKVCrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636],
    outs := [15384, 13796, 13806, 13820, 13832], params := [5] }
private def cKVCrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637],
    outs := [15386, 13797, 13807, 13821, 13833], params := [5] }
private def cKVCrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8348], outs := [5565] }
private def cKVCrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15384, 15386],
    outs := [12094], params := [0] }
private def cKVCrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12094], outs := [5565] }
private def cKVCrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5565, 5566], outs := [5567] }
private def cKVCrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5565, 5566], outs := [5567] }
private def cKVCrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5567], outs := [9644], params := [0] }
private def cKVCrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5567], outs := [9645], params := [0] }
private def cKVCrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5567],
    outs := [5568, 5569, 5570], params := [8, 1] }
private def cKVCrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9644],
    outs := [9646, 9648, 9650], params := [8, 1] }
private def cKVCrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9645],
    outs := [9647, 9649, 9651], params := [8, 1] }

theorem cKVCr_red_sm8348 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8348 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 447 cKVCrSmRef
    5564 8348 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564
    [8348, 8352, 8356, 8360, 8364] 5 rfl 8348 (by decide)

theorem cKVCr_red_pm15384 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15384 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 991 cKVCrPmRef0
    9636 15384 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636
    [15384, 13796, 13806, 13820, 13832] 5 rfl 15384 (by decide)

theorem cKVCr_red_pm15386 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15386 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 992 cKVCrPmRef1
    9637 15386 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637
    [15386, 13797, 13807, 13821, 13833] 5 rfl 15386 (by decide)

theorem cKVCr_red_sm5565 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5565 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8348 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 448 cKVCrSmFloat
    8348 5565 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8348 5565 []

theorem cKVCr_red_pm12094 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12094 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15384,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15386] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 996 cKVCrPmGather
    15384 15386 12094 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15384, 15386] 12094 0]
  rfl

theorem cKVCr_red_pm5565 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5565 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12094 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1004 cKVCrPmFloat1
    12094 5565 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12094 5565 []

theorem cKVCr_red_sm5567 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5567 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5565)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5566) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 452 cKVCrSmNormLinear
    5565 5566 5567 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5565 5566 5567 []

theorem cKVCr_red_pm5567 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5567 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5565)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5566) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1012 cKVCrPmNormLinear1
    5565 5566 5567 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5565 5566 5567 []

theorem cKVCr_red_pm9644 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9644 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5567) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1018 cKVCrPmChunk0
    5567 9644 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5567 9644 0

theorem cKVCr_red_pm9645 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9645 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5567) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1019 cKVCrPmChunk1
    5567 9645 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5567 9645 0

private def cKVCrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem cKVCr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = cKVCrTopkNode rnk logits probs mapTid scores)
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
      unfold cKVCrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem cKVCr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = cKVCrTopkNode rnk logits probs mapTid scores)
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
      unfold cKVCrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem cKVCr_red_sm5568 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5567).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5568 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5567) 8 64).1 :=
  cKVCr_red_topk_probs sm_goal_1 initSM 456 cKVCrSmTopk 0 5567 5568 5569 5570
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem cKVCr_red_pm9646 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9644).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9646 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9644) 8 64).1 :=
  cKVCr_red_topk_probs pm_goal_1 initPM 1023 cKVCrPmTopk0 0 9644 9646 9648 9650
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem cKVCr_red_pm9647 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9645).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9647 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9645) 8 64).1 :=
  cKVCr_red_topk_probs pm_goal_1 initPM 1024 cKVCrPmTopk1 1 9645 9647 9649 9651
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem cKVCr_red_sm5569 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5567).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5569 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5567) 8 64).2.1 :=
  cKVCr_red_topk_map sm_goal_1 initSM 456 cKVCrSmTopk 0 5567 5568 5569 5570
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem cKVCr_red_pm9648 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9644).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9648 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9644) 8 64).2.1 :=
  cKVCr_red_topk_map pm_goal_1 initPM 1023 cKVCrPmTopk0 0 9644 9646 9648 9650
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem cKVCr_red_pm9649 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 9645).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9649 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 9645) 8 64).2.1 :=
  cKVCr_red_topk_map pm_goal_1 initPM 1024 cKVCrPmTopk1 1 9645 9647 9649 9651
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem cKVCr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5566 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5566 ∉ n.outs) := by
  native_decide

theorem cKVCr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5566 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5566 := by
  have hi := (hInit initGoal_5566 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5566 pm_goal_1.numRanks _ rfl,
    show initGoal_5566.tps = [{rank := 0, tid := 5566}] from rfl,
    show initGoal_5566.ts = 5566 from rfl,
    show initGoal_5566.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5566 (by native_decide) cKVCr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5566 (by native_decide) cKVCr_weight_not_written.2]
  exact hi

theorem cKVCr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5566).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5566 (by native_decide) cKVCr_weight_not_written.2]
  exact hPM 5566 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def cKVCrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5564],
    outs := [8348, 8352, 8356, 8360, 8364], params := [5] }
private def cKVCrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9636],
    outs := [15384, 13796, 13806, 13820, 13832], params := [5] }
private def cKVCrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9637],
    outs := [15386, 13797, 13807, 13821, 13833], params := [5] }
private def cKVCrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8356], outs := [5574],
    params := [4096, 1024] }
private def cKVCrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [13806], outs := [9658],
    params := [2048, 1024] }
private def cKVCrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [13807], outs := [9659],
    params := [2048, 1024] }
private def cKVCrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5574, 5575],
    outs := [5576] }
private def cKVCrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9658, 5575],
    outs := [9662] }
private def cKVCrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9659, 5575],
    outs := [9663] }
private def cKVCrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5576], outs := [5577],
    params := [4096, 1] }
private def cKVCrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [9662], outs := [9664],
    params := [2048, 1] }
private def cKVCrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [9663], outs := [9665],
    params := [2048, 1] }
private def cKVCrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5577], outs := [5578] }
private def cKVCrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [9664], outs := [9666] }
private def cKVCrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [9665], outs := [9667] }

theorem cKVCrg_red_sm8356 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8356 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5564 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 447 cKVCrgSmRef
    5564 8356 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5564 [8348, 8352, 8356, 8360, 8364]
    5 rfl 8356 (by decide)

theorem cKVCrg_red_pm13806 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13806 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9636 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 991 cKVCrgPmRef0
    9636 13806 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9636
    [15384, 13796, 13806, 13820, 13832] 5 rfl 13806 (by decide)

theorem cKVCrg_red_pm13807 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 13807 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9637 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 992 cKVCrgPmRef1
    9637 13807 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9637
    [15386, 13797, 13807, 13821, 13833] 5 rfl 13807 (by decide)

theorem cKVCrg_red_sm5574 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5574 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 8356) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 449 cKVCrgSmReshape
    8356 5574 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8356 5574 [4096, 1024]

theorem cKVCrg_red_pm9658 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9658 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13806) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 993 cKVCrgPmReshape0
    13806 9658 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 13806 9658 [2048, 1024]

theorem cKVCrg_red_pm9659 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9659 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 13807) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 997 cKVCrgPmReshape1
    13807 9659 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 13807 9659 [2048, 1024]

theorem cKVCrg_red_sm5576 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5576 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5574)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5575) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 453 cKVCrgSmLinear
    5574 5575 5576 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5574 5575 5576

theorem cKVCrg_red_pm9662 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9662 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9658)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5575) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1000 cKVCrgPmLinear0
    9658 5575 9662 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 9658 5575 9662

theorem cKVCrg_red_pm9663 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9663 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9659)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5575) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1005 cKVCrgPmLinear1
    9659 5575 9663 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 9659 5575 9663

theorem cKVCrg_red_sm5577 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5577 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5576) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 457 cKVCrgSmView
    5576 5577 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5576 5577

theorem cKVCrg_red_pm9664 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9664 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9662) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1008 cKVCrgPmView0
    9662 9664 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 9662 9664

theorem cKVCrg_red_pm9665 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9665 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 9663) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1013 cKVCrgPmView1
    9663 9665 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 9663 9665

theorem cKVCrg_red_sm5578 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5578 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5577) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 461 cKVCrgSmSigmoid
    5577 5578 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5577 5578

theorem cKVCrg_red_pm9666 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9666 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9664) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1016 cKVCrgPmSigmoid0
    9664 9666 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 9664 9666

theorem cKVCrg_red_pm9667 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9667 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 9665) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1020 cKVCrgPmSigmoid1
    9665 9667 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cKVCrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 9665 9667

theorem cKVCrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5575 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5575 ∉ n.outs) := by
  native_decide

theorem cKVCrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5575 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5575 := by
  have hi := (hInit initGoal_5575 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5575 pm_goal_1.numRanks _ rfl,
    show initGoal_5575.tps = [{rank := 0, tid := 5575}] from rfl,
    show initGoal_5575.ts = 5575 from rfl,
    show initGoal_5575.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5575
      (by native_decide) cKVCrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5575
      (by native_decide) cKVCrg_weight_not_written.2]
  exact hi

theorem cKVCrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5575).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5575 = initPM 5575 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5575
      (by native_decide) cKVCrg_weight_not_written.2
  rw [e]
  exact hPM 5575 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
