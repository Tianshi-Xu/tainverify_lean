/- Layout-neutral graph reductions and initialized-weight bridge for the L2 ordinary MoE segment. -/
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

def l2OMonSmResidualRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5067],
    outs := [7869, 7873], params := [2] }
def l2OMonPmResidualRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8156],
    outs := [15518, 15522], params := [2] }
def l2OMonPmResidualRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8157],
    outs := [15526, 15530], params := [2] }
def l2OMonSmRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [7869, 5068], outs := [5069] }
def l2OMonPmRms0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [15518, 5068], outs := [8160] }
def l2OMonPmRms1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [15526, 5068], outs := [8161] }
def l2OMonSmNormRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5069],
    outs := [7880, 7884, 7888, 7892, 7896], params := [5] }
def l2OMonPmNormRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8160],
    outs := [15312, 12662, 12672, 12686, 12698], params := [5] }
def l2OMonPmNormRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8161],
    outs := [15314, 12663, 12673, 12687, 12699], params := [5] }

theorem l2OMon_red_sm7869 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7869 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5067 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 94 l2OMonSmResidualRef
    5067 7869 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5067 [7869, 7873] 2 rfl 7869 (by decide)

theorem l2OMon_red_pm15518 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15518 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8156 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 231 l2OMonPmResidualRef0
    8156 15518 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8156 [15518, 15522] 2 rfl 15518 (by decide)

theorem l2OMon_red_pm15526 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15526 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8157 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 232 l2OMonPmResidualRef1
    8157 15526 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8157 [15526, 15530] 2 rfl 15526 (by decide)

theorem l2OMon_red_sm5069 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5069 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 7869)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5068) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 95 l2OMonSmRms
    7869 5068 5069 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l2OMonSmRms
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_1 s 0 7869 5068 5069

theorem l2OMon_red_pm8160 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8160 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15518)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5068) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 233 l2OMonPmRms0
    15518 5068 8160 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l2OMonPmRms0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 0 15518 5068 8160

theorem l2OMon_red_pm8161 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8161 =
      fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 15526)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5068) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 234 l2OMonPmRms1
    15526 5068 8161 fw_rms_norm (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  intro s
  unfold l2OMonPmRms1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_1 s 1 15526 5068 8161

theorem l2OMon_red_sm7884 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7884 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5069 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 96 l2OMonSmNormRef
    5069 7884 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonSmNormRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5069 [7880, 7884, 7888, 7892, 7896]
    5 rfl 7884 (by decide)

theorem l2OMon_red_pm12662 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12662 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8160 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 235 l2OMonPmNormRef0
    8160 12662 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonPmNormRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8160
    [15312, 12662, 12672, 12686, 12698] 5 rfl 12662 (by decide)

theorem l2OMon_red_pm12663 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12663 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8161 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 236 l2OMonPmNormRef1
    8161 12663 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonPmNormRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8161
    [15314, 12663, 12673, 12687, 12699] 5 rfl 12663 (by decide)

theorem l2OMon_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5068 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5068 := by
  have h := hInit initGoal_5068 (by native_decide)
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5068 pm_goal_1.numRanks _ rfl,
    show initGoal_5068.tps = [{rank := 0, tid := 5068}] from rfl,
    show initGoal_5068.ts = 5068 from rfl,
    show initGoal_5068.gatherDim = 0 from rfl] at hval
  simp only [List.map, reconstructWithDim] at hval
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5068
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5068
      (by native_decide) (by native_decide)]
  exact hval

theorem l2OMon_red_sm7873 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7873 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5067 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 94 l2OMonSmResidualRef
    5067 7873 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonSmResidualRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5067 [7869, 7873] 2 rfl 7873 (by decide)

theorem l2OMon_red_pm15522 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15522 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8156 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 231 l2OMonPmResidualRef0
    8156 15522 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonPmResidualRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8156 [15518, 15522] 2 rfl 15522 (by decide)

theorem l2OMon_red_pm15530 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15530 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8157 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 232 l2OMonPmResidualRef1
    8157 15530 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMonPmResidualRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8157 [15526, 15530] 2 rfl 15530 (by decide)


/-! Router graph reductions. -/
theorem l2OMr_chunk_gather0 (x0 x1 : Tensor)
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

theorem l2OMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l2OMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5069],
    outs := [7880, 7884, 7888, 7892, 7896], params := [5] }
private def l2OMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8160],
    outs := [15312, 12662, 12672, 12686, 12698], params := [5] }
private def l2OMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8161],
    outs := [15314, 12663, 12673, 12687, 12699], params := [5] }
private def l2OMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [7880], outs := [5070] }
private def l2OMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15312, 15314],
    outs := [11806], params := [0] }
private def l2OMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [11806], outs := [5070] }
private def l2OMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5070, 5071], outs := [5072] }
private def l2OMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5070, 5071], outs := [5072] }
private def l2OMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5072], outs := [8168], params := [0] }
private def l2OMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5072], outs := [8169], params := [0] }
private def l2OMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5072],
    outs := [5073, 5074, 5075], params := [8, 1] }
private def l2OMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8168],
    outs := [8170, 8172, 8174], params := [8, 1] }
private def l2OMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8169],
    outs := [8171, 8173, 8175], params := [8, 1] }

theorem l2OMr_red_sm7880 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7880 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5069 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 96 l2OMrSmRef
    5069 7880 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5069
    [7880, 7884, 7888, 7892, 7896] 5 rfl 7880 (by decide)

theorem l2OMr_red_pm15312 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15312 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8160 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 235 l2OMrPmRef0
    8160 15312 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8160
    [15312, 12662, 12672, 12686, 12698] 5 rfl 15312 (by decide)

theorem l2OMr_red_pm15314 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15314 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8161 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 236 l2OMrPmRef1
    8161 15314 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8161
    [15314, 12663, 12673, 12687, 12699] 5 rfl 15314 (by decide)

theorem l2OMr_red_sm5070 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5070 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 7880 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 97 l2OMrSmFloat
    7880 5070 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 7880 5070 []

theorem l2OMr_red_pm11806 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11806 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15312,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15314] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 240 l2OMrPmGather
    15312 15314 11806 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15312, 15314] 11806 0]
  rfl

theorem l2OMr_red_pm5070 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5070 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11806 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 248 l2OMrPmFloat1
    11806 5070 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 11806 5070 []

theorem l2OMr_red_sm5072 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5072 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5070)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5071) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 101 l2OMrSmNormLinear
    5070 5071 5072 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5070 5071 5072 []

theorem l2OMr_red_pm5072 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5072 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5070)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5071) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 256 l2OMrPmNormLinear1
    5070 5071 5072 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5070 5071 5072 []

theorem l2OMr_red_pm8168 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8168 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5072) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 262 l2OMrPmChunk0
    5072 8168 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5072 8168 0

theorem l2OMr_red_pm8169 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8169 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5072) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 263 l2OMrPmChunk1
    5072 8169 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5072 8169 0

private def l2OMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l2OMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l2OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l2OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l2OMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l2OMrTopkNode rnk logits probs mapTid scores)
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
      unfold l2OMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

theorem l2OMr_red_sm5073 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5072).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5073 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5072) 8 64).1 :=
  l2OMr_red_topk_probs sm_goal_1 initSM 105 l2OMrSmTopk 0 5072 5073 5074 5075
    (by native_decide) (by native_decide) rfl (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l2OMr_red_pm8170 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8168).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8170 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8168) 8 64).1 :=
  l2OMr_red_topk_probs pm_goal_1 initPM 267 l2OMrPmTopk0 0 8168 8170 8172 8174
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l2OMr_red_pm8171 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8169).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8171 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8169) 8 64).1 :=
  l2OMr_red_topk_probs pm_goal_1 initPM 268 l2OMrPmTopk1 1 8169 8171 8173 8175
    (by native_decide) (by native_decide) rfl (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l2OMr_red_sm5074 (initSM : Store)
    (hsh : (denoteGraphDistributedFaithful sm_goal_1 initSM 5072).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5074 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_1 initSM 5072) 8 64).2.1 :=
  l2OMr_red_topk_map sm_goal_1 initSM 105 l2OMrSmTopk 0 5072 5073 5074 5075
    (by native_decide) (by native_decide) rfl (by decide) (Or.inr hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l2OMr_red_pm8172 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8168).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8172 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8168) 8 64).2.1 :=
  l2OMr_red_topk_map pm_goal_1 initPM 267 l2OMrPmTopk0 0 8168 8170 8172 8174
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l2OMr_red_pm8173 (initPM : Store)
    (hsh : (denoteGraphDistributedFaithful pm_goal_1 initPM 8169).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8173 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_1 initPM 8169) 8 64).2.1 :=
  l2OMr_red_topk_map pm_goal_1 initPM 268 l2OMrPmTopk1 1 8169 8171 8173 8175
    (by native_decide) (by native_decide) rfl (by decide) (Or.inl hsh)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem l2OMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5071 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5071 ∉ n.outs) := by
  native_decide

theorem l2OMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5071 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5071 := by
  have hi := (hInit initGoal_5071 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5071 pm_goal_1.numRanks _ rfl,
    show initGoal_5071.tps = [{rank := 0, tid := 5071}] from rfl,
    show initGoal_5071.ts = 5071 from rfl,
    show initGoal_5071.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5071 (by native_decide) l2OMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5071 (by native_decide) l2OMr_weight_not_written.2]
  exact hi

theorem l2OMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5071).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5071 (by native_decide) l2OMr_weight_not_written.2]
  exact hPM 5071 [64, 1024] (by native_decide)



/-! Scalar-gate graph reductions. -/
private def l2OMrgSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5069],
    outs := [7880, 7884, 7888, 7892, 7896], params := [5] }
private def l2OMrgPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [8160],
    outs := [15312, 12662, 12672, 12686, 12698], params := [5] }
private def l2OMrgPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [8161],
    outs := [15314, 12663, 12673, 12687, 12699], params := [5] }
private def l2OMrgSmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [7888], outs := [5079],
    params := [4096, 1024] }
private def l2OMrgPmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [12672], outs := [8182],
    params := [2048, 1024] }
private def l2OMrgPmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [12673], outs := [8183],
    params := [2048, 1024] }
private def l2OMrgSmLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5079, 5080],
    outs := [5081] }
private def l2OMrgPmLinear0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8182, 5080],
    outs := [8186] }
private def l2OMrgPmLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8183, 5080],
    outs := [8187] }
private def l2OMrgSmView : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [5081], outs := [5082],
    params := [4096, 1] }
private def l2OMrgPmView0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [8186], outs := [8188],
    params := [2048, 1] }
private def l2OMrgPmView1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [8187], outs := [8189],
    params := [2048, 1] }
private def l2OMrgSmSigmoid : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [5082], outs := [5083] }
private def l2OMrgPmSigmoid0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sigmoid", ins := [8188], outs := [8190] }
private def l2OMrgPmSigmoid1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sigmoid", ins := [8189], outs := [8191] }

theorem l2OMrg_red_sm7888 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 7888 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5069 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 96 l2OMrgSmRef
    5069 7888 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5069 [7880, 7884, 7888, 7892, 7896]
    5 rfl 7888 (by decide)

theorem l2OMrg_red_pm12672 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12672 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8160 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 235 l2OMrgPmRef0
    8160 12672 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 8160
    [15312, 12662, 12672, 12686, 12698] 5 rfl 12672 (by decide)

theorem l2OMrg_red_pm12673 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12673 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 8161 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 236 l2OMrgPmRef1
    8161 12673 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 8161
    [15314, 12663, 12673, 12687, 12699] 5 rfl 12673 (by decide)

theorem l2OMrg_red_sm5079 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5079 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 initSM 7888) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 98 l2OMrgSmReshape
    7888 5079 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgSmReshape
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 7888 5079 [4096, 1024]

theorem l2OMrg_red_pm8182 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8182 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12672) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 237 l2OMrgPmReshape0
    12672 8182 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmReshape0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 12672 8182 [2048, 1024]

theorem l2OMrg_red_pm8183 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8183 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 initPM 12673) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 241 l2OMrgPmReshape1
    12673 8183 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmReshape1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 12673 8183 [2048, 1024]

theorem l2OMrg_red_sm5081 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5081 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5079)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5080) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 102 l2OMrgSmLinear
    5079 5080 5081 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgSmLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 5079 5080 5081

theorem l2OMrg_red_pm8186 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8186 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8182)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5080) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 244 l2OMrgPmLinear0
    8182 5080 8186 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmLinear0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 8182 5080 8186

theorem l2OMrg_red_pm8187 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8187 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 8183)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5080) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 249 l2OMrgPmLinear1
    8183 5080 8187 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 8183 5080 8187

theorem l2OMrg_red_sm5082 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5082 =
      fw_view [4096, 1] (denoteGraphDistributedFaithful sm_goal_1 initSM 5081) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 106 l2OMrgSmView
    5081 5082 (fun x => fw_view [4096, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgSmView
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1] 5081 5082

theorem l2OMrg_red_pm8188 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8188 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8186) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 252 l2OMrgPmView0
    8186 8188 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmView0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1] 8186 8188

theorem l2OMrg_red_pm8189 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8189 =
      fw_view [2048, 1] (denoteGraphDistributedFaithful pm_goal_1 initPM 8187) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 257 l2OMrgPmView1
    8187 8189 (fun x => fw_view [2048, 1] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmView1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1] 8187 8189

theorem l2OMrg_red_sm5083 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5083 =
      fw_sigmoid (denoteGraphDistributedFaithful sm_goal_1 initSM 5082) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 110 l2OMrgSmSigmoid
    5082 5083 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgSmSigmoid
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p sm_goal_1 s 0 5082 5083

theorem l2OMrg_red_pm8190 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8190 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8188) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 260 l2OMrgPmSigmoid0
    8188 8190 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmSigmoid0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 0 8188 8190

theorem l2OMrg_red_pm8191 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 8191 =
      fw_sigmoid (denoteGraphDistributedFaithful pm_goal_1 initPM 8189) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 264 l2OMrgPmSigmoid1
    8189 8191 fw_sigmoid
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l2OMrgPmSigmoid1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_sigmoid_out_1p pm_goal_1 s 1 8189 8191

theorem l2OMrg_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5080 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5080 ∉ n.outs) := by
  native_decide

theorem l2OMrg_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5080 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5080 := by
  have hi := (hInit initGoal_5080 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5080 pm_goal_1.numRanks _ rfl,
    show initGoal_5080.tps = [{rank := 0, tid := 5080}] from rfl,
    show initGoal_5080.ts = 5080 from rfl,
    show initGoal_5080.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 5080
      (by native_decide) l2OMrg_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5080
      (by native_decide) l2OMrg_weight_not_written.2]
  exact hi

theorem l2OMrg_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5080).shape = [1, 1024] := by
  have e : denoteGraphDistributedFaithful pm_goal_1 initPM 5080 = initPM 5080 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5080
      (by native_decide) l2OMrg_weight_not_written.2
  rw [e]
  exact hPM 5080 [1, 1024] (by native_decide)


end
end TrainVerify.Denote.GeneratedPatterns
