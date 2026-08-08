import denote.yoco_goals.Goal_1
import denote.Gather2Rel
import denote.InnerChunkCEShard
import denote.InnerChunkCELossShard

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def cSmCE : NodeDecl :=
  { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [6255, 6256, 4931],
    outs := [4926, 4927], params := [1024] }
private def cPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [4931], outs := [11714], params := [0] }
private def cPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [4931], outs := [11715], params := [0] }
private def cPmCE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11712, 6256, 11714],
    outs := [11716, 11718], params := [1024] }
private def cPmCE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11713, 6256, 11715],
    outs := [11717, 11719], params := [1024] }
private def cPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11716, 11717],
    outs := [4926], params := [0] }

private theorem csm_all_nonempty : ∀ n ∈ sm_goal_1.nodes, n.outs ≠ [] := by
  native_decide
private theorem cpm_all_nonempty : ∀ n ∈ pm_goal_1.nodes, n.outs ≠ [] := by
  native_decide
private theorem csm_nonempty (k : Nat) :
    ∀ n ∈ sm_goal_1.nodes.drop k, n.outs ≠ [] :=
  fun n hn => csm_all_nonempty n (List.mem_of_mem_drop hn)
private theorem cpm_nonempty (k : Nat) :
    ∀ n ∈ pm_goal_1.nodes.drop k, n.outs ≠ [] :=
  fun n hn => cpm_all_nonempty n (List.mem_of_mem_drop hn)

private theorem red_sm4926 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4926 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful sm_goal_1 initSM 6255)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6256)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4931)
        (((denoteGraphDistributedFaithful sm_goal_1 initSM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  refine denoteGraphDistributedFaithful_reduce3 sm_goal_1 initSM 924 cSmCE
    6255 6256 4931 4926
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
      ((0 : Nat) : Scalar)).fst)
    (by native_decide) (by native_decide) ?_
    (csm_nonempty 925) (by native_decide)
    (csm_nonempty 924) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cSmCE
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_fst_out_1p sm_goal_1 s 0 6255 6256 4931
    4926 4927 [1024]

private theorem red_pm11714 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11714 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 4931) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 13 cPmChunk0
    4931 11714 (fun y => chunkPrimDimN 0 2 0 y)
    (by native_decide) (by native_decide) ?_
    (cpm_nonempty 14) (by native_decide)
    (cpm_nonempty 13) (by native_decide)
  intro s
  unfold cPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 4931 11714 0

private theorem red_pm11715 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11715 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 4931) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 27 cPmChunk1
    4931 11715 (fun y => chunkPrimDimN 0 2 1 y)
    (by native_decide) (by native_decide) ?_
    (cpm_nonempty 28) (by native_decide)
    (cpm_nonempty 27) (by native_decide)
  intro s
  unfold cPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 4931 11715 0

private theorem red_pm11716 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11716 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_1 initPM 11712)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6256)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11714)
        (((denoteGraphDistributedFaithful pm_goal_1 initPM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_1 initPM 2020 cPmCE0
    11712 6256 11714 11716
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
      ((0 : Nat) : Scalar)).fst)
    (by native_decide) (by native_decide) ?_
    (cpm_nonempty 2021) (by native_decide)
    (cpm_nonempty 2020) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cPmCE0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_fst_out_1p pm_goal_1 s 0 11712 6256 11714
    11716 11718 [1024]

private theorem red_pm11717 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11717 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_1 initPM 11713)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6256)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11715)
        (((denoteGraphDistributedFaithful pm_goal_1 initPM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_1 initPM 2021 cPmCE1
    11713 6256 11715 11717
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
      ((0 : Nat) : Scalar)).fst)
    (by native_decide) (by native_decide) ?_
    (cpm_nonempty 2022) (by native_decide)
    (cpm_nonempty 2021) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cPmCE1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_fst_out_1p pm_goal_1 s 1 11713 6256 11715
    11717 11719 [1024]

private theorem red_pm4926 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 4926 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11716,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11717] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 2022 cPmGather
    11716 11717 4926 (fun a b => allGatherPrimDimN 0 2 0 [a, b])
    (by native_decide) (by native_decide) ?_
    (cpm_nonempty 2023) (by native_decide)
    (cpm_nonempty 2022) (by native_decide) (by native_decide)
  intro s
  unfold cPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [11716, 11717] 4926 0

private theorem canonical_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (tid : Tid) (g : LineageGoal) (hg : g ∈ initGoals)
    (htp : g.tps = [{rank := 0, tid := tid}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hs : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hp : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := (hInit g hg).2.2
  rw [reconstructForGoal_of_not_replicated g pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM tid
      (by native_decide) hs,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM tid
      (by native_decide) hp]
  exact hi

-- The concrete CE commute is isolated so its elaboration budget does not
-- accumulate with the final generated-goal reconstruction.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem canonical_goal_1_value_from_norm (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hnorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11713)
      [4096, 1024] [2048, 1024])
    (hlabels : ∀ l < 4096, scalarToNat (valAt (initPM 4931) l) < 154880) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4926 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 4926 := by
  have hw := canonical_input_eq initSM initPM hInit 6256 initGoal_6256
    (by native_decide) rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hy := canonical_input_eq initSM initPM hInit 4931 initGoal_4931
    (by native_decide) rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwy : (denoteGraphDistributedFaithful pm_goal_1 initPM 6256).shape =
      [154880, 1024] := by
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6256 (by native_decide) (by native_decide)]
    exact hPM 6256 [154880, 1024] (by native_decide)
  have hyy : (denoteGraphDistributedFaithful pm_goal_1 initPM 4931).shape = [4096] := by
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 4931 (by native_decide) (by native_decide)]
    exact hPM 4931 [4096] (by native_decide)
  have hvocab : ((denoteGraphDistributedFaithful pm_goal_1 initPM 6256).shape.head?).getD 0 =
      154880 := by rw [hwy]; rfl
  have hlabelDenote : ∀ l < 4096,
      scalarToNat (valAt (denoteGraphDistributedFaithful pm_goal_1 initPM 4931) l) < 154880 := by
    intro l hl
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 4931 (by native_decide) (by native_decide)]
    exact hlabels l hl
  have hval : denoteGraphDistributedFaithful sm_goal_1 initSM 4926 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 4926 := by
    rw [red_sm4926, red_pm4926, red_pm11716, red_pm11717, red_pm11714, red_pm11715,
      hw, hy, hnorm.value, hvocab]
    exact fw_inner_chunk_ce_fst_allGather0_commute_2_of
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11713)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6256)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 4931)
      2048 1024 154880 (by decide) (by decide) (by decide)
      hnorm.shard0_shape hnorm.shard1_shape hwy hyy hlabelDenote ((0 : Nat) : Scalar)
  exact hval

-- The generated graph reduction for the loss tensor is isolated from the final
-- `InitGoalHolds` record normalization for deterministic elaboration cost.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem canonical_goal_1_shape_from_norm (initSM initPM : Store)
    (hnorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11713)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM 4926).shape = [4096] := by
  calc
    _ = ((fw_inner_chunk_ce
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6255)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6256)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4931)
        (((denoteGraphDistributedFaithful sm_goal_1 initSM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).fst).shape := congrArg Tensor.shape (red_sm4926 initSM)
    _ = [4096] := fw_inner_chunk_ce_fst_shape _ _ _ _ _ 4096 (by
      rw [hnorm.full_shape]
      rfl)

-- Final reconstruction normalization expands the concrete generated goal record.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Canonical ancestry-closed CE head.  The sole upstream obligation is the
actual two-shard Gather relation at the output of the trailing RMSNorm. -/
theorem canonical_goal_1_from_norm (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hnorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11713)
      [4096, 1024] [2048, 1024])
    (hlabels : ∀ l < 4096, scalarToNat (valAt (initPM 4931) l) < 154880) :
    InitGoalHolds pm_goal_1.numRanks goal_1
      (denoteGraphDistributedFaithful sm_goal_1 initSM)
      (denoteGraphDistributedFaithful pm_goal_1 initPM) := by
  have hval := canonical_goal_1_value_from_norm initSM initPM hPM hInit hnorm hlabels
  have hsmShape := canonical_goal_1_shape_from_norm initSM initPM hnorm
  have hpmShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 4926).shape = [4096] := by
    rw [← hval]
    exact hsmShape
  change (denoteGraphDistributedFaithful sm_goal_1 initSM 4926).shape = [4096] ∧
    [(denoteGraphDistributedFaithful pm_goal_1 initPM 4926).shape] = [[4096]] ∧
    denoteGraphDistributedFaithful sm_goal_1 initSM 4926 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 4926
  exact ⟨hsmShape, congrArg (fun sh => [sh]) hpmShape, hval⟩

end
end TrainVerify.Denote.GeneratedPatterns
