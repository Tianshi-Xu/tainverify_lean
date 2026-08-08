import denote.yoco_goals.Goal_2_FaithfulHead
import denote.Gather2Rel
import denote.yoco_goals.ZigzagLayoutRel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def cSmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6247, 6252],
    outs := [6253], params := [1, 0] }
private def cSmNorm : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [6253, 6254], outs := [6255] }
private def cPmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11598, 6252],
    outs := [11606], params := [2, 0] }
private def cPmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11599, 6252],
    outs := [11607], params := [2, 1] }
private def cPmNorm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [11606, 6254], outs := [11712] }
private def cPmNorm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_rms_norm", ins := [11607, 6254], outs := [11713] }

private theorem sm_all_nonempty : ∀ n ∈ sm_goal_2.nodes, n.outs ≠ [] := by
  native_decide
private theorem pm_all_nonempty : ∀ n ∈ pm_goal_2.nodes, n.outs ≠ [] := by
  native_decide
private theorem sm_nonempty (k : Nat) : ∀ n ∈ sm_goal_2.nodes.drop k, n.outs ≠ [] :=
  fun n hn => sm_all_nonempty n (List.mem_of_mem_drop hn)
private theorem pm_nonempty (k : Nat) : ∀ n ∈ pm_goal_2.nodes.drop k, n.outs ≠ [] :=
  fun n hn => pm_all_nonempty n (List.mem_of_mem_drop hn)

private theorem sm_922_lt : 922 < sm_goal_2.nodes.length := by native_decide
private theorem sm_922_node : sm_goal_2.nodes[922]'sm_922_lt = cSmUnshuffle := by
  native_decide
private theorem sm_after_6253 : ∀ n ∈ sm_goal_2.nodes.drop 923, 6253 ∉ n.outs := by
  native_decide
private theorem sm_from_922_6247 : ∀ n ∈ sm_goal_2.nodes.drop 922, 6247 ∉ n.outs := by
  native_decide

private theorem red_sm6253 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_2 initSM 6253 =
      denoteGraphDistributedFaithful sm_goal_2 initSM 6247 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_2 initSM 922 cSmUnshuffle
    6247 6253 (fun x => x)
    sm_922_lt sm_922_node ?_
    (sm_nonempty 923) sm_after_6253
    (sm_nonempty 922) sm_from_922_6247
  intro s
  unfold cSmUnshuffle
  rw [applyNodeDistributedFaithful_unshuffle_out,
    applyNodeFaithfulUnshuffleValue_cpSize_one]
  · rfl
  · native_decide
  · decide
  · decide

private theorem red_pm11606 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 11606 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_2 initPM 11598,
         denoteGraphDistributedFaithful pm_goal_2 initPM 11599]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)) 2 0 := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_2 initPM 2016 cPmUnshuffle0
    11598 11599 6252 11606
    (fun x0 x1 cu => fw_maybe_unshuffle_collective [x0, x1] (decodeCuSeqlens cu) 2 0)
    (by native_decide) (by native_decide) ?_
    (pm_nonempty 2017) (by native_decide)
    (pm_nonempty 2016) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cPmUnshuffle0
  rw [applyNodeDistributedFaithful_unshuffle_out]
  unfold applyNodeFaithfulUnshuffleValue
  have hb : pm_goal_2.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11598, 6252],
        outs := [11606], params := [2, 0] } =
      [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11598, 6252],
         outs := [11606], params := [2, 0] },
       { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11599, 6252],
         outs := [11607], params := [2, 1] }] := by native_decide
  rw [hb]
  rfl

private theorem red_pm11607 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 11607 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_2 initPM 11598,
         denoteGraphDistributedFaithful pm_goal_2 initPM 11599]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)) 2 1 := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_2 initPM 2017 cPmUnshuffle1
    11598 11599 6252 11607
    (fun x0 x1 cu => fw_maybe_unshuffle_collective [x0, x1] (decodeCuSeqlens cu) 2 1)
    (by native_decide) (by native_decide) ?_
    (pm_nonempty 2018) (by native_decide)
    (pm_nonempty 2017) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cPmUnshuffle1
  rw [applyNodeDistributedFaithful_unshuffle_out]
  unfold applyNodeFaithfulUnshuffleValue
  have hb : pm_goal_2.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11599, 6252],
        outs := [11607], params := [2, 1] } =
      [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11598, 6252],
         outs := [11606], params := [2, 0] },
       { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11599, 6252],
         outs := [11607], params := [2, 1] }] := by native_decide
  rw [hb]
  rfl

private theorem red_sm6255 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_2 initSM 6255 =
      fw_rms_norm
        (denoteGraphDistributedFaithful sm_goal_2 initSM 6253)
        (denoteGraphDistributedFaithful sm_goal_2 initSM 6254) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_2 initSM 923 cSmNorm
    6253 6254 6255 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (sm_nonempty 924) (by native_decide)
    (sm_nonempty 923) (by native_decide) (by native_decide)
  intro s
  unfold cSmNorm
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p sm_goal_2 s 0 6253 6254 6255

private theorem red_pm11712 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 11712 =
      fw_rms_norm
        (denoteGraphDistributedFaithful pm_goal_2 initPM 11606)
        (denoteGraphDistributedFaithful pm_goal_2 initPM 6254) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_2 initPM 2018 cPmNorm0
    11606 6254 11712 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (pm_nonempty 2019) (by native_decide)
    (pm_nonempty 2018) (by native_decide) (by native_decide)
  intro s
  unfold cPmNorm0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_2 s 0 11606 6254 11712

private theorem red_pm11713 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 11713 =
      fw_rms_norm
        (denoteGraphDistributedFaithful pm_goal_2 initPM 11607)
        (denoteGraphDistributedFaithful pm_goal_2 initPM 6254) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_2 initPM 2019 cPmNorm1
    11607 6254 11713 fw_rms_norm
    (by native_decide) (by native_decide) ?_
    (pm_nonempty 2020) (by native_decide)
    (pm_nonempty 2019) (by native_decide) (by native_decide)
  intro s
  unfold cPmNorm1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_rms_norm_out_1p pm_goal_2 s 1 11607 6254 11713

private theorem canonical_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_2.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_2 initSM 6254 =
      denoteGraphDistributedFaithful pm_goal_2 initPM 6254 := by
  have hi := (hInit initGoal_6254 (by native_decide)).2.2
  simp only [initGoal_6254, reconstructForGoal, Bool.false_eq_true, if_false,
    List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_2 sm_goal_2.nodes initSM 6254
      (by native_decide) (by native_decide),
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_2 pm_goal_2.nodes initPM 6254
      (by native_decide) (by native_decide)]
  exact hi

private theorem canonical_final_unshuffle_value (initSM initPM : Store)
    (hpre : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252) = [0, 4096]) :
    denoteGraphDistributedFaithful sm_goal_2 initSM 6253 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_2 initPM 11606,
         denoteGraphDistributedFaithful pm_goal_2 initPM 11607] := by
  calc
    denoteGraphDistributedFaithful sm_goal_2 initSM 6253
          = denoteGraphDistributedFaithful sm_goal_2 initSM 6247 := red_sm6253 initSM
    _ = allGatherPrimDimN 0 2 0
          [fw_maybe_unshuffle_collective
              [denoteGraphDistributedFaithful pm_goal_2 initPM 11598,
               denoteGraphDistributedFaithful pm_goal_2 initPM 11599]
              (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)) 2 0,
           fw_maybe_unshuffle_collective
              [denoteGraphDistributedFaithful pm_goal_2 initPM 11598,
               denoteGraphDistributedFaithful pm_goal_2 initPM 11599]
              (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)) 2 1] :=
            Zigzag2Rel.unshuffle_gather_single 2048 [1024] hpre
              (by omega) (by decide) rfl hdecoded
    _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_2 initPM 11606,
             denoteGraphDistributedFaithful pm_goal_2 initPM 11607] :=
            congrArg (allGatherPrimDimN 0 2 0)
              (congrArg₂ List.cons (red_pm11606 initPM).symm
                (congrArg (List.cons · []) (red_pm11607 initPM).symm))

private theorem canonical_final_unshuffle_full_shape (initSM initPM : Store)
    (hpre : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful sm_goal_2 initSM 6253).shape = [4096, 1024] :=
  (congrArg Tensor.shape (red_sm6253 initSM)).trans hpre.full_shape

private theorem canonical_final_unshuffle_rank0_shape (initSM initPM : Store)
    (hpre : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful pm_goal_2 initPM 11606).shape = [2048, 1024] := by
  rw [red_pm11606, fw_maybe_unshuffle_collective_shape]
  simp only [List.getD_cons_zero]
  rcases hpre with ⟨_, _, hs⟩
  exact hs.rank0_shape

private theorem canonical_final_unshuffle_rank1_shape (initSM initPM : Store)
    (hpre : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful pm_goal_2 initPM 11607).shape = [2048, 1024] := by
  rw [red_pm11607, fw_maybe_unshuffle_collective_shape]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rcases hpre with ⟨_, _, hs⟩
  exact hs.rank1_shape

private theorem canonical_cu_not_written :
    ∀ n ∈ pm_goal_2.nodes, (6252 : Tid) ∉ n.outs := by
  native_decide

private theorem canonical_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 6252 = initPM 6252 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written
    pm_goal_2 pm_goal_2.nodes initPM 6252
      (by native_decide) canonical_cu_not_written

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The concrete canonical final faithful unshuffle.  Its input is the zigzag
relation produced by L23; the decoded packed-sequence fact turns the paired PM
collective outputs back into ordinary rank-order shards. -/
theorem canonical_final_unshuffle (initSM initPM : Store)
    (hpre : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252) = [0, 4096]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6253)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11606)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11607)
      [4096, 1024] [2048, 1024] :=
  ⟨canonical_final_unshuffle_value initSM initPM hpre hdecoded,
   canonical_final_unshuffle_full_shape initSM initPM hpre,
   canonical_final_unshuffle_rank0_shape initSM initPM hpre,
   canonical_final_unshuffle_rank1_shape initSM initPM hpre,
   by decide⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Canonical shared loss-backbone tail: graph nodes 922--923 on SM and
2016--2019 on PM, with concrete tids through the final RMSNorm output. -/
theorem canonical_loss_backbone_tail_goal_2 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_2.numRanks initGoals initSM initPM)
    (hpre : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
      [4096, 1024] [2048, 1024] := by
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252) = [0, 4096] := by
    exact (congrArg decodeCuSeqlens (canonical_cu_input initPM)).trans
      hPacked.decoded_single
  have hu := canonical_final_unshuffle initSM initPM hpre hdecoded
  have hw := canonical_weight_eq initSM initPM hInit
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · calc
      denoteGraphDistributedFaithful sm_goal_2 initSM 6255
          = fw_rms_norm
              (denoteGraphDistributedFaithful sm_goal_2 initSM 6253)
              (denoteGraphDistributedFaithful sm_goal_2 initSM 6254) := red_sm6255 initSM
      _ = allGatherPrimDimN 0 2 0
            [fw_rms_norm (denoteGraphDistributedFaithful pm_goal_2 initPM 11606)
              (denoteGraphDistributedFaithful pm_goal_2 initPM 6254),
             fw_rms_norm (denoteGraphDistributedFaithful pm_goal_2 initPM 11607)
              (denoteGraphDistributedFaithful pm_goal_2 initPM 6254)] := by
            rw [hu.value, hw]
            exact fw_rms_norm_allGather0_commute_2_core _ _ _ 2048 1024
              (by omega) (by omega) hu.shard0_shape hu.shard1_shape
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_2 initPM 11712,
             denoteGraphDistributedFaithful pm_goal_2 initPM 11713] := by
            rw [red_pm11712, red_pm11713]
  · calc
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6255).shape
          = (fw_rms_norm
              (denoteGraphDistributedFaithful sm_goal_2 initSM 6253)
              (denoteGraphDistributedFaithful sm_goal_2 initSM 6254)).shape :=
            congrArg Tensor.shape (red_sm6255 initSM)
      _ = [4096, 1024] := by
            unfold fw_rms_norm
            rw [hu.full_shape]
            rfl
  · calc
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11712).shape
          = (fw_rms_norm
              (denoteGraphDistributedFaithful pm_goal_2 initPM 11606)
              (denoteGraphDistributedFaithful pm_goal_2 initPM 6254)).shape :=
            congrArg Tensor.shape (red_pm11712 initPM)
      _ = [2048, 1024] := by
            unfold fw_rms_norm
            rw [hu.shard0_shape]
            rfl
  · calc
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11713).shape
          = (fw_rms_norm
              (denoteGraphDistributedFaithful pm_goal_2 initPM 11607)
              (denoteGraphDistributedFaithful pm_goal_2 initPM 6254)).shape :=
            congrArg Tensor.shape (red_pm11713 initPM)
      _ = [2048, 1024] := by
            unfold fw_rms_norm
            rw [hu.shard1_shape]
            rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Goal 2 closure from its own faithful graph: the shared L23 zigzag relation
feeds the concrete Goal 2 unshuffle/RMSNorm tail and then the canonical CE head. -/
theorem canonical_goal_2_from_zigzag (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_2InitEnv)
    (hInit : InitGoalsHold pm_goal_2.numRanks initGoals initSM initPM)
    (hpre : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6247)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11598)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11599)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2) :
    InitGoalHolds pm_goal_2.numRanks goal_2
      (denoteGraphDistributedFaithful sm_goal_2 initSM)
      (denoteGraphDistributedFaithful pm_goal_2 initPM) :=
  canonical_goal_2_from_norm initSM initPM hPM hInit
    (canonical_loss_backbone_tail_goal_2 initSM initPM hInit hpre hPacked)

end
end TrainVerify.Denote.GeneratedPatterns

#print axioms TrainVerify.Denote.GeneratedPatterns.canonical_loss_backbone_tail_goal_2
#print axioms TrainVerify.Denote.GeneratedPatterns.canonical_goal_2_from_zigzag
