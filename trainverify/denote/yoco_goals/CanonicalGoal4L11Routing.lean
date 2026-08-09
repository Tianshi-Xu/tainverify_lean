/- Canonical Goal 4, layer 11: computed router gate-score relation. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather
import denote.TopkGateScoreGather

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def g4l11PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5567], outs := [9644], params := [0] }
private def g4l11PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5567], outs := [9645], params := [0] }
private def g4l11SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5567],
    outs := [5568, 5569, 5570], params := [8, 1] }
private def g4l11PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9644],
    outs := [9646, 9648, 9650], params := [8, 1] }
private def g4l11PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9645],
    outs := [9647, 9649, 9651], params := [8, 1] }

private theorem g4l11_nodes :
    sm_goal_4.nodes[456]'(by native_decide) = g4l11SmTopk ∧
    pm_goal_4.nodes[1016]'(by native_decide) = g4l11PmChunk0 ∧
    pm_goal_4.nodes[1017]'(by native_decide) = g4l11PmChunk1 ∧
    pm_goal_4.nodes[1021]'(by native_decide) = g4l11PmTopk0 ∧
    pm_goal_4.nodes[1022]'(by native_decide) = g4l11PmTopk1 := by
  native_decide

private theorem g4l11_sm_nonempty (k : Nat)
    (h : k = 456 ∨ k = 457) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l11_pm_nonempty (k : Nat)
    (h : k = 1016 ∨ k = 1017 ∨ k = 1018 ∨ k = 1021 ∨ k = 1022 ∨ k = 1023) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l11_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(457, 5570), (456, 5567)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l11_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1017, 9644), (1018, 9645), (1016, 5567), (1017, 5567),
      (1022, 9650), (1023, 9651), (1021, 9644), (1022, 9645)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l11_red_pm9644 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9644 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5567) := by
  let pre := (pm_goal_4.nodes.take 1016).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1016
    g4l11PmChunk0 9644 (by native_decide) g4l11_nodes.2.1
    (g4l11_pm_nonempty 1017 (by decide))
    (g4l11_pm_not_written 1017 9644 (by decide))
  have hread : pre 5567 = denoteGraphDistributedFaithful pm_goal_4 initPM 5567 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1016 5567
      (g4l11_pm_nonempty 1016 (by decide)) (g4l11_pm_not_written 1016 5567 (by decide))
  rw [hcore]
  unfold g4l11PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5567) = _
  rw [hread]

theorem g4l11_red_pm9645 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9645 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5567) := by
  let pre := (pm_goal_4.nodes.take 1017).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1017
    g4l11PmChunk1 9645 (by native_decide) g4l11_nodes.2.2.1
    (g4l11_pm_nonempty 1018 (by decide))
    (g4l11_pm_not_written 1018 9645 (by decide))
  have hread : pre 5567 = denoteGraphDistributedFaithful pm_goal_4 initPM 5567 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1017 5567
      (g4l11_pm_nonempty 1017 (by decide)) (g4l11_pm_not_written 1017 5567 (by decide))
  rw [hcore]
  unfold g4l11PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5567) = _
  rw [hread]

theorem g4l11_red_sm5570 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5567).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5570 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5567) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 456).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 456
    g4l11SmTopk 5570 (by native_decide) g4l11_nodes.1
    (g4l11_sm_nonempty 457 (by decide))
    (g4l11_sm_not_written 457 5570 (by decide))
  have hread : pre 5567 = denoteGraphDistributedFaithful sm_goal_4 initSM 5567 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 456 5567
      (g4l11_sm_nonempty 456 (by decide)) (g4l11_sm_not_written 456 5567 (by decide))
  rw [hcore]
  unfold g4l11SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5567) 8
    (((pre 5567).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l11_red_pm9650 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9644).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9650 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9644) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 1021).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1021
    g4l11PmTopk0 9650 (by native_decide) g4l11_nodes.2.2.2.1
    (g4l11_pm_nonempty 1022 (by decide))
    (g4l11_pm_not_written 1022 9650 (by decide))
  have hread : pre 9644 = denoteGraphDistributedFaithful pm_goal_4 initPM 9644 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1021 9644
      (g4l11_pm_nonempty 1021 (by decide)) (g4l11_pm_not_written 1021 9644 (by decide))
  rw [hcore]
  unfold g4l11PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9644) 8
    (((pre 9644).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l11_red_pm9651 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9645).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9651 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9645) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 1022).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1022
    g4l11PmTopk1 9651 (by native_decide) g4l11_nodes.2.2.2.2
    (g4l11_pm_nonempty 1023 (by decide))
    (g4l11_pm_not_written 1023 9651 (by decide))
  have hread : pre 9645 = denoteGraphDistributedFaithful pm_goal_4 initPM 9645 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1022 9645
      (g4l11_pm_nonempty 1022 (by decide)) (g4l11_pm_not_written 1022 9645 (by decide))
  rw [hcore]
  unfold g4l11PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9645) 8
    (((pre 9645).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-11 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l11_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5567)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9644)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9645)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5570)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9650)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9651)
      [4096, 64] [2048, 64] := by
  have hsm := g4l11_red_sm5570 initSM hrel.full_shape
  have hpm0 := g4l11_red_pm9650 initPM hrel.rank0_shape
  have hpm1 := g4l11_red_pm9651 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9644)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9645)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5570 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5567) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 9644,
               denoteGraphDistributedFaithful pm_goal_4 initPM 9645]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9644) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9645) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 9650,
             denoteGraphDistributedFaithful pm_goal_4 initPM 9651] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5567) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9644) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9645) hrel.rank1_shape)

#print axioms canonical_goal4_l11_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns

