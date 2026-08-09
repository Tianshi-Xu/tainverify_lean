/- Canonical Goal 4, layer 6: computed router gate-score relation. -/
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

private def g4l6PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5292], outs := [8824], params := [0] }
private def g4l6PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5292], outs := [8825], params := [0] }
private def g4l6SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5292],
    outs := [5293, 5294, 5295], params := [8, 1] }
private def g4l6PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8824],
    outs := [8826, 8828, 8830], params := [8, 1] }
private def g4l6PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8825],
    outs := [8827, 8829, 8831], params := [8, 1] }

private theorem g4l6_nodes :
    sm_goal_4.nodes[261]'(by native_decide) = g4l6SmTopk ∧
    pm_goal_4.nodes[596]'(by native_decide) = g4l6PmChunk0 ∧
    pm_goal_4.nodes[597]'(by native_decide) = g4l6PmChunk1 ∧
    pm_goal_4.nodes[601]'(by native_decide) = g4l6PmTopk0 ∧
    pm_goal_4.nodes[602]'(by native_decide) = g4l6PmTopk1 := by
  native_decide

private theorem g4l6_sm_nonempty (k : Nat)
    (h : k = 261 ∨ k = 262) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l6_pm_nonempty (k : Nat)
    (h : k = 596 ∨ k = 597 ∨ k = 598 ∨ k = 601 ∨ k = 602 ∨ k = 603) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l6_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(262, 5295), (261, 5292)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l6_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(597, 8824), (598, 8825), (596, 5292), (597, 5292),
      (602, 8830), (603, 8831), (601, 8824), (602, 8825)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l6_red_pm8824 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8824 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5292) := by
  let pre := (pm_goal_4.nodes.take 596).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 596
    g4l6PmChunk0 8824 (by native_decide) g4l6_nodes.2.1
    (g4l6_pm_nonempty 597 (by decide))
    (g4l6_pm_not_written 597 8824 (by decide))
  have hread : pre 5292 = denoteGraphDistributedFaithful pm_goal_4 initPM 5292 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 596 5292
      (g4l6_pm_nonempty 596 (by decide)) (g4l6_pm_not_written 596 5292 (by decide))
  rw [hcore]
  unfold g4l6PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5292) = _
  rw [hread]

theorem g4l6_red_pm8825 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8825 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5292) := by
  let pre := (pm_goal_4.nodes.take 597).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 597
    g4l6PmChunk1 8825 (by native_decide) g4l6_nodes.2.2.1
    (g4l6_pm_nonempty 598 (by decide))
    (g4l6_pm_not_written 598 8825 (by decide))
  have hread : pre 5292 = denoteGraphDistributedFaithful pm_goal_4 initPM 5292 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 597 5292
      (g4l6_pm_nonempty 597 (by decide)) (g4l6_pm_not_written 597 5292 (by decide))
  rw [hcore]
  unfold g4l6PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5292) = _
  rw [hread]

theorem g4l6_red_sm5295 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5292).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5295 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5292) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 261).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 261
    g4l6SmTopk 5295 (by native_decide) g4l6_nodes.1
    (g4l6_sm_nonempty 262 (by decide))
    (g4l6_sm_not_written 262 5295 (by decide))
  have hread : pre 5292 = denoteGraphDistributedFaithful sm_goal_4 initSM 5292 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 261 5292
      (g4l6_sm_nonempty 261 (by decide)) (g4l6_sm_not_written 261 5292 (by decide))
  rw [hcore]
  unfold g4l6SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5292) 8
    (((pre 5292).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l6_red_pm8830 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8824).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8830 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8824) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 601).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 601
    g4l6PmTopk0 8830 (by native_decide) g4l6_nodes.2.2.2.1
    (g4l6_pm_nonempty 602 (by decide))
    (g4l6_pm_not_written 602 8830 (by decide))
  have hread : pre 8824 = denoteGraphDistributedFaithful pm_goal_4 initPM 8824 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 601 8824
      (g4l6_pm_nonempty 601 (by decide)) (g4l6_pm_not_written 601 8824 (by decide))
  rw [hcore]
  unfold g4l6PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8824) 8
    (((pre 8824).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l6_red_pm8831 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8825).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8831 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8825) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 602).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 602
    g4l6PmTopk1 8831 (by native_decide) g4l6_nodes.2.2.2.2
    (g4l6_pm_nonempty 603 (by decide))
    (g4l6_pm_not_written 603 8831 (by decide))
  have hread : pre 8825 = denoteGraphDistributedFaithful pm_goal_4 initPM 8825 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 602 8825
      (g4l6_pm_nonempty 602 (by decide)) (g4l6_pm_not_written 602 8825 (by decide))
  rw [hcore]
  unfold g4l6PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8825) 8
    (((pre 8825).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-6 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l6_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5292)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8824)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8825)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5295)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8830)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8831)
      [4096, 64] [2048, 64] := by
  have hsm := g4l6_red_sm5295 initSM hrel.full_shape
  have hpm0 := g4l6_red_pm8830 initPM hrel.rank0_shape
  have hpm1 := g4l6_red_pm8831 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8824)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8825)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5295 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5292) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 8824,
               denoteGraphDistributedFaithful pm_goal_4 initPM 8825]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8824) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8825) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 8830,
             denoteGraphDistributedFaithful pm_goal_4 initPM 8831] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5292) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8824) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8825) hrel.rank1_shape)

#print axioms canonical_goal4_l6_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns


