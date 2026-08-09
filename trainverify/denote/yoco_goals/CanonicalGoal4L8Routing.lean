/- Canonical Goal 4, layer 8: computed router gate-score relation. -/
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

private def g4l8PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5402], outs := [9152], params := [0] }
private def g4l8PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5402], outs := [9153], params := [0] }
private def g4l8SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5402],
    outs := [5403, 5404, 5405], params := [8, 1] }
private def g4l8PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9152],
    outs := [9154, 9156, 9158], params := [8, 1] }
private def g4l8PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9153],
    outs := [9155, 9157, 9159], params := [8, 1] }

private theorem g4l8_nodes :
    sm_goal_4.nodes[339]'(by native_decide) = g4l8SmTopk ∧
    pm_goal_4.nodes[764]'(by native_decide) = g4l8PmChunk0 ∧
    pm_goal_4.nodes[765]'(by native_decide) = g4l8PmChunk1 ∧
    pm_goal_4.nodes[769]'(by native_decide) = g4l8PmTopk0 ∧
    pm_goal_4.nodes[770]'(by native_decide) = g4l8PmTopk1 := by
  native_decide

private theorem g4l8_sm_nonempty (k : Nat)
    (h : k = 339 ∨ k = 340) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l8_pm_nonempty (k : Nat)
    (h : k = 764 ∨ k = 765 ∨ k = 766 ∨ k = 769 ∨ k = 770 ∨ k = 771) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l8_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(340, 5405), (339, 5402)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l8_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(765, 9152), (766, 9153), (764, 5402), (765, 5402),
      (770, 9158), (771, 9159), (769, 9152), (770, 9153)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l8_red_pm9152 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9152 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5402) := by
  let pre := (pm_goal_4.nodes.take 764).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 764
    g4l8PmChunk0 9152 (by native_decide) g4l8_nodes.2.1
    (g4l8_pm_nonempty 765 (by decide))
    (g4l8_pm_not_written 765 9152 (by decide))
  have hread : pre 5402 = denoteGraphDistributedFaithful pm_goal_4 initPM 5402 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 764 5402
      (g4l8_pm_nonempty 764 (by decide)) (g4l8_pm_not_written 764 5402 (by decide))
  rw [hcore]
  unfold g4l8PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5402) = _
  rw [hread]

theorem g4l8_red_pm9153 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9153 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5402) := by
  let pre := (pm_goal_4.nodes.take 765).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 765
    g4l8PmChunk1 9153 (by native_decide) g4l8_nodes.2.2.1
    (g4l8_pm_nonempty 766 (by decide))
    (g4l8_pm_not_written 766 9153 (by decide))
  have hread : pre 5402 = denoteGraphDistributedFaithful pm_goal_4 initPM 5402 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 765 5402
      (g4l8_pm_nonempty 765 (by decide)) (g4l8_pm_not_written 765 5402 (by decide))
  rw [hcore]
  unfold g4l8PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5402) = _
  rw [hread]

theorem g4l8_red_sm5405 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5402).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5405 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5402) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 339).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 339
    g4l8SmTopk 5405 (by native_decide) g4l8_nodes.1
    (g4l8_sm_nonempty 340 (by decide))
    (g4l8_sm_not_written 340 5405 (by decide))
  have hread : pre 5402 = denoteGraphDistributedFaithful sm_goal_4 initSM 5402 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 339 5402
      (g4l8_sm_nonempty 339 (by decide)) (g4l8_sm_not_written 339 5402 (by decide))
  rw [hcore]
  unfold g4l8SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5402) 8
    (((pre 5402).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l8_red_pm9158 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9152).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9158 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9152) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 769).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 769
    g4l8PmTopk0 9158 (by native_decide) g4l8_nodes.2.2.2.1
    (g4l8_pm_nonempty 770 (by decide))
    (g4l8_pm_not_written 770 9158 (by decide))
  have hread : pre 9152 = denoteGraphDistributedFaithful pm_goal_4 initPM 9152 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 769 9152
      (g4l8_pm_nonempty 769 (by decide)) (g4l8_pm_not_written 769 9152 (by decide))
  rw [hcore]
  unfold g4l8PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9152) 8
    (((pre 9152).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l8_red_pm9159 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9153).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9159 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9153) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 770).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 770
    g4l8PmTopk1 9159 (by native_decide) g4l8_nodes.2.2.2.2
    (g4l8_pm_nonempty 771 (by decide))
    (g4l8_pm_not_written 771 9159 (by decide))
  have hread : pre 9153 = denoteGraphDistributedFaithful pm_goal_4 initPM 9153 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 770 9153
      (g4l8_pm_nonempty 770 (by decide)) (g4l8_pm_not_written 770 9153 (by decide))
  rw [hcore]
  unfold g4l8PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9153) 8
    (((pre 9153).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-8 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l8_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5402)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9152)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9153)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5405)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9158)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9159)
      [4096, 64] [2048, 64] := by
  have hsm := g4l8_red_sm5405 initSM hrel.full_shape
  have hpm0 := g4l8_red_pm9158 initPM hrel.rank0_shape
  have hpm1 := g4l8_red_pm9159 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9152)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9153)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5405 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5402) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 9152,
               denoteGraphDistributedFaithful pm_goal_4 initPM 9153]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9152) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9153) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 9158,
             denoteGraphDistributedFaithful pm_goal_4 initPM 9159] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5402) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9152) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9153) hrel.rank1_shape)

#print axioms canonical_goal4_l8_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns

