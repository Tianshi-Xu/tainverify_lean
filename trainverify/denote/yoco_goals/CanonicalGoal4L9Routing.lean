/- Canonical Goal 4, layer 9: computed router gate-score relation. -/
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

private def g4l9PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5457], outs := [9316], params := [0] }
private def g4l9PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5457], outs := [9317], params := [0] }
private def g4l9SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5457],
    outs := [5458, 5459, 5460], params := [8, 1] }
private def g4l9PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9316],
    outs := [9318, 9320, 9322], params := [8, 1] }
private def g4l9PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9317],
    outs := [9319, 9321, 9323], params := [8, 1] }

private theorem g4l9_nodes :
    sm_goal_4.nodes[378]'(by native_decide) = g4l9SmTopk ∧
    pm_goal_4.nodes[848]'(by native_decide) = g4l9PmChunk0 ∧
    pm_goal_4.nodes[849]'(by native_decide) = g4l9PmChunk1 ∧
    pm_goal_4.nodes[853]'(by native_decide) = g4l9PmTopk0 ∧
    pm_goal_4.nodes[854]'(by native_decide) = g4l9PmTopk1 := by
  native_decide

private theorem g4l9_sm_nonempty (k : Nat)
    (h : k = 378 ∨ k = 379) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l9_pm_nonempty (k : Nat)
    (h : k = 848 ∨ k = 849 ∨ k = 850 ∨ k = 853 ∨ k = 854 ∨ k = 855) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l9_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(379, 5460), (378, 5457)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l9_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(849, 9316), (850, 9317), (848, 5457), (849, 5457),
      (854, 9322), (855, 9323), (853, 9316), (854, 9317)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l9_red_pm9316 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9316 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5457) := by
  let pre := (pm_goal_4.nodes.take 848).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 848
    g4l9PmChunk0 9316 (by native_decide) g4l9_nodes.2.1
    (g4l9_pm_nonempty 849 (by decide))
    (g4l9_pm_not_written 849 9316 (by decide))
  have hread : pre 5457 = denoteGraphDistributedFaithful pm_goal_4 initPM 5457 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 848 5457
      (g4l9_pm_nonempty 848 (by decide)) (g4l9_pm_not_written 848 5457 (by decide))
  rw [hcore]
  unfold g4l9PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5457) = _
  rw [hread]

theorem g4l9_red_pm9317 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9317 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5457) := by
  let pre := (pm_goal_4.nodes.take 849).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 849
    g4l9PmChunk1 9317 (by native_decide) g4l9_nodes.2.2.1
    (g4l9_pm_nonempty 850 (by decide))
    (g4l9_pm_not_written 850 9317 (by decide))
  have hread : pre 5457 = denoteGraphDistributedFaithful pm_goal_4 initPM 5457 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 849 5457
      (g4l9_pm_nonempty 849 (by decide)) (g4l9_pm_not_written 849 5457 (by decide))
  rw [hcore]
  unfold g4l9PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5457) = _
  rw [hread]

theorem g4l9_red_sm5460 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5457).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5460 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5457) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 378).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 378
    g4l9SmTopk 5460 (by native_decide) g4l9_nodes.1
    (g4l9_sm_nonempty 379 (by decide))
    (g4l9_sm_not_written 379 5460 (by decide))
  have hread : pre 5457 = denoteGraphDistributedFaithful sm_goal_4 initSM 5457 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 378 5457
      (g4l9_sm_nonempty 378 (by decide)) (g4l9_sm_not_written 378 5457 (by decide))
  rw [hcore]
  unfold g4l9SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5457) 8
    (((pre 5457).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l9_red_pm9322 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9316).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9322 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9316) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 853).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 853
    g4l9PmTopk0 9322 (by native_decide) g4l9_nodes.2.2.2.1
    (g4l9_pm_nonempty 854 (by decide))
    (g4l9_pm_not_written 854 9322 (by decide))
  have hread : pre 9316 = denoteGraphDistributedFaithful pm_goal_4 initPM 9316 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 853 9316
      (g4l9_pm_nonempty 853 (by decide)) (g4l9_pm_not_written 853 9316 (by decide))
  rw [hcore]
  unfold g4l9PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9316) 8
    (((pre 9316).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l9_red_pm9323 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9317).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9323 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9317) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 854).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 854
    g4l9PmTopk1 9323 (by native_decide) g4l9_nodes.2.2.2.2
    (g4l9_pm_nonempty 855 (by decide))
    (g4l9_pm_not_written 855 9323 (by decide))
  have hread : pre 9317 = denoteGraphDistributedFaithful pm_goal_4 initPM 9317 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 854 9317
      (g4l9_pm_nonempty 854 (by decide)) (g4l9_pm_not_written 854 9317 (by decide))
  rw [hcore]
  unfold g4l9PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9317) 8
    (((pre 9317).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-9 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l9_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5457)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9316)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9317)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5460)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9322)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9323)
      [4096, 64] [2048, 64] := by
  have hsm := g4l9_red_sm5460 initSM hrel.full_shape
  have hpm0 := g4l9_red_pm9322 initPM hrel.rank0_shape
  have hpm1 := g4l9_red_pm9323 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9316)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9317)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5460 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5457) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 9316,
               denoteGraphDistributedFaithful pm_goal_4 initPM 9317]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9316) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9317) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 9322,
             denoteGraphDistributedFaithful pm_goal_4 initPM 9323] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5457) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9316) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9317) hrel.rank1_shape)

#print axioms canonical_goal4_l9_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns


