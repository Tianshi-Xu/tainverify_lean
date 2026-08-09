/- Canonical Goal 4, layer 7: computed router gate-score relation. -/
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

private def g4l7PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5347], outs := [8988], params := [0] }
private def g4l7PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5347], outs := [8989], params := [0] }
private def g4l7SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5347],
    outs := [5348, 5349, 5350], params := [8, 1] }
private def g4l7PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8988],
    outs := [8990, 8992, 8994], params := [8, 1] }
private def g4l7PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8989],
    outs := [8991, 8993, 8995], params := [8, 1] }

private theorem g4l7_nodes :
    sm_goal_4.nodes[300]'(by native_decide) = g4l7SmTopk ∧
    pm_goal_4.nodes[680]'(by native_decide) = g4l7PmChunk0 ∧
    pm_goal_4.nodes[681]'(by native_decide) = g4l7PmChunk1 ∧
    pm_goal_4.nodes[685]'(by native_decide) = g4l7PmTopk0 ∧
    pm_goal_4.nodes[686]'(by native_decide) = g4l7PmTopk1 := by
  native_decide

private theorem g4l7_sm_nonempty (k : Nat)
    (h : k = 300 ∨ k = 301) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l7_pm_nonempty (k : Nat)
    (h : k = 680 ∨ k = 681 ∨ k = 682 ∨ k = 685 ∨ k = 686 ∨ k = 687) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l7_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(301, 5350), (300, 5347)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l7_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(681, 8988), (682, 8989), (680, 5347), (681, 5347),
      (686, 8994), (687, 8995), (685, 8988), (686, 8989)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l7_red_pm8988 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8988 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5347) := by
  let pre := (pm_goal_4.nodes.take 680).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 680
    g4l7PmChunk0 8988 (by native_decide) g4l7_nodes.2.1
    (g4l7_pm_nonempty 681 (by decide))
    (g4l7_pm_not_written 681 8988 (by decide))
  have hread : pre 5347 = denoteGraphDistributedFaithful pm_goal_4 initPM 5347 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 680 5347
      (g4l7_pm_nonempty 680 (by decide)) (g4l7_pm_not_written 680 5347 (by decide))
  rw [hcore]
  unfold g4l7PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5347) = _
  rw [hread]

theorem g4l7_red_pm8989 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8989 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5347) := by
  let pre := (pm_goal_4.nodes.take 681).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 681
    g4l7PmChunk1 8989 (by native_decide) g4l7_nodes.2.2.1
    (g4l7_pm_nonempty 682 (by decide))
    (g4l7_pm_not_written 682 8989 (by decide))
  have hread : pre 5347 = denoteGraphDistributedFaithful pm_goal_4 initPM 5347 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 681 5347
      (g4l7_pm_nonempty 681 (by decide)) (g4l7_pm_not_written 681 5347 (by decide))
  rw [hcore]
  unfold g4l7PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5347) = _
  rw [hread]

theorem g4l7_red_sm5350 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5347).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5350 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5347) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 300).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 300
    g4l7SmTopk 5350 (by native_decide) g4l7_nodes.1
    (g4l7_sm_nonempty 301 (by decide))
    (g4l7_sm_not_written 301 5350 (by decide))
  have hread : pre 5347 = denoteGraphDistributedFaithful sm_goal_4 initSM 5347 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 300 5347
      (g4l7_sm_nonempty 300 (by decide)) (g4l7_sm_not_written 300 5347 (by decide))
  rw [hcore]
  unfold g4l7SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5347) 8
    (((pre 5347).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l7_red_pm8994 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8988).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8994 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8988) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 685).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 685
    g4l7PmTopk0 8994 (by native_decide) g4l7_nodes.2.2.2.1
    (g4l7_pm_nonempty 686 (by decide))
    (g4l7_pm_not_written 686 8994 (by decide))
  have hread : pre 8988 = denoteGraphDistributedFaithful pm_goal_4 initPM 8988 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 685 8988
      (g4l7_pm_nonempty 685 (by decide)) (g4l7_pm_not_written 685 8988 (by decide))
  rw [hcore]
  unfold g4l7PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8988) 8
    (((pre 8988).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l7_red_pm8995 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8989).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8995 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8989) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 686).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 686
    g4l7PmTopk1 8995 (by native_decide) g4l7_nodes.2.2.2.2
    (g4l7_pm_nonempty 687 (by decide))
    (g4l7_pm_not_written 687 8995 (by decide))
  have hread : pre 8989 = denoteGraphDistributedFaithful pm_goal_4 initPM 8989 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 686 8989
      (g4l7_pm_nonempty 686 (by decide)) (g4l7_pm_not_written 686 8989 (by decide))
  rw [hcore]
  unfold g4l7PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8989) 8
    (((pre 8989).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-7 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l7_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5347)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8988)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8989)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5350)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8994)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8995)
      [4096, 64] [2048, 64] := by
  have hsm := g4l7_red_sm5350 initSM hrel.full_shape
  have hpm0 := g4l7_red_pm8994 initPM hrel.rank0_shape
  have hpm1 := g4l7_red_pm8995 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8988)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8989)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5350 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5347) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 8988,
               denoteGraphDistributedFaithful pm_goal_4 initPM 8989]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8988) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8989) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 8994,
             denoteGraphDistributedFaithful pm_goal_4 initPM 8995] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5347) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8988) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8989) hrel.rank1_shape)

#print axioms canonical_goal4_l7_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns

