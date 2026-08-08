/- Canonical Goal 4, layer 0: computed router gate-score relation. -/
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

private def g4l0PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [4962], outs := [7840], params := [0] }
private def g4l0PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [4962], outs := [7841], params := [0] }
private def g4l0SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [4962],
    outs := [4963, 4964, 4965], params := [8, 1] }
private def g4l0PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [7840],
    outs := [7842, 7844, 7846], params := [8, 1] }
private def g4l0PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [7841],
    outs := [7843, 7845, 7847], params := [8, 1] }

private theorem g4l0_nodes :
    sm_goal_4.nodes[27]'(by native_decide) = g4l0SmTopk ∧
    pm_goal_4.nodes[92]'(by native_decide) = g4l0PmChunk0 ∧
    pm_goal_4.nodes[93]'(by native_decide) = g4l0PmChunk1 ∧
    pm_goal_4.nodes[97]'(by native_decide) = g4l0PmTopk0 ∧
    pm_goal_4.nodes[98]'(by native_decide) = g4l0PmTopk1 := by
  native_decide

private theorem g4l0_sm_nonempty (k : Nat)
    (h : k = 27 ∨ k = 28) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l0_pm_nonempty (k : Nat)
    (h : k = 92 ∨ k = 93 ∨ k = 94 ∨ k = 97 ∨ k = 98 ∨ k = 99) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l0_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(28, 4965), (27, 4962)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l0_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(93, 7840), (94, 7841), (92, 4962), (93, 4962),
      (98, 7846), (99, 7847), (97, 7840), (98, 7841)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l0_red_pm7840 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 7840 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 4962) := by
  let pre := (pm_goal_4.nodes.take 92).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 92
    g4l0PmChunk0 7840 (by native_decide) g4l0_nodes.2.1
    (g4l0_pm_nonempty 93 (by decide))
    (g4l0_pm_not_written 93 7840 (by decide))
  have hread : pre 4962 = denoteGraphDistributedFaithful pm_goal_4 initPM 4962 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 92 4962
      (g4l0_pm_nonempty 92 (by decide)) (g4l0_pm_not_written 92 4962 (by decide))
  rw [hcore]
  unfold g4l0PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 4962) = _
  rw [hread]

theorem g4l0_red_pm7841 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 7841 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 4962) := by
  let pre := (pm_goal_4.nodes.take 93).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 93
    g4l0PmChunk1 7841 (by native_decide) g4l0_nodes.2.2.1
    (g4l0_pm_nonempty 94 (by decide))
    (g4l0_pm_not_written 94 7841 (by decide))
  have hread : pre 4962 = denoteGraphDistributedFaithful pm_goal_4 initPM 4962 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 93 4962
      (g4l0_pm_nonempty 93 (by decide)) (g4l0_pm_not_written 93 4962 (by decide))
  rw [hcore]
  unfold g4l0PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 4962) = _
  rw [hread]

theorem g4l0_red_sm4965 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 4962).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 4965 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 4962) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 27).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 27
    g4l0SmTopk 4965 (by native_decide) g4l0_nodes.1
    (g4l0_sm_nonempty 28 (by decide))
    (g4l0_sm_not_written 28 4965 (by decide))
  have hread : pre 4962 = denoteGraphDistributedFaithful sm_goal_4 initSM 4962 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 27 4962
      (g4l0_sm_nonempty 27 (by decide)) (g4l0_sm_not_written 27 4962 (by decide))
  rw [hcore]
  unfold g4l0SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 4962) 8
    (((pre 4962).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l0_red_pm7846 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 7840).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 7846 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 7840) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 97).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 97
    g4l0PmTopk0 7846 (by native_decide) g4l0_nodes.2.2.2.1
    (g4l0_pm_nonempty 98 (by decide))
    (g4l0_pm_not_written 98 7846 (by decide))
  have hread : pre 7840 = denoteGraphDistributedFaithful pm_goal_4 initPM 7840 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 97 7840
      (g4l0_pm_nonempty 97 (by decide)) (g4l0_pm_not_written 97 7840 (by decide))
  rw [hcore]
  unfold g4l0PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 7840) 8
    (((pre 7840).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l0_red_pm7847 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 7841).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 7847 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 7841) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 98).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 98
    g4l0PmTopk1 7847 (by native_decide) g4l0_nodes.2.2.2.2
    (g4l0_pm_nonempty 99 (by decide))
    (g4l0_pm_not_written 99 7847 (by decide))
  have hread : pre 7841 = denoteGraphDistributedFaithful pm_goal_4 initPM 7841 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 98 7841
      (g4l0_pm_nonempty 98 (by decide)) (g4l0_pm_not_written 98 7841 (by decide))
  rw [hcore]
  unfold g4l0PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 7841) 8
    (((pre 7841).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-0 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l0_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 4962)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 7840)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 7841)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 4965)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 7846)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 7847)
      [4096, 64] [2048, 64] := by
  have hsm := g4l0_red_sm4965 initSM hrel.full_shape
  have hpm0 := g4l0_red_pm7846 initPM hrel.rank0_shape
  have hpm1 := g4l0_red_pm7847 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 7840)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 7841)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 4965 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 4962) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 7840,
               denoteGraphDistributedFaithful pm_goal_4 initPM 7841]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 7840) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 7841) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 7846,
             denoteGraphDistributedFaithful pm_goal_4 initPM 7847] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 4962) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 7840) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 7841) hrel.rank1_shape)

end
end TrainVerify.Denote.GeneratedPatterns
