/- Canonical Goal 4, layer 2: computed router gate-score relation. -/
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

private def g4l2PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5072], outs := [8168], params := [0] }
private def g4l2PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5072], outs := [8169], params := [0] }
private def g4l2SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5072],
    outs := [5073, 5074, 5075], params := [8, 1] }
private def g4l2PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8168],
    outs := [8170, 8172, 8174], params := [8, 1] }
private def g4l2PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8169],
    outs := [8171, 8173, 8175], params := [8, 1] }

private theorem g4l2_nodes :
    sm_goal_4.nodes[105]'(by native_decide) = g4l2SmTopk ∧
    pm_goal_4.nodes[260]'(by native_decide) = g4l2PmChunk0 ∧
    pm_goal_4.nodes[261]'(by native_decide) = g4l2PmChunk1 ∧
    pm_goal_4.nodes[265]'(by native_decide) = g4l2PmTopk0 ∧
    pm_goal_4.nodes[266]'(by native_decide) = g4l2PmTopk1 := by
  native_decide

private theorem g4l2_sm_nonempty (k : Nat)
    (h : k = 105 ∨ k = 106) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l2_pm_nonempty (k : Nat)
    (h : k = 260 ∨ k = 261 ∨ k = 262 ∨ k = 265 ∨ k = 266 ∨ k = 267) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l2_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(106, 5075), (105, 5072)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l2_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(261, 8168), (262, 8169), (260, 5072), (261, 5072),
      (266, 8174), (267, 8175), (265, 8168), (266, 8169)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l2_red_pm8168 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8168 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5072) := by
  let pre := (pm_goal_4.nodes.take 260).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 260
    g4l2PmChunk0 8168 (by native_decide) g4l2_nodes.2.1
    (g4l2_pm_nonempty 261 (by decide))
    (g4l2_pm_not_written 261 8168 (by decide))
  have hread : pre 5072 = denoteGraphDistributedFaithful pm_goal_4 initPM 5072 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 260 5072
      (g4l2_pm_nonempty 260 (by decide)) (g4l2_pm_not_written 260 5072 (by decide))
  rw [hcore]
  unfold g4l2PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5072) = _
  rw [hread]

theorem g4l2_red_pm8169 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8169 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5072) := by
  let pre := (pm_goal_4.nodes.take 261).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 261
    g4l2PmChunk1 8169 (by native_decide) g4l2_nodes.2.2.1
    (g4l2_pm_nonempty 262 (by decide))
    (g4l2_pm_not_written 262 8169 (by decide))
  have hread : pre 5072 = denoteGraphDistributedFaithful pm_goal_4 initPM 5072 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 261 5072
      (g4l2_pm_nonempty 261 (by decide)) (g4l2_pm_not_written 261 5072 (by decide))
  rw [hcore]
  unfold g4l2PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5072) = _
  rw [hread]

theorem g4l2_red_sm5075 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5072).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5075 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5072) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 105).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 105
    g4l2SmTopk 5075 (by native_decide) g4l2_nodes.1
    (g4l2_sm_nonempty 106 (by decide))
    (g4l2_sm_not_written 106 5075 (by decide))
  have hread : pre 5072 = denoteGraphDistributedFaithful sm_goal_4 initSM 5072 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 105 5072
      (g4l2_sm_nonempty 105 (by decide)) (g4l2_sm_not_written 105 5072 (by decide))
  rw [hcore]
  unfold g4l2SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5072) 8
    (((pre 5072).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l2_red_pm8174 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8168).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8174 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8168) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 265).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 265
    g4l2PmTopk0 8174 (by native_decide) g4l2_nodes.2.2.2.1
    (g4l2_pm_nonempty 266 (by decide))
    (g4l2_pm_not_written 266 8174 (by decide))
  have hread : pre 8168 = denoteGraphDistributedFaithful pm_goal_4 initPM 8168 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 265 8168
      (g4l2_pm_nonempty 265 (by decide)) (g4l2_pm_not_written 265 8168 (by decide))
  rw [hcore]
  unfold g4l2PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8168) 8
    (((pre 8168).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l2_red_pm8175 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8169).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8175 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8169) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 266).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 266
    g4l2PmTopk1 8175 (by native_decide) g4l2_nodes.2.2.2.2
    (g4l2_pm_nonempty 267 (by decide))
    (g4l2_pm_not_written 267 8175 (by decide))
  have hread : pre 8169 = denoteGraphDistributedFaithful pm_goal_4 initPM 8169 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 266 8169
      (g4l2_pm_nonempty 266 (by decide)) (g4l2_pm_not_written 266 8169 (by decide))
  rw [hcore]
  unfold g4l2PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8169) 8
    (((pre 8169).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-2 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l2_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5072)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8168)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8169)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5075)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8174)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8175)
      [4096, 64] [2048, 64] := by
  have hsm := g4l2_red_sm5075 initSM hrel.full_shape
  have hpm0 := g4l2_red_pm8174 initPM hrel.rank0_shape
  have hpm1 := g4l2_red_pm8175 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8168)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8169)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5075 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5072) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 8168,
               denoteGraphDistributedFaithful pm_goal_4 initPM 8169]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8168) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8169) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 8174,
             denoteGraphDistributedFaithful pm_goal_4 initPM 8175] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5072) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8168) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8169) hrel.rank1_shape)

#print axioms canonical_goal4_l2_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns
