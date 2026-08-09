/- Canonical Goal 4, layer 10: computed router gate-score relation. -/
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

private def g4l10PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5512], outs := [9480], params := [0] }
private def g4l10PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5512], outs := [9481], params := [0] }
private def g4l10SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5512],
    outs := [5513, 5514, 5515], params := [8, 1] }
private def g4l10PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9480],
    outs := [9482, 9484, 9486], params := [8, 1] }
private def g4l10PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9481],
    outs := [9483, 9485, 9487], params := [8, 1] }

private theorem g4l10_nodes :
    sm_goal_4.nodes[417]'(by native_decide) = g4l10SmTopk ∧
    pm_goal_4.nodes[932]'(by native_decide) = g4l10PmChunk0 ∧
    pm_goal_4.nodes[933]'(by native_decide) = g4l10PmChunk1 ∧
    pm_goal_4.nodes[937]'(by native_decide) = g4l10PmTopk0 ∧
    pm_goal_4.nodes[938]'(by native_decide) = g4l10PmTopk1 := by
  native_decide

private theorem g4l10_sm_nonempty (k : Nat)
    (h : k = 417 ∨ k = 418) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l10_pm_nonempty (k : Nat)
    (h : k = 932 ∨ k = 933 ∨ k = 934 ∨ k = 937 ∨ k = 938 ∨ k = 939) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l10_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(418, 5515), (417, 5512)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l10_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(933, 9480), (934, 9481), (932, 5512), (933, 5512),
      (938, 9486), (939, 9487), (937, 9480), (938, 9481)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l10_red_pm9480 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9480 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5512) := by
  let pre := (pm_goal_4.nodes.take 932).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 932
    g4l10PmChunk0 9480 (by native_decide) g4l10_nodes.2.1
    (g4l10_pm_nonempty 933 (by decide))
    (g4l10_pm_not_written 933 9480 (by decide))
  have hread : pre 5512 = denoteGraphDistributedFaithful pm_goal_4 initPM 5512 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 932 5512
      (g4l10_pm_nonempty 932 (by decide)) (g4l10_pm_not_written 932 5512 (by decide))
  rw [hcore]
  unfold g4l10PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5512) = _
  rw [hread]

theorem g4l10_red_pm9481 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9481 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5512) := by
  let pre := (pm_goal_4.nodes.take 933).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 933
    g4l10PmChunk1 9481 (by native_decide) g4l10_nodes.2.2.1
    (g4l10_pm_nonempty 934 (by decide))
    (g4l10_pm_not_written 934 9481 (by decide))
  have hread : pre 5512 = denoteGraphDistributedFaithful pm_goal_4 initPM 5512 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 933 5512
      (g4l10_pm_nonempty 933 (by decide)) (g4l10_pm_not_written 933 5512 (by decide))
  rw [hcore]
  unfold g4l10PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5512) = _
  rw [hread]

theorem g4l10_red_sm5515 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5512).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5515 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5512) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 417).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 417
    g4l10SmTopk 5515 (by native_decide) g4l10_nodes.1
    (g4l10_sm_nonempty 418 (by decide))
    (g4l10_sm_not_written 418 5515 (by decide))
  have hread : pre 5512 = denoteGraphDistributedFaithful sm_goal_4 initSM 5512 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 417 5512
      (g4l10_sm_nonempty 417 (by decide)) (g4l10_sm_not_written 417 5512 (by decide))
  rw [hcore]
  unfold g4l10SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5512) 8
    (((pre 5512).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l10_red_pm9486 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9480).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9486 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9480) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 937).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 937
    g4l10PmTopk0 9486 (by native_decide) g4l10_nodes.2.2.2.1
    (g4l10_pm_nonempty 938 (by decide))
    (g4l10_pm_not_written 938 9486 (by decide))
  have hread : pre 9480 = denoteGraphDistributedFaithful pm_goal_4 initPM 9480 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 937 9480
      (g4l10_pm_nonempty 937 (by decide)) (g4l10_pm_not_written 937 9480 (by decide))
  rw [hcore]
  unfold g4l10PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9480) 8
    (((pre 9480).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l10_red_pm9487 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 9481).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9487 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 9481) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 938).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 938
    g4l10PmTopk1 9487 (by native_decide) g4l10_nodes.2.2.2.2
    (g4l10_pm_nonempty 939 (by decide))
    (g4l10_pm_not_written 939 9487 (by decide))
  have hread : pre 9481 = denoteGraphDistributedFaithful pm_goal_4 initPM 9481 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 938 9481
      (g4l10_pm_nonempty 938 (by decide)) (g4l10_pm_not_written 938 9481 (by decide))
  rw [hcore]
  unfold g4l10PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 9481) 8
    (((pre 9481).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-10 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l10_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5512)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9480)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9481)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5515)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9486)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9487)
      [4096, 64] [2048, 64] := by
  have hsm := g4l10_red_sm5515 initSM hrel.full_shape
  have hpm0 := g4l10_red_pm9486 initPM hrel.rank0_shape
  have hpm1 := g4l10_red_pm9487 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9480)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9481)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5515 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5512) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 9480,
               denoteGraphDistributedFaithful pm_goal_4 initPM 9481]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9480) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 9481) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 9486,
             denoteGraphDistributedFaithful pm_goal_4 initPM 9487] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5512) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9480) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9481) hrel.rank1_shape)

#print axioms canonical_goal4_l10_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns


