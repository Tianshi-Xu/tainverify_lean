/- Canonical Goal 4, layer 5: computed router gate-score relation. -/
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

private def g4l5PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5237], outs := [8660], params := [0] }
private def g4l5PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5237], outs := [8661], params := [0] }
private def g4l5SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5237],
    outs := [5238, 5239, 5240], params := [8, 1] }
private def g4l5PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8660],
    outs := [8662, 8664, 8666], params := [8, 1] }
private def g4l5PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8661],
    outs := [8663, 8665, 8667], params := [8, 1] }

private theorem g4l5_nodes :
    sm_goal_4.nodes[222]'(by native_decide) = g4l5SmTopk ∧
    pm_goal_4.nodes[512]'(by native_decide) = g4l5PmChunk0 ∧
    pm_goal_4.nodes[513]'(by native_decide) = g4l5PmChunk1 ∧
    pm_goal_4.nodes[517]'(by native_decide) = g4l5PmTopk0 ∧
    pm_goal_4.nodes[518]'(by native_decide) = g4l5PmTopk1 := by
  native_decide

private theorem g4l5_sm_nonempty (k : Nat)
    (h : k = 222 ∨ k = 223) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l5_pm_nonempty (k : Nat)
    (h : k = 512 ∨ k = 513 ∨ k = 514 ∨ k = 517 ∨ k = 518 ∨ k = 519) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l5_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(223, 5240), (222, 5237)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l5_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(513, 8660), (514, 8661), (512, 5237), (513, 5237),
      (518, 8666), (519, 8667), (517, 8660), (518, 8661)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l5_red_pm8660 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8660 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5237) := by
  let pre := (pm_goal_4.nodes.take 512).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 512
    g4l5PmChunk0 8660 (by native_decide) g4l5_nodes.2.1
    (g4l5_pm_nonempty 513 (by decide))
    (g4l5_pm_not_written 513 8660 (by decide))
  have hread : pre 5237 = denoteGraphDistributedFaithful pm_goal_4 initPM 5237 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 512 5237
      (g4l5_pm_nonempty 512 (by decide)) (g4l5_pm_not_written 512 5237 (by decide))
  rw [hcore]
  unfold g4l5PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5237) = _
  rw [hread]

theorem g4l5_red_pm8661 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8661 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5237) := by
  let pre := (pm_goal_4.nodes.take 513).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 513
    g4l5PmChunk1 8661 (by native_decide) g4l5_nodes.2.2.1
    (g4l5_pm_nonempty 514 (by decide))
    (g4l5_pm_not_written 514 8661 (by decide))
  have hread : pre 5237 = denoteGraphDistributedFaithful pm_goal_4 initPM 5237 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 513 5237
      (g4l5_pm_nonempty 513 (by decide)) (g4l5_pm_not_written 513 5237 (by decide))
  rw [hcore]
  unfold g4l5PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5237) = _
  rw [hread]

theorem g4l5_red_sm5240 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5237).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5240 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5237) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 222).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 222
    g4l5SmTopk 5240 (by native_decide) g4l5_nodes.1
    (g4l5_sm_nonempty 223 (by decide))
    (g4l5_sm_not_written 223 5240 (by decide))
  have hread : pre 5237 = denoteGraphDistributedFaithful sm_goal_4 initSM 5237 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 222 5237
      (g4l5_sm_nonempty 222 (by decide)) (g4l5_sm_not_written 222 5237 (by decide))
  rw [hcore]
  unfold g4l5SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5237) 8
    (((pre 5237).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l5_red_pm8666 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8660).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8666 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8660) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 517).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 517
    g4l5PmTopk0 8666 (by native_decide) g4l5_nodes.2.2.2.1
    (g4l5_pm_nonempty 518 (by decide))
    (g4l5_pm_not_written 518 8666 (by decide))
  have hread : pre 8660 = denoteGraphDistributedFaithful pm_goal_4 initPM 8660 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 517 8660
      (g4l5_pm_nonempty 517 (by decide)) (g4l5_pm_not_written 517 8660 (by decide))
  rw [hcore]
  unfold g4l5PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8660) 8
    (((pre 8660).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l5_red_pm8667 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8661).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8667 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8661) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 518).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 518
    g4l5PmTopk1 8667 (by native_decide) g4l5_nodes.2.2.2.2
    (g4l5_pm_nonempty 519 (by decide))
    (g4l5_pm_not_written 519 8667 (by decide))
  have hread : pre 8661 = denoteGraphDistributedFaithful pm_goal_4 initPM 8661 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 518 8661
      (g4l5_pm_nonempty 518 (by decide)) (g4l5_pm_not_written 518 8661 (by decide))
  rw [hcore]
  unfold g4l5PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8661) 8
    (((pre 8661).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-5 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l5_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5237)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8660)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8661)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5240)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8666)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8667)
      [4096, 64] [2048, 64] := by
  have hsm := g4l5_red_sm5240 initSM hrel.full_shape
  have hpm0 := g4l5_red_pm8666 initPM hrel.rank0_shape
  have hpm1 := g4l5_red_pm8667 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8660)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8661)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5240 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5237) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 8660,
               denoteGraphDistributedFaithful pm_goal_4 initPM 8661]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8660) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8661) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 8666,
             denoteGraphDistributedFaithful pm_goal_4 initPM 8667] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5237) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8660) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8661) hrel.rank1_shape)

#print axioms canonical_goal4_l5_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns

