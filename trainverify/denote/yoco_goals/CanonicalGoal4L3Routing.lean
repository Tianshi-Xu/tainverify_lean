/- Canonical Goal 4, layer 3: computed router gate-score relation. -/
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

private def g4l3PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5127], outs := [8332], params := [0] }
private def g4l3PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5127], outs := [8333], params := [0] }
private def g4l3SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5127],
    outs := [5128, 5129, 5130], params := [8, 1] }
private def g4l3PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8332],
    outs := [8334, 8336, 8338], params := [8, 1] }
private def g4l3PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8333],
    outs := [8335, 8337, 8339], params := [8, 1] }

private theorem g4l3_nodes :
    sm_goal_4.nodes[144]'(by native_decide) = g4l3SmTopk ∧
    pm_goal_4.nodes[344]'(by native_decide) = g4l3PmChunk0 ∧
    pm_goal_4.nodes[345]'(by native_decide) = g4l3PmChunk1 ∧
    pm_goal_4.nodes[349]'(by native_decide) = g4l3PmTopk0 ∧
    pm_goal_4.nodes[350]'(by native_decide) = g4l3PmTopk1 := by
  native_decide

private theorem g4l3_sm_nonempty (k : Nat)
    (h : k = 144 ∨ k = 145) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l3_pm_nonempty (k : Nat)
    (h : k = 344 ∨ k = 345 ∨ k = 346 ∨ k = 349 ∨ k = 350 ∨ k = 351) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l3_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(145, 5130), (144, 5127)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l3_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(345, 8332), (346, 8333), (344, 5127), (345, 5127),
      (350, 8338), (351, 8339), (349, 8332), (350, 8333)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l3_red_pm8332 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8332 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5127) := by
  let pre := (pm_goal_4.nodes.take 344).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 344
    g4l3PmChunk0 8332 (by native_decide) g4l3_nodes.2.1
    (g4l3_pm_nonempty 345 (by decide))
    (g4l3_pm_not_written 345 8332 (by decide))
  have hread : pre 5127 = denoteGraphDistributedFaithful pm_goal_4 initPM 5127 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 344 5127
      (g4l3_pm_nonempty 344 (by decide)) (g4l3_pm_not_written 344 5127 (by decide))
  rw [hcore]
  unfold g4l3PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5127) = _
  rw [hread]

theorem g4l3_red_pm8333 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8333 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5127) := by
  let pre := (pm_goal_4.nodes.take 345).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 345
    g4l3PmChunk1 8333 (by native_decide) g4l3_nodes.2.2.1
    (g4l3_pm_nonempty 346 (by decide))
    (g4l3_pm_not_written 346 8333 (by decide))
  have hread : pre 5127 = denoteGraphDistributedFaithful pm_goal_4 initPM 5127 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 345 5127
      (g4l3_pm_nonempty 345 (by decide)) (g4l3_pm_not_written 345 5127 (by decide))
  rw [hcore]
  unfold g4l3PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5127) = _
  rw [hread]

theorem g4l3_red_sm5130 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5127).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5130 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5127) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 144).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 144
    g4l3SmTopk 5130 (by native_decide) g4l3_nodes.1
    (g4l3_sm_nonempty 145 (by decide))
    (g4l3_sm_not_written 145 5130 (by decide))
  have hread : pre 5127 = denoteGraphDistributedFaithful sm_goal_4 initSM 5127 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 144 5127
      (g4l3_sm_nonempty 144 (by decide)) (g4l3_sm_not_written 144 5127 (by decide))
  rw [hcore]
  unfold g4l3SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5127) 8
    (((pre 5127).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l3_red_pm8338 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8332).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8338 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8332) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 349).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 349
    g4l3PmTopk0 8338 (by native_decide) g4l3_nodes.2.2.2.1
    (g4l3_pm_nonempty 350 (by decide))
    (g4l3_pm_not_written 350 8338 (by decide))
  have hread : pre 8332 = denoteGraphDistributedFaithful pm_goal_4 initPM 8332 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 349 8332
      (g4l3_pm_nonempty 349 (by decide)) (g4l3_pm_not_written 349 8332 (by decide))
  rw [hcore]
  unfold g4l3PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8332) 8
    (((pre 8332).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l3_red_pm8339 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8333).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8339 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8333) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 350).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 350
    g4l3PmTopk1 8339 (by native_decide) g4l3_nodes.2.2.2.2
    (g4l3_pm_nonempty 351 (by decide))
    (g4l3_pm_not_written 351 8339 (by decide))
  have hread : pre 8333 = denoteGraphDistributedFaithful pm_goal_4 initPM 8333 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 350 8333
      (g4l3_pm_nonempty 350 (by decide)) (g4l3_pm_not_written 350 8333 (by decide))
  rw [hcore]
  unfold g4l3PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8333) 8
    (((pre 8333).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-3 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l3_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5127)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8332)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8333)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5130)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8338)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8339)
      [4096, 64] [2048, 64] := by
  have hsm := g4l3_red_sm5130 initSM hrel.full_shape
  have hpm0 := g4l3_red_pm8338 initPM hrel.rank0_shape
  have hpm1 := g4l3_red_pm8339 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8332)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8333)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5130 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5127) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 8332,
               denoteGraphDistributedFaithful pm_goal_4 initPM 8333]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8332) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8333) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 8338,
             denoteGraphDistributedFaithful pm_goal_4 initPM 8339] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5127) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8332) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8333) hrel.rank1_shape)

#print axioms canonical_goal4_l3_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns

