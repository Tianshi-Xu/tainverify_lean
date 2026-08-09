/- Canonical Goal 4, layer 4: computed router gate-score relation. -/
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

private def g4l4PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5182], outs := [8496], params := [0] }
private def g4l4PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5182], outs := [8497], params := [0] }
private def g4l4SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5182],
    outs := [5183, 5184, 5185], params := [8, 1] }
private def g4l4PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8496],
    outs := [8498, 8500, 8502], params := [8, 1] }
private def g4l4PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8497],
    outs := [8499, 8501, 8503], params := [8, 1] }

private theorem g4l4_nodes :
    sm_goal_4.nodes[183]'(by native_decide) = g4l4SmTopk ∧
    pm_goal_4.nodes[428]'(by native_decide) = g4l4PmChunk0 ∧
    pm_goal_4.nodes[429]'(by native_decide) = g4l4PmChunk1 ∧
    pm_goal_4.nodes[433]'(by native_decide) = g4l4PmTopk0 ∧
    pm_goal_4.nodes[434]'(by native_decide) = g4l4PmTopk1 := by
  native_decide

private theorem g4l4_sm_nonempty (k : Nat)
    (h : k = 183 ∨ k = 184) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l4_pm_nonempty (k : Nat)
    (h : k = 428 ∨ k = 429 ∨ k = 430 ∨ k = 433 ∨ k = 434 ∨ k = 435) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l4_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(184, 5185), (183, 5182)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l4_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(429, 8496), (430, 8497), (428, 5182), (429, 5182),
      (434, 8502), (435, 8503), (433, 8496), (434, 8497)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l4_red_pm8496 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8496 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5182) := by
  let pre := (pm_goal_4.nodes.take 428).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 428
    g4l4PmChunk0 8496 (by native_decide) g4l4_nodes.2.1
    (g4l4_pm_nonempty 429 (by decide))
    (g4l4_pm_not_written 429 8496 (by decide))
  have hread : pre 5182 = denoteGraphDistributedFaithful pm_goal_4 initPM 5182 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 428 5182
      (g4l4_pm_nonempty 428 (by decide)) (g4l4_pm_not_written 428 5182 (by decide))
  rw [hcore]
  unfold g4l4PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5182) = _
  rw [hread]

theorem g4l4_red_pm8497 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8497 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5182) := by
  let pre := (pm_goal_4.nodes.take 429).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 429
    g4l4PmChunk1 8497 (by native_decide) g4l4_nodes.2.2.1
    (g4l4_pm_nonempty 430 (by decide))
    (g4l4_pm_not_written 430 8497 (by decide))
  have hread : pre 5182 = denoteGraphDistributedFaithful pm_goal_4 initPM 5182 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 429 5182
      (g4l4_pm_nonempty 429 (by decide)) (g4l4_pm_not_written 429 5182 (by decide))
  rw [hcore]
  unfold g4l4PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5182) = _
  rw [hread]

theorem g4l4_red_sm5185 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5182).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5185 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5182) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 183).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 183
    g4l4SmTopk 5185 (by native_decide) g4l4_nodes.1
    (g4l4_sm_nonempty 184 (by decide))
    (g4l4_sm_not_written 184 5185 (by decide))
  have hread : pre 5182 = denoteGraphDistributedFaithful sm_goal_4 initSM 5182 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 183 5182
      (g4l4_sm_nonempty 183 (by decide)) (g4l4_sm_not_written 183 5182 (by decide))
  rw [hcore]
  unfold g4l4SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5182) 8
    (((pre 5182).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l4_red_pm8502 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8496).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8502 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8496) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 433).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 433
    g4l4PmTopk0 8502 (by native_decide) g4l4_nodes.2.2.2.1
    (g4l4_pm_nonempty 434 (by decide))
    (g4l4_pm_not_written 434 8502 (by decide))
  have hread : pre 8496 = denoteGraphDistributedFaithful pm_goal_4 initPM 8496 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 433 8496
      (g4l4_pm_nonempty 433 (by decide)) (g4l4_pm_not_written 433 8496 (by decide))
  rw [hcore]
  unfold g4l4PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8496) 8
    (((pre 8496).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l4_red_pm8503 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8497).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8503 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8497) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 434).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 434
    g4l4PmTopk1 8503 (by native_decide) g4l4_nodes.2.2.2.2
    (g4l4_pm_nonempty 435 (by decide))
    (g4l4_pm_not_written 435 8503 (by decide))
  have hread : pre 8497 = denoteGraphDistributedFaithful pm_goal_4 initPM 8497 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 434 8497
      (g4l4_pm_nonempty 434 (by decide)) (g4l4_pm_not_written 434 8497 (by decide))
  rw [hcore]
  unfold g4l4PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8497) 8
    (((pre 8497).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-4 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l4_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5182)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8496)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8497)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5185)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8502)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8503)
      [4096, 64] [2048, 64] := by
  have hsm := g4l4_red_sm5185 initSM hrel.full_shape
  have hpm0 := g4l4_red_pm8502 initPM hrel.rank0_shape
  have hpm1 := g4l4_red_pm8503 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8496)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8497)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5185 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5182) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 8496,
               denoteGraphDistributedFaithful pm_goal_4 initPM 8497]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8496) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8497) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 8502,
             denoteGraphDistributedFaithful pm_goal_4 initPM 8503] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5182) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8496) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8497) hrel.rank1_shape)

#print axioms canonical_goal4_l4_gate_scores

end
end TrainVerify.Denote.GeneratedPatterns

