/- Canonical Goal 4, layer 1: computed router gate-score relation. -/
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

private def g4l1PmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5017], outs := [8004], params := [0] }
private def g4l1PmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5017], outs := [8005], params := [0] }
private def g4l1SmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5017],
    outs := [5018, 5019, 5020], params := [8, 1] }
private def g4l1PmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [8004],
    outs := [8006, 8008, 8010], params := [8, 1] }
private def g4l1PmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [8005],
    outs := [8007, 8009, 8011], params := [8, 1] }

private theorem g4l1_nodes :
    sm_goal_4.nodes[66]'(by native_decide) = g4l1SmTopk ∧
    pm_goal_4.nodes[176]'(by native_decide) = g4l1PmChunk0 ∧
    pm_goal_4.nodes[177]'(by native_decide) = g4l1PmChunk1 ∧
    pm_goal_4.nodes[181]'(by native_decide) = g4l1PmTopk0 ∧
    pm_goal_4.nodes[182]'(by native_decide) = g4l1PmTopk1 := by
  native_decide

private theorem g4l1_sm_nonempty (k : Nat)
    (h : k = 66 ∨ k = 67) : ∀ n ∈ sm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl <;> native_decide

private theorem g4l1_pm_nonempty (k : Nat)
    (h : k = 176 ∨ k = 177 ∨ k = 178 ∨ k = 181 ∨ k = 182 ∨ k = 183) :
    ∀ n ∈ pm_goal_4.nodes.drop k, n.outs ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem g4l1_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(67, 5020), (66, 5017)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem g4l1_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(177, 8004), (178, 8005), (176, 5017), (177, 5017),
      (182, 8010), (183, 8011), (181, 8004), (182, 8005)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

theorem g4l1_red_pm8004 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8004 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_4 initPM 5017) := by
  let pre := (pm_goal_4.nodes.take 176).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 176
    g4l1PmChunk0 8004 (by native_decide) g4l1_nodes.2.1
    (g4l1_pm_nonempty 177 (by decide))
    (g4l1_pm_not_written 177 8004 (by decide))
  have hread : pre 5017 = denoteGraphDistributedFaithful pm_goal_4 initPM 5017 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 176 5017
      (g4l1_pm_nonempty 176 (by decide)) (g4l1_pm_not_written 176 5017 (by decide))
  rw [hcore]
  unfold g4l1PmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 0 (pre 5017) = _
  rw [hread]

theorem g4l1_red_pm8005 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8005 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_4 initPM 5017) := by
  let pre := (pm_goal_4.nodes.take 177).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 177
    g4l1PmChunk1 8005 (by native_decide) g4l1_nodes.2.2.1
    (g4l1_pm_nonempty 178 (by decide))
    (g4l1_pm_not_written 178 8005 (by decide))
  have hread : pre 5017 = denoteGraphDistributedFaithful pm_goal_4 initPM 5017 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 177 5017
      (g4l1_pm_nonempty 177 (by decide)) (g4l1_pm_not_written 177 5017 (by decide))
  rw [hcore]
  unfold g4l1PmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_chunkPrimDimN_out]
  change chunkPrimDimN 0 2 1 (pre 5017) = _
  rw [hread]

theorem g4l1_red_sm5020 (initSM : Store)
    (hshape : (denoteGraphDistributedFaithful sm_goal_4 initSM 5017).shape = [4096, 64]) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5020 =
      (fw_topk_routing (denoteGraphDistributedFaithful sm_goal_4 initSM 5017) 8 64).2.2 := by
  let pre := (sm_goal_4.nodes.take 66).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore := denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 66
    g4l1SmTopk 5020 (by native_decide) g4l1_nodes.1
    (g4l1_sm_nonempty 67 (by decide))
    (g4l1_sm_not_written 67 5020 (by decide))
  have hread : pre 5017 = denoteGraphDistributedFaithful sm_goal_4 initSM 5017 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 66 5017
      (g4l1_sm_nonempty 66 (by decide)) (g4l1_sm_not_written 66 5017 (by decide))
  rw [hcore]
  unfold g4l1SmTopk
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 5017) 8
    (((pre 5017).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l1_red_pm8010 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8004).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8010 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8004) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 181).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 181
    g4l1PmTopk0 8010 (by native_decide) g4l1_nodes.2.2.2.1
    (g4l1_pm_nonempty 182 (by decide))
    (g4l1_pm_not_written 182 8010 (by decide))
  have hread : pre 8004 = denoteGraphDistributedFaithful pm_goal_4 initPM 8004 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 181 8004
      (g4l1_pm_nonempty 181 (by decide)) (g4l1_pm_not_written 181 8004 (by decide))
  rw [hcore]
  unfold g4l1PmTopk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8004) 8
    (((pre 8004).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

theorem g4l1_red_pm8011 (initPM : Store)
    (hshape : (denoteGraphDistributedFaithful pm_goal_4 initPM 8005).shape = [2048, 64]) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 8011 =
      (fw_topk_routing (denoteGraphDistributedFaithful pm_goal_4 initPM 8005) 8 64).2.2 := by
  let pre := (pm_goal_4.nodes.take 182).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  have hcore := denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 182
    g4l1PmTopk1 8011 (by native_decide) g4l1_nodes.2.2.2.2
    (g4l1_pm_nonempty 183 (by decide))
    (g4l1_pm_not_written 183 8011 (by decide))
  have hread : pre 8005 = denoteGraphDistributedFaithful pm_goal_4 initPM 8005 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 182 8005
      (g4l1_pm_nonempty 182 (by decide)) (g4l1_pm_not_written 182 8005 (by decide))
  rw [hcore]
  unfold g4l1PmTopk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      _ _ _ (by decide) (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_fw_topk_routing_scores_out _ _ _ _ _ _ _ _ (by decide) (by decide)]
  change (fw_topk_routing (pre 8005) 8
    (((pre 8005).shape.reverse.head?).getD 1)).2.2 = _
  rw [hread, hshape]
  rfl

/-- The canonical layer-1 gate scores preserve the ordinary two-rank token
layout.  The source relation is an internal layer-to-layer premise; the graph
reductions compute all three target tensors. -/
theorem canonical_goal4_l1_gate_scores
    (initSM initPM : Store)
    (hrel : Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5017)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8004)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8005)
      [4096, 64] [2048, 64]) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5020)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8010)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 8011)
      [4096, 64] [2048, 64] := by
  have hsm := g4l1_red_sm5020 initSM hrel.full_shape
  have hpm0 := g4l1_red_pm8010 initPM hrel.rank0_shape
  have hpm1 := g4l1_red_pm8011 initPM hrel.rank1_shape
  have hcommute := fw_topk_routing_gate_scores_allGather0_commute_2
    2048 64 8 (by decide) (by decide)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8004)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 8005)
    hrel.rank0_shape hrel.rank1_shape
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · calc
      denoteGraphDistributedFaithful sm_goal_4 initSM 5020 =
          (fw_topk_routing
            (denoteGraphDistributedFaithful sm_goal_4 initSM 5017) 8 64).2.2 := hsm
      _ = (fw_topk_routing
            (allGatherPrimDimN 0 2 0
              [denoteGraphDistributedFaithful pm_goal_4 initPM 8004,
               denoteGraphDistributedFaithful pm_goal_4 initPM 8005]) 8 64).2.2 :=
        congrArg (fun x => (fw_topk_routing x 8 64).2.2) hrel.full_value
      _ = allGatherPrimDimN 0 2 0
            [(fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8004) 8 64).2.2,
             (fw_topk_routing
              (denoteGraphDistributedFaithful pm_goal_4 initPM 8005) 8 64).2.2] := hcommute
      _ = allGatherPrimDimN 0 2 0
            [denoteGraphDistributedFaithful pm_goal_4 initPM 8010,
             denoteGraphDistributedFaithful pm_goal_4 initPM 8011] :=
        congrArg (allGatherPrimDimN 0 2 0) (by rw [hpm0, hpm1])
  · exact (congrArg Tensor.shape hsm).trans
      (RowLocalShape_topk_thd 64 8 4096
        (denoteGraphDistributedFaithful sm_goal_4 initSM 5017) hrel.full_shape)
  · exact (congrArg Tensor.shape hpm0).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8004) hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans
      (RowLocalShape_topk_thd 64 8 2048
        (denoteGraphDistributedFaithful pm_goal_4 initPM 8005) hrel.rank1_shape)

end
end TrainVerify.Denote.GeneratedPatterns
