/- Canonical Goal 4, layer 0: computed router gate-score relation. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

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

end
end TrainVerify.Denote.GeneratedPatterns
