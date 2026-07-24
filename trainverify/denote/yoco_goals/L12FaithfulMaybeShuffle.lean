import denote.yoco_goals.Layer12DistributedBoundaryContinuation
import denote.yoco_goals.ZigzagLayoutRel
import denote.DenoteDistributedFaithful

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def l12SmShuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_shuffle",
    ins := [8011, 5337], outs := [5338], params := [1, 0] }
private def l12PmShuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_shuffle",
    ins := [13257, 5337], outs := [9655], params := [2, 0] }
private def l12PmShuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_shuffle",
    ins := [13258, 5337], outs := [9656], params := [2, 1] }

set_option maxRecDepth 1000000 in
private theorem l12_sm_node472 : sm.nodes[472]'(by native_decide) = l12SmShuffle := by
  native_decide
set_option maxRecDepth 1000000 in
private theorem l12_pm_node1003 : pm.nodes[1003]'(by native_decide) = l12PmShuffle0 := by
  native_decide
set_option maxRecDepth 1000000 in
private theorem l12_pm_node1005 : pm.nodes[1005]'(by native_decide) = l12PmShuffle1 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_sm_shuffle_buddies :
    sm.replicaBuddies l12SmShuffle = [l12SmShuffle] := by native_decide
set_option maxRecDepth 1000000 in
private theorem l12_pm_shuffle0_buddies :
    pm.replicaBuddies l12PmShuffle0 = [l12PmShuffle0, l12PmShuffle1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem l12_pm_shuffle1_buddies :
    pm.replicaBuddies l12PmShuffle1 = [l12PmShuffle0, l12PmShuffle1] := by native_decide

private theorem l12_sm_pre_shuffle_facts :
    (∀ n ∈ sm.nodes.take 472,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧ n.op ≠ "OpName.FW_maybe_unshuffle") ∧
    (∀ n ∈ sm.nodes.drop 472, n.outs ≠ []) ∧
    (∀ n ∈ sm.nodes.drop 472, 5330 ∉ n.outs ∧ 8011 ∉ n.outs ∧ 5337 ∉ n.outs) := by
  native_decide

private theorem l12_pm_pre_shuffle_facts :
    (∀ n ∈ pm.nodes.take 1003,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧ n.op ≠ "OpName.FW_maybe_unshuffle") ∧
    (∀ n ∈ pm.nodes.drop 1003, n.outs ≠ []) ∧
    (∀ n ∈ pm.nodes.drop 1003,
      9625 ∉ n.outs ∧ 9626 ∉ n.outs ∧ 13257 ∉ n.outs ∧
      13258 ∉ n.outs ∧ 5337 ∉ n.outs) := by
  native_decide

private theorem l12_pm_shuffle_outputs_final :
    (∀ n ∈ pm.nodes.drop 1004, 9655 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1006, 9656 ∉ n.outs) := by
  native_decide

-- Keep the large graph-membership decisions shared instead of recompiling the
-- same suffix scans at every argument of `distributed_reduce1`.
set_option maxRecDepth 1000000 in
private theorem l12_sm_multiref_facts :
    470 < sm.nodes.length ∧
    sm.nodes[470]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5330],
        outs := [8007, 8011], params := [2] } ∧
    (∀ n ∈ sm.nodes.drop 471, n.outs ≠ []) ∧
    (∀ n ∈ sm.nodes.drop 471, 8011 ∉ n.outs) ∧
    (∀ n ∈ sm.nodes.drop 470, n.outs ≠ []) ∧
    (∀ n ∈ sm.nodes.drop 470, 5330 ∉ n.outs) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_pm_multiref0_facts :
    1001 < pm.nodes.length ∧
    pm.nodes[1001]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [9625],
        outs := [14597, 13257], params := [2] } ∧
    (∀ n ∈ pm.nodes.drop 1002, n.outs ≠ []) ∧
    (∀ n ∈ pm.nodes.drop 1002, 13257 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1001, n.outs ≠ []) ∧
    (∀ n ∈ pm.nodes.drop 1001, 9625 ∉ n.outs) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_pm_multiref1_facts :
    1002 < pm.nodes.length ∧
    pm.nodes[1002]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [9626],
        outs := [14599, 13258], params := [2] } ∧
    (∀ n ∈ pm.nodes.drop 1003, n.outs ≠ []) ∧
    (∀ n ∈ pm.nodes.drop 1003, 13258 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1002, n.outs ≠ []) ∧
    (∀ n ∈ pm.nodes.drop 1002, 9626 ∉ n.outs) := by
  native_decide

private theorem l12_sm_bridges (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5330 = denoteGraphDistributed sm initSM 5330 ∧
    denoteGraphDistributedFaithful sm initSM 8011 = denoteGraphDistributed sm initSM 8011 ∧
    denoteGraphDistributedFaithful sm initSM 5337 = denoteGraphDistributed sm initSM 5337 := by
  have h := l12_sm_pre_shuffle_facts
  refine ⟨?_, ?_, ?_⟩
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix sm initSM 5330 472
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix sm initSM 8011 472
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix sm initSM 5337 472
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).2.2)

private theorem l12_pm_bridges (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9625 = denoteGraphDistributed pm initPM 9625 ∧
    denoteGraphDistributedFaithful pm initPM 9626 = denoteGraphDistributed pm initPM 9626 ∧
    denoteGraphDistributedFaithful pm initPM 13257 = denoteGraphDistributed pm initPM 13257 ∧
    denoteGraphDistributedFaithful pm initPM 13258 = denoteGraphDistributed pm initPM 13258 ∧
    denoteGraphDistributedFaithful pm initPM 5337 = denoteGraphDistributed pm initPM 5337 := by
  have h := l12_pm_pre_shuffle_facts
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix pm initPM 9625 1003
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix pm initPM 9626 1003
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix pm initPM 13257 1003
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).2.2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix pm initPM 13258 1003
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).2.2.2.1)
  · exact denoteGraphDistributedFaithful_eq_distributed_of_prefix pm initPM 5337 1003
      h.1 h.2.1 (fun n hn => (h.2.2 n hn).2.2.2.2)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful source-witness reconstruction of generated L12 `maybe_shuffle` goal 5338.
The explicit `ZigzagCuWF` premise is the metadata contract required by the faithful
collective semantics; no ordinary gather claim is made about the shuffled outputs. -/
theorem recon_zigzagGoal_5338_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5338)
      (denoteGraphDistributedFaithful pm initPM 9655)
      (denoteGraphDistributedFaithful pm initPM 9656)
      (denoteGraphDistributedFaithful pm initPM 5337)
      [4096, 1024] [2048, 1024] := by
  have h30 := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5330 5330 9625 9626
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5330_distributed initSM initPM hSM hPM hInit)
  have sf := l12_sm_multiref_facts
  have pf0 := l12_pm_multiref0_facts
  have pf1 := l12_pm_multiref1_facts
  have s8011 := distributed_reduce1 sm initSM 470
    { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] }
    5330 8011 id sf.1 sf.2.1 (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5330 8007 8011 (by decide))
    sf.2.2.1 sf.2.2.2.1 sf.2.2.2.2.1 sf.2.2.2.2.2
  have p13257 := distributed_reduce1 pm initPM 1001
    { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] }
    9625 13257 id pf0.1 pf0.2.1 (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 9625 14597 13257 (by decide))
    pf0.2.2.1 pf0.2.2.2.1 pf0.2.2.2.2.1 pf0.2.2.2.2.2
  have p13258 := distributed_reduce1 pm initPM 1002
    { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] }
    9626 13258 id pf1.1 pf1.2.1 (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 9626 14599 13258 (by decide))
    pf1.2.2.1 pf1.2.2.2.1 pf1.2.2.2.2.1 pf1.2.2.2.2.2
  simp only [id_eq] at s8011 p13257 p13258
  have hsbr := l12_sm_bridges initSM
  have hpbr := l12_pm_bridges initPM
  have hpre := l12_pm_pre_shuffle_facts
  have hout := l12_pm_shuffle_outputs_final
  have hnil (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
    intro n hn
    exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)
  have h13257_1005 : ∀ n ∈ pm.nodes.drop 1005, 13257 ∉ n.outs := by
    intro n hn
    exact (hpre.2.2 n (List.mem_of_mem_drop (i := 2) (by
      simpa only [List.drop_drop, Nat.reduceAdd] using hn))).2.2.1
  have h13258_1005 : ∀ n ∈ pm.nodes.drop 1005, 13258 ∉ n.outs := by
    intro n hn
    exact (hpre.2.2 n (List.mem_of_mem_drop (i := 2) (by
      simpa only [List.drop_drop, Nat.reduceAdd] using hn))).2.2.2.1
  have h5337_1005 : ∀ n ∈ pm.nodes.drop 1005, 5337 ∉ n.outs := by
    intro n hn
    exact (hpre.2.2 n (List.mem_of_mem_drop (i := 2) (by
      simpa only [List.drop_drop, Nat.reduceAdd] using hn))).2.2.2.2
  have hsm : denoteGraphDistributedFaithful sm initSM 5338 =
      denoteGraphDistributedFaithful sm initSM 8011 := by
    rw [denoteGraphDistributedFaithful_node_core sm initSM 472 l12SmShuffle 5338
      (by native_decide) l12_sm_node472 (by native_decide) (by native_decide)]
    unfold l12SmShuffle
    rw [applyNodeDistributedFaithful_shuffle_out]
    rw [← denoteGraphDistributedFaithful_prefix_read sm initSM 472 8011
      l12_sm_pre_shuffle_facts.2.1
      (fun n hn => (l12_sm_pre_shuffle_facts.2.2 n hn).2.1)]
    apply applyNodeFaithfulShuffleValue_cpSize_one
    · exact l12_sm_shuffle_buddies
    · rfl
    · rfl
  have hz0 : denoteGraphDistributedFaithful pm initPM 9655 =
      fw_maybe_shuffle_collective
        [denoteGraphDistributedFaithful pm initPM 13257,
         denoteGraphDistributedFaithful pm initPM 13258]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337)) 2 0 := by
    refine denoteGraphDistributedFaithful_reduce3 pm initPM 1003 l12PmShuffle0
      13257 13258 5337 9655
      (fun a b cu => fw_maybe_shuffle_collective [a, b] (decodeCuSeqlens cu) 2 0)
      (by native_decide) l12_pm_node1003 ?_
      (hnil 1004) hout.1 hpre.2.1
      (fun n hn => (hpre.2.2 n hn).2.2.1)
      (fun n hn => (hpre.2.2 n hn).2.2.2.1)
      (fun n hn => (hpre.2.2 n hn).2.2.2.2)
    intro st
    unfold l12PmShuffle0
    rw [applyNodeDistributedFaithful_shuffle_out]
    unfold applyNodeFaithfulShuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [13257, 5337],
        outs := [9655], params := [2, 0] } = [l12PmShuffle0, l12PmShuffle1] by
          exact l12_pm_shuffle0_buddies]
    unfold l12PmShuffle0 l12PmShuffle1
    rfl
  have hz1 : denoteGraphDistributedFaithful pm initPM 9656 =
      fw_maybe_shuffle_collective
        [denoteGraphDistributedFaithful pm initPM 13257,
         denoteGraphDistributedFaithful pm initPM 13258]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337)) 2 1 := by
    refine denoteGraphDistributedFaithful_reduce3 pm initPM 1005 l12PmShuffle1
      13257 13258 5337 9656
      (fun a b cu => fw_maybe_shuffle_collective [a, b] (decodeCuSeqlens cu) 2 1)
      (by native_decide) l12_pm_node1005 ?_
      (hnil 1006) hout.2 (hnil 1005) h13257_1005 h13258_1005 h5337_1005
    intro st
    unfold l12PmShuffle1
    rw [applyNodeDistributedFaithful_shuffle_out]
    unfold applyNodeFaithfulShuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [13258, 5337],
        outs := [9656], params := [2, 1] } = [l12PmShuffle0, l12PmShuffle1] by
          exact l12_pm_shuffle1_buddies]
    unfold l12PmShuffle0 l12PmShuffle1
    rfl
  apply Zigzag2Rel.of_sources
    (denoteGraphDistributedFaithful pm initPM 13257)
    (denoteGraphDistributedFaithful pm initPM 13258)
  · rw [hsm, hsbr.2.1, s8011, h30.value, hpbr.2.2.1, hpbr.2.2.2.1,
      p13257, p13258]
  · exact hz0
  · exact hz1
  · rw [hsm, hsbr.2.1, s8011]
    exact h30.full_shape
  · rw [hpbr.2.2.1, p13257]
    exact h30.shard0_shape
  · rw [hpbr.2.2.2.1, p13258]
    exact h30.shard1_shape
  · exact hCu

end
end TrainVerify.Denote.GeneratedPatterns
