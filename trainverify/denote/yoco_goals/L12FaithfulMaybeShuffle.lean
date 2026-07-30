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
      n.op ≠ "OpName.FW_maybe_shuffle" ∧ n.op ≠ "OpName.FW_maybe_unshuffle" ∧
        n.op ≠ "OpName.FW_attn_zigzag") ∧
    (∀ n ∈ sm.nodes.drop 472, n.outs ≠ []) ∧
    (∀ n ∈ sm.nodes.drop 472, 5330 ∉ n.outs ∧ 8011 ∉ n.outs ∧ 5337 ∉ n.outs) := by
  native_decide

private theorem l12_pm_pre_shuffle_facts :
    (∀ n ∈ pm.nodes.take 1003,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧ n.op ≠ "OpName.FW_maybe_unshuffle" ∧
        n.op ≠ "OpName.FW_attn_zigzag") ∧
    (∀ n ∈ pm.nodes.drop 1003, n.outs ≠ []) ∧
    (∀ n ∈ pm.nodes.drop 1003,
      9625 ∉ n.outs ∧ 9626 ∉ n.outs ∧ 13257 ∉ n.outs ∧
      13258 ∉ n.outs ∧ 5337 ∉ n.outs) := by
  native_decide

private theorem l12_pm_shuffle_outputs_final :
    (∀ n ∈ pm.nodes.drop 1004, 9655 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1006, 9656 ∉ n.outs) := by
  native_decide

-- Graph facts for the faithful 5338 -> 5340 RMSNorm continuation.  Keeping these
-- scans out of the proof avoids repeating large generated-graph reductions.
set_option maxRecDepth 1000000 in
private theorem l12_sm_5340_graph_facts :
    sm.nodes[474]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5338],
        outs := [8139, 8143], params := [2] } ∧
    (∀ n ∈ sm.nodes.drop 475, 8139 ∉ n.outs) ∧
    (∀ n ∈ sm.nodes.drop 474, 5338 ∉ n.outs) ∧
    sm.nodes[477]'(by native_decide) =
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8139, 5339], outs := [5340] } ∧
    (∀ n ∈ sm.nodes.drop 478, 5340 ∉ n.outs) ∧
    (∀ n ∈ sm.nodes.drop 477, 8139 ∉ n.outs) ∧
    (∀ n ∈ sm.nodes.drop 477, 5339 ∉ n.outs) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_pm_5340_graph_facts :
    pm.nodes[1006]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [9655],
        outs := [15969, 15973], params := [2] } ∧
    (∀ n ∈ pm.nodes.drop 1007, 15969 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1006, 9655 ∉ n.outs) ∧
    pm.nodes[1009]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [9656],
        outs := [15977, 15981], params := [2] } ∧
    (∀ n ∈ pm.nodes.drop 1010, 15977 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1009, 9656 ∉ n.outs) ∧
    pm.nodes[1010]'(by native_decide) =
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15969, 5339], outs := [9657] } ∧
    (∀ n ∈ pm.nodes.drop 1011, 9657 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1010, 15969 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1010, 5339 ∉ n.outs) ∧
    pm.nodes[1013]'(by native_decide) =
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15977, 5339], outs := [9658] } ∧
    (∀ n ∈ pm.nodes.drop 1014, 9658 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1013, 15977 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1013, 5339 ∉ n.outs) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_weight5339_not_written :
    (∀ n ∈ sm.nodes, 5339 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5339 ∉ n.outs) := by
  native_decide

-- Hoisted generated-graph facts for the faithful 5342 per-head continuation.
set_option maxRecDepth 1000000 in
private theorem l12_sm_5342_graph_facts :
    sm.nodes[480]'(by native_decide) =
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [5340, 5341], outs := [5342] } ∧
    (∀ n ∈ sm.nodes.drop 481, 5342 ∉ n.outs) ∧
    (∀ n ∈ sm.nodes.drop 480, 5340 ∉ n.outs) ∧
    (∀ n ∈ sm.nodes.drop 480, 5341 ∉ n.outs) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_pm_5342_graph_facts :
    pm.nodes[1014]'(by native_decide) =
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [9657, 5341], outs := [9659] } ∧
    (∀ n ∈ pm.nodes.drop 1015, 9659 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1014, 9657 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1014, 5341 ∉ n.outs) ∧
    pm.nodes[1019]'(by native_decide) =
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [9658, 5341], outs := [9660] } ∧
    (∀ n ∈ pm.nodes.drop 1020, 9660 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1019, 9658 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.drop 1019, 5341 ∉ n.outs) := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_weight5341_not_written :
    (∀ n ∈ sm.nodes, 5341 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5341 ∉ n.outs) := by
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
theorem recon_zigzagGoal_5338_faithful (initSM initPM : Store)
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

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful generated goal 5340: row-local RMSNorm preserves the zigzag layout
relation established at 5338. -/
theorem recon_zigzagGoal_5340_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5340)
      (denoteGraphDistributedFaithful pm initPM 9657)
      (denoteGraphDistributedFaithful pm initPM 9658)
      (denoteGraphDistributedFaithful pm initPM 5337)
      [4096, 1024] [2048, 1024] := by
  have h38 := recon_zigzagGoal_5338_faithful initSM initPM hSM hPM hInit hCu
  have hsnil (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
    intro n hn
    exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)
  have hpnil (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
    intro n hn
    exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)
  rcases l12_sm_5340_graph_facts with
    ⟨sn0, sout0, sin0, sr0, srout, srin0, srw⟩
  rcases l12_pm_5340_graph_facts with
    ⟨pn0, pout0, pin0, pn1, pout1, pin1,
      pr0, prout0, prin0, prw0, pr1, prout1, prin1, prw1⟩
  have s8139 : denoteGraphDistributedFaithful sm initSM 8139 =
      denoteGraphDistributedFaithful sm initSM 5338 := by
    have h := denoteGraphDistributedFaithful_reduce1 sm initSM 474
      { rank := 0, op := "OpName.FW_multiref", ins := [5338],
        outs := [8139, 8143], params := [2] }
      5338 8139 id (by native_decide) sn0 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out sm s 0 5338 8139 8143)
      (hsnil 475) sout0 (hsnil 474) sin0
    simpa only [id_eq] using h
  have p15969 : denoteGraphDistributedFaithful pm initPM 15969 =
      denoteGraphDistributedFaithful pm initPM 9655 := by
    have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1006
      { rank := 0, op := "OpName.FW_multiref", ins := [9655],
        outs := [15969, 15973], params := [2] }
      9655 15969 id (by native_decide) pn0 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out pm s 0 9655 15969 15973)
      (hpnil 1007) pout0 (hpnil 1006) pin0
    simpa only [id_eq] using h
  have p15977 : denoteGraphDistributedFaithful pm initPM 15977 =
      denoteGraphDistributedFaithful pm initPM 9656 := by
    have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1009
      { rank := 1, op := "OpName.FW_multiref", ins := [9656],
        outs := [15977, 15981], params := [2] }
      9656 15977 id (by native_decide) pn1 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out pm s 1 9656 15977 15981)
      (hpnil 1010) pout1 (hpnil 1009) pin1
    simpa only [id_eq] using h
  have rSM : denoteGraphDistributedFaithful sm initSM 5340 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8139)
        (denoteGraphDistributedFaithful sm initSM 5339) := by
    exact denoteGraphDistributedFaithful_reduce2 sm initSM 477
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8139, 5339], outs := [5340] }
      8139 5339 5340 fw_rms_norm (by native_decide) sr0 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_rms_norm_out_1p sm s 0 8139 5339 5340)
      (hsnil 478) srout (hsnil 477) srin0 srw
  have rP0 : denoteGraphDistributedFaithful pm initPM 9657 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 15969)
        (denoteGraphDistributedFaithful pm initPM 5339) := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1010
      { rank := 0, op := "OpName.FW_rms_norm", ins := [15969, 5339], outs := [9657] }
      15969 5339 9657 fw_rms_norm (by native_decide) pr0 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_rms_norm_out_1p pm s 0 15969 5339 9657)
      (hpnil 1011) prout0 (hpnil 1010) prin0 prw0
  have rP1 : denoteGraphDistributedFaithful pm initPM 9658 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 15977)
        (denoteGraphDistributedFaithful pm initPM 5339) := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1013
      { rank := 1, op := "OpName.FW_rms_norm", ins := [15977, 5339], outs := [9658] }
      15977 5339 9658 fw_rms_norm (by native_decide) pr1 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_rms_norm_out_1p pm s 1 15977 5339 9658)
      (hpnil 1014) prout1 (hpnil 1013) prin1 prw1
  have hwInit : initSM 5339 = initPM 5339 :=
    recon_weight initSM initPM hInit initGoal_5339 (by native_decide) 5339
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5339 = initSM 5339 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5339
      layer1_sm_nodes_nonempty l12_weight5339_not_written.1
  have hpw : denoteGraphDistributedFaithful pm initPM 5339 = initPM 5339 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5339
      layer1_pm_nodes_nonempty l12_weight5339_not_written.2
  have hw : denoteGraphDistributedFaithful sm initSM 5339 =
      denoteGraphDistributedFaithful pm initPM 5339 := by
    rw [hsw, hpw]
    exact hwInit
  rw [rSM, rP0, rP1, s8139, p15969, p15977, hw]
  exact Zigzag2Rel.rms_norm 2048 1024 h38 (by decide) (by decide) rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful generated goal 5342: a replicated Q weight transports the zigzag
relation through the row-local per-head linear operation. -/
theorem recon_zigzagGoal_5342_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5342)
      (denoteGraphDistributedFaithful pm initPM 9659)
      (denoteGraphDistributedFaithful pm initPM 9660)
      (denoteGraphDistributedFaithful pm initPM 5337)
      [4096, 16, 64] [2048, 16, 64] := by
  have h40 := recon_zigzagGoal_5340_faithful initSM initPM hSM hPM hInit hCu
  have hsnil (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
    intro n hn
    exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)
  have hpnil (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
    intro n hn
    exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)
  rcases l12_sm_5342_graph_facts with ⟨sn, sout, sin, sw⟩
  rcases l12_pm_5342_graph_facts with ⟨pn0, pout0, pin0, pw0,
    pn1, pout1, pin1, pw1⟩
  have rSM : denoteGraphDistributedFaithful sm initSM 5342 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 5340)
        (denoteGraphDistributedFaithful sm initSM 5341) := by
    exact denoteGraphDistributedFaithful_reduce2 sm initSM 480
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [5340, 5341], outs := [5342] }
      5340 5341 5342 fw_per_head_linear (by native_decide) sn (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 5340 5341 5342 [])
      (hsnil 481) sout (hsnil 480) sin sw
  have rP0 : denoteGraphDistributedFaithful pm initPM 9659 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 9657)
        (denoteGraphDistributedFaithful pm initPM 5341) := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1014
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [9657, 5341], outs := [9659] }
      9657 5341 9659 fw_per_head_linear (by native_decide) pn0 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_per_head_mix_precision_linear_out pm s 0 9657 5341 9659 [])
      (hpnil 1015) pout0 (hpnil 1014) pin0 pw0
  have rP1 : denoteGraphDistributedFaithful pm initPM 9660 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 9658)
        (denoteGraphDistributedFaithful pm initPM 5341) := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1019
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [9658, 5341], outs := [9660] }
      9658 5341 9660 fw_per_head_linear (by native_decide) pn1 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 9658 5341 9660 [])
      (hpnil 1020) pout1 (hpnil 1019) pin1 pw1
  have hwInit : initSM 5341 = initPM 5341 :=
    recon_weight initSM initPM hInit initGoal_5341 (by native_decide) 5341
      rfl rfl rfl rfl
  have hsw : denoteGraphDistributedFaithful sm initSM 5341 = initSM 5341 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 5341
      layer1_sm_nodes_nonempty l12_weight5341_not_written.1
  have hpw : denoteGraphDistributedFaithful pm initPM 5341 = initPM 5341 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 5341
      layer1_pm_nodes_nonempty l12_weight5341_not_written.2
  have hw : denoteGraphDistributedFaithful sm initSM 5341 =
      denoteGraphDistributedFaithful pm initPM 5341 := by
    rw [hsw, hpw]
    exact hwInit
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5341).shape =
      [16, 64, 1024] := by
    rw [hpw]
    exact hPM 5341 [16, 64, 1024] (by native_decide)
  rw [rSM, rP0, rP1, hw]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 h40 hwShape
    (by decide) (by decide) (by decide) (by decide)

/-! Compatibility aliases for older downstream modules. -/

abbrev recon_zigzagGoal_5338_distributed := recon_zigzagGoal_5338_faithful

abbrev recon_zigzagGoal_5340_distributed := recon_zigzagGoal_5340_faithful

abbrev recon_zigzagGoal_5342_distributed := recon_zigzagGoal_5342_faithful

end
end TrainVerify.Denote.GeneratedPatterns
