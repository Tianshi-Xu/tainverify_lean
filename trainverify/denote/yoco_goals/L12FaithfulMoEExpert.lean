/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulMoEBranch
import denote.yoco_goals.ZigzagMoEGmmRel

/-!
# Faithful zigzag relation for the MoE expert layer (goal 5365)

* SM node 527 `FW_all2all_moe_gmm [8162, 5360, 5361, 5363, 5364] → [5365]`,
  params `[64, 0, 64, 8]`
* PM node 1116 (rank 0) `[16008, 9731, 9733, 9737, 9739] → [9741]`, params `[64, 0, 32, 8]`
* PM node 1119 (rank 1) `[16031, 9732, 9734, 9738, 9740] → [9742]`, params `[64, 32, 64, 8]`

The faithful evaluator routes `FW_all2all_moe_gmm` through
`applyNodeFullExpertMoE_value`, which *gathers* the per-rank expert weight shards
declared by `GraphDecl.replicaBuddies` and evaluates
`fw_all2all_moe_gmm_full`, i.e. `fw_all2all_moe_gmm` over the **full** expert
range `start = 0, end = numExp`.  On the PM side the buddy list resolves to both
ranks, so both PM outputs use the same gathered `w13`/`w2`; on the SM side the
buddy list is the singleton and the gather collapses.  The init-goal bridge for
`5363` / `5364` identifies the SM weights with exactly that PM gather, so both
sides are literally the same full-range operator and the plain
`Zigzag2Rel.all2all_moe_gmm` applies — no routing-map disjointness contract is
needed.

No new hypotheses: the theorem takes literally the same five parameters as its
parents.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-! ### Local reduction helpers -/

private theorem denoteGraphDistributedFaithful_reduce5'
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4]

/-- Seven-read reduction: the faithful MoE evaluator reads the node's five
declared inputs *plus* the buddy rank's two expert-weight shards. -/
private theorem denoteGraphDistributedFaithful_reduce7
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 in5 in6 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4) (s in5) (s in6))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs)
    (hpre5 : ∀ n ∈ g.nodes.drop k, in5 ∉ n.outs)
    (hpre6 : ∀ n ∈ g.nodes.drop k, in6 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4)
        (denoteGraphDistributedFaithful g init in5)
        (denoteGraphDistributedFaithful g init in6) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4,
    denoteGraphDistributedFaithful_prefix_read g init k in5 hpreNil hpre5,
    denoteGraphDistributedFaithful_prefix_read g init k in6 hpreNil hpre6]

/-! ### Node literals -/

private def l12meSmMoE : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [8162, 5360, 5361, 5363, 5364], outs := [5365], params := [64, 0, 64, 8] }
private def l12mePmMoE0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [16008, 9731, 9733, 9737, 9739], outs := [9741], params := [64, 0, 32, 8] }
private def l12mePmMoE1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [16031, 9732, 9734, 9738, 9740], outs := [9742], params := [64, 32, 64, 8] }

/-! ### Certified node indices and replica metadata -/

set_option maxRecDepth 1000000 in
private theorem l12me_node_facts :
    sm.nodes[527]'(by native_decide) = l12meSmMoE ∧
    pm.nodes[1116]'(by native_decide) = l12mePmMoE0 ∧
    pm.nodes[1119]'(by native_decide) = l12mePmMoE1 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12me_buddy_facts :
    sm.replicaBuddies l12meSmMoE = [l12meSmMoE] ∧
    pm.replicaBuddies l12mePmMoE0 = [l12mePmMoE0, l12mePmMoE1] ∧
    pm.replicaBuddies l12mePmMoE1 = [l12mePmMoE0, l12mePmMoE1] := by
  native_decide

private theorem l12me_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l12me_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12me_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(528, 5365), (527, 8162), (527, 5360), (527, 5361),
      (527, 5363), (527, 5364)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12me_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1117, 9741), (1116, 16008), (1116, 9731), (1116, 9733),
      (1116, 9737), (1116, 9739), (1116, 9738), (1116, 9740),
      (1120, 9742), (1119, 16031), (1119, 9732), (1119, 9734),
      (1119, 9737), (1119, 9739), (1119, 9738), (1119, 9740)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12me_sm_leaf_not_written (tid : Nat)
    (h : tid ∈ [5363, 5364]) : ∀ n ∈ sm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12me_pm_leaf_not_written (tid : Nat)
    (h : tid ∈ [9737, 9738, 9739, 9740, 5345]) : ∀ n ∈ pm.nodes, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> native_decide +revert

/-! ### Leaf reads -/

private theorem l12me_sm_leaf (initSM : Store) (tid : Nat) (h : tid ∈ [5363, 5364]) :
    denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
    layer1_sm_nodes_nonempty (l12me_sm_leaf_not_written tid h)

private theorem l12me_pm_leaf (initPM : Store) (tid : Nat)
    (h : tid ∈ [9737, 9738, 9739, 9740, 5345]) :
    denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
    layer1_pm_nodes_nonempty (l12me_pm_leaf_not_written tid h)

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12me_red_sm5365 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5365 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful sm initSM 8162)
        (denoteGraphDistributedFaithful sm initSM 5360)
        (denoteGraphDistributedFaithful sm initSM 5361)
        [denoteGraphDistributedFaithful sm initSM 5363]
        [denoteGraphDistributedFaithful sm initSM 5364]
        64 8 (((10 : Nat) : Scalar)) := by
  refine denoteGraphDistributedFaithful_reduce5' sm initSM 527 l12meSmMoE
    8162 5360 5361 5363 5364 5365
    (fun x rp rm w13 w2 => fw_all2all_moe_gmm_full x rp rm [w13] [w2] 64 8
      (((10 : Nat) : Scalar)))
    (by native_decide) l12me_node_facts.1 ?_
    (l12me_nonempty_sm 528) (l12me_sm_not_written 528 5365 (by decide))
    (l12me_nonempty_sm 527) (l12me_sm_not_written 527 8162 (by decide))
    (l12me_sm_not_written 527 5360 (by decide))
    (l12me_sm_not_written 527 5361 (by decide))
    (l12me_sm_not_written 527 5363 (by decide))
    (l12me_sm_not_written 527 5364 (by decide))
  intro s
  have hb := l12me_buddy_facts.1
  unfold l12meSmMoE at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out sm s 0 8162 5360 5361 5363 5364 5365 [64, 0, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12me_red_pm9741 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9741 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16008)
        (denoteGraphDistributedFaithful pm initPM 9731)
        (denoteGraphDistributedFaithful pm initPM 9733)
        [denoteGraphDistributedFaithful pm initPM 9737,
         denoteGraphDistributedFaithful pm initPM 9738]
        [denoteGraphDistributedFaithful pm initPM 9739,
         denoteGraphDistributedFaithful pm initPM 9740]
        64 8 (((10 : Nat) : Scalar)) := by
  refine denoteGraphDistributedFaithful_reduce7 pm initPM 1116 l12mePmMoE0
    16008 9731 9733 9737 9739 9738 9740 9741
    (fun x rp rm w13a w2a w13b w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l12me_node_facts.2.1 ?_
    (l12me_nonempty_pm 1117) (l12me_pm_not_written 1117 9741 (by decide))
    (l12me_nonempty_pm 1116) (l12me_pm_not_written 1116 16008 (by decide))
    (l12me_pm_not_written 1116 9731 (by decide))
    (l12me_pm_not_written 1116 9733 (by decide))
    (l12me_pm_not_written 1116 9737 (by decide))
    (l12me_pm_not_written 1116 9739 (by decide))
    (l12me_pm_not_written 1116 9738 (by decide))
    (l12me_pm_not_written 1116 9740 (by decide))
  intro s
  have hb := l12me_buddy_facts.2.1
  unfold l12mePmMoE0 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 0 16008 9731 9733 9737 9739 9741 [64, 0, 32, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12me_red_pm9742 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9742 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributedFaithful pm initPM 16031)
        (denoteGraphDistributedFaithful pm initPM 9732)
        (denoteGraphDistributedFaithful pm initPM 9734)
        [denoteGraphDistributedFaithful pm initPM 9737,
         denoteGraphDistributedFaithful pm initPM 9738]
        [denoteGraphDistributedFaithful pm initPM 9739,
         denoteGraphDistributedFaithful pm initPM 9740]
        64 8 (((10 : Nat) : Scalar)) := by
  refine denoteGraphDistributedFaithful_reduce7 pm initPM 1119 l12mePmMoE1
    16031 9732 9734 9737 9738 9739 9740 9742
    (fun x rp rm w13a w13b w2a w2b =>
      fw_all2all_moe_gmm_full x rp rm [w13a, w13b] [w2a, w2b] 64 8
        (((10 : Nat) : Scalar)))
    (by native_decide) l12me_node_facts.2.2 ?_
    (l12me_nonempty_pm 1120) (l12me_pm_not_written 1120 9742 (by decide))
    (l12me_nonempty_pm 1119) (l12me_pm_not_written 1119 16031 (by decide))
    (l12me_pm_not_written 1119 9732 (by decide))
    (l12me_pm_not_written 1119 9734 (by decide))
    (l12me_pm_not_written 1119 9737 (by decide))
    (l12me_pm_not_written 1119 9738 (by decide))
    (l12me_pm_not_written 1119 9739 (by decide))
    (l12me_pm_not_written 1119 9740 (by decide))
  intro s
  have hb := l12me_buddy_facts.2.2
  unfold l12mePmMoE1 at hb ⊢
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide) (by decide)]
  rw [applyNodeDistributed_moe_out pm s 1 16031 9732 9734 9738 9740 9742 [64, 32, 64, 8]]
  unfold applyNodeFullExpertMoE_value
  rw [hb]
  rfl

/-! ### Weight boundary bridges (init goals `5363` / `5364`) -/

set_option maxRecDepth 1000000 in
private theorem l12me_weight_bridge (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W A B : Tid) (shard : Shape)
    (htp : gW.tps = [{rank := 0, tid := A}, {rank := 1, tid := B}])
    (hgd : gW.gatherDim = 0) (hrep : gW.replicated = false) (hts : gW.ts = W)
    (htpShapes : gW.tpShapes = [shard, shard]) (hshard : shard ≠ [1]) :
    initSM W = allGatherPrimDimN 0 2 0 [initPM A, initPM B] := by
  have h := hInit gW hgW
  unfold InitGoalHolds at h
  have hshapes := h.2.1
  rw [htp, htpShapes] at hshapes
  simp only [List.map, List.cons.injEq, and_true] at hshapes
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated gW pm.numRanks _ hrep, htp, hts, hgd] at hval
  simp only [List.map] at hval
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
        (by rw [hshapes.1]; exact hshard)] at hval
  rw [show pm.numRanks = 2 from rfl] at hval
  exact hval

/-! ### `hdec` derived from the ambient zigzag well-formedness -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12me_cu_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm initPM 5345).shape = [2] := by
  rw [l12me_pm_leaf initPM 5345 (by decide)]
  exact hPM 5345 [2] (by native_decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l12me_hdec {full z0 z1 : Tensor} {k : Nat} (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hrel : Zigzag2Rel full z0 z1 (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, k] [2048, k]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5345) = [0, 2 * 2048] := by
  have hcuShape := l12me_cu_shape initPM hPM
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5345)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hrel
  apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
  have ht := hs.cu_wf.local_tokens
  simp only [List.getD_cons_zero] at ht
  rw [hs.source0_shape] at ht
  norm_num at ht
  norm_num
  exact ht.symm

/-! ### Goal -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5365_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5365)
      (denoteGraphDistributedFaithful pm initPM 9741)
      (denoteGraphDistributedFaithful pm initPM 9742)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  -- Parent relations for the three streaming inputs.
  have hX := recon_zigzagGoal_8162_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRP := recon_zigzagGoal_5360_faithful initSM initPM hSM hPM hInit hValues hCu
  have hRM := recon_zigzagGoal_5361_faithful initSM initPM hSM hPM hInit hValues hCu
  have hdec := l12me_hdec initPM hPM hX
  obtain ⟨x0, x1, hxs⟩ := hX
  obtain ⟨p0, p1, hps⟩ := hRP
  obtain ⟨m0, m1, hms⟩ := hRM
  have hX' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 8162)
      (denoteGraphDistributedFaithful pm initPM 16008)
      (denoteGraphDistributedFaithful pm initPM 16031)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 1024] [2048, 1024] := ⟨x0, x1, hxs⟩
  have hRP' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5360)
      (denoteGraphDistributedFaithful pm initPM 9731)
      (denoteGraphDistributedFaithful pm initPM 9732)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 64] [2048, 64] := ⟨p0, p1, hps⟩
  have hRM' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5361)
      (denoteGraphDistributedFaithful pm initPM 9733)
      (denoteGraphDistributedFaithful pm initPM 9734)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [2048 * 2, 64] [2048, 64] := ⟨m0, m1, hms⟩
  -- Weight bridges: SM weight = PM expert-axis all-gather of the two shards.
  have hbW13 : initSM 5363 = allGatherPrimDimN 0 2 0 [initPM 9737, initPM 9738] :=
    l12me_weight_bridge initSM initPM hInit initGoal_5363 (by native_decide)
      5363 9737 9738 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
  have hbW2 : initSM 5364 = allGatherPrimDimN 0 2 0 [initPM 9739, initPM 9740] :=
    l12me_weight_bridge initSM initPM hInit initGoal_5364 (by native_decide)
      5364 9739 9740 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
  have hw13shape : (initSM 5363).shape = [64, 1024, 1024] :=
    hSM 5363 [64, 1024, 1024] (by native_decide)
  have hw2shape : (initSM 5364).shape = [64, 1024, 512] :=
    hSM 5364 [64, 1024, 512] (by native_decide)
  -- Reduce all three nodes to `fw_all2all_moe_gmm_full`.
  rw [l12me_red_sm5365 initSM, l12me_red_pm9741 initPM, l12me_red_pm9742 initPM]
  rw [l12me_sm_leaf initSM 5363 (by decide), l12me_sm_leaf initSM 5364 (by decide),
    l12me_pm_leaf initPM 9737 (by decide), l12me_pm_leaf initPM 9738 (by decide),
    l12me_pm_leaf initPM 9739 (by decide), l12me_pm_leaf initPM 9740 (by decide)]
  -- Unfold `_full` and collapse the SM-side singleton gather to `initSM 5363/5364`.
  unfold fw_all2all_moe_gmm_full
  simp only [List.length_cons, List.length_nil]
  rw [allGatherPrimDimN_singleton_eq 0 (initSM 5363) (by rw [hw13shape]; decide),
    allGatherPrimDimN_singleton_eq 0 (initSM 5364) (by rw [hw2shape]; decide)]
  -- Both sides now use exactly the same gathered expert weights.
  rw [hbW13, hbW2]
  exact Zigzag2Rel.all2all_moe_gmm
    (allGatherPrimDimN 0 2 0 [initPM 9737, initPM 9738])
    (allGatherPrimDimN 0 2 0 [initPM 9739, initPM 9740])
    2048 1024 64 8 64 1024 512 (((10 : Nat) : Scalar))
    hX' hRP' hRM' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [← hbW13]; exact hw13shape) hdec

end
end TrainVerify.Denote.GeneratedPatterns
