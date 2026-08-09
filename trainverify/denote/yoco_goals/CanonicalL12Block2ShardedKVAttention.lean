/- Canonical Goal 1 L12 block 2: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.CanonicalL12Block2AttentionComposition
import denote.yoco_goals.CanonicalL12Block2KAlignment
import denote.yoco_goals.CanonicalL12Block2KVGraph
import denote.yoco_goals.CanonicalL12Block2Upstream
import denote.yoco_goals.CanonicalL12Block2Output
import denote.yoco_goals.CanonicalL12ZigzagEntry

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective
noncomputable section

private theorem cL12B2A_reduce5
    (g : GraphDecl) (init : Store) (idx : Nat) (node : NodeDecl)
    (i0 i1 i2 i3 i4 out : Tid)
    (f : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hidx : idx < g.nodes.length) (hnode : g.nodes[idx]'hidx = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node out =
      f (s i0) (s i1) (s i2) (s i3) (s i4))
    (ha : ∀ n ∈ g.nodes.drop (idx + 1), n.outs ≠ [])
    (ho : ∀ n ∈ g.nodes.drop (idx + 1), out ∉ n.outs)
    (hp : ∀ n ∈ g.nodes.drop idx, n.outs ≠ [])
    (h0 : ∀ n ∈ g.nodes.drop idx, i0 ∉ n.outs)
    (h1 : ∀ n ∈ g.nodes.drop idx, i1 ∉ n.outs)
    (h2 : ∀ n ∈ g.nodes.drop idx, i2 ∉ n.outs)
    (h3 : ∀ n ∈ g.nodes.drop idx, i3 ∉ n.outs)
    (h4 : ∀ n ∈ g.nodes.drop idx, i4 ∉ n.outs) :
    denoteGraphDistributedFaithful g init out =
      f (denoteGraphDistributedFaithful g init i0)
        (denoteGraphDistributedFaithful g init i1)
        (denoteGraphDistributedFaithful g init i2)
        (denoteGraphDistributedFaithful g init i3)
        (denoteGraphDistributedFaithful g init i4) := by
  rw [denoteGraphDistributedFaithful_node_core g init idx node out hidx hnode ha ho,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init idx i0 hp h0,
    denoteGraphDistributedFaithful_prefix_read g init idx i1 hp h1,
    denoteGraphDistributedFaithful_prefix_read g init idx i2 hp h2,
    denoteGraphDistributedFaithful_prefix_read g init idx i3 hp h3,
    denoteGraphDistributedFaithful_prefix_read g init idx i4 hp h4]

private theorem cL12B2A_reduce8
    (g : GraphDecl) (init : Store) (idx : Nat) (node : NodeDecl)
    (i0 i1 i2 i3 i4 i5 i6 i7 out : Tid)
    (f : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hidx : idx < g.nodes.length) (hnode : g.nodes[idx]'hidx = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node out =
      f (s i0) (s i1) (s i2) (s i3) (s i4) (s i5) (s i6) (s i7))
    (ha : ∀ n ∈ g.nodes.drop (idx + 1), n.outs ≠ [])
    (ho : ∀ n ∈ g.nodes.drop (idx + 1), out ∉ n.outs)
    (hp : ∀ n ∈ g.nodes.drop idx, n.outs ≠ [])
    (h0 : ∀ n ∈ g.nodes.drop idx, i0 ∉ n.outs)
    (h1 : ∀ n ∈ g.nodes.drop idx, i1 ∉ n.outs)
    (h2 : ∀ n ∈ g.nodes.drop idx, i2 ∉ n.outs)
    (h3 : ∀ n ∈ g.nodes.drop idx, i3 ∉ n.outs)
    (h4 : ∀ n ∈ g.nodes.drop idx, i4 ∉ n.outs)
    (h5 : ∀ n ∈ g.nodes.drop idx, i5 ∉ n.outs)
    (h6 : ∀ n ∈ g.nodes.drop idx, i6 ∉ n.outs)
    (h7 : ∀ n ∈ g.nodes.drop idx, i7 ∉ n.outs) :
    denoteGraphDistributedFaithful g init out =
      f (denoteGraphDistributedFaithful g init i0)
        (denoteGraphDistributedFaithful g init i1)
        (denoteGraphDistributedFaithful g init i2)
        (denoteGraphDistributedFaithful g init i3)
        (denoteGraphDistributedFaithful g init i4)
        (denoteGraphDistributedFaithful g init i5)
        (denoteGraphDistributedFaithful g init i6)
        (denoteGraphDistributedFaithful g init i7) := by
  rw [denoteGraphDistributedFaithful_node_core g init idx node out hidx hnode ha ho,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init idx i0 hp h0,
    denoteGraphDistributedFaithful_prefix_read g init idx i1 hp h1,
    denoteGraphDistributedFaithful_prefix_read g init idx i2 hp h2,
    denoteGraphDistributedFaithful_prefix_read g init idx i3 hp h3,
    denoteGraphDistributedFaithful_prefix_read g init idx i4 hp h4,
    denoteGraphDistributedFaithful_prefix_read g init idx i5 hp h5,
    denoteGraphDistributedFaithful_prefix_read g init idx i6 hp h6,
    denoteGraphDistributedFaithful_prefix_read g init idx i7 hp h7]

private theorem cL12B2A_init_singleton_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid) :
    initSM tid = initPM tid := by
  have h := hInit g hg
  unfold InitGoalHolds at h
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated g pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hv
  simpa only [List.map, reconstructWithDim] using hv

private theorem cL12B2A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL12B2A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem cL12B2A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def cL12B2ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5661, 5662, 5663, 5664, 5665], outs := [5666, 5667],
    params := [16, 4, 64, 64, 1, 0] }
private def cL12B2APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9914, 9926, 9932, 5664, 5665], outs := [9938, 5667],
    params := [16, 4, 64, 64, 1, 0] }
private def cL12B2APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9915, 9927, 9933, 5664, 5665], outs := [9939, 5667],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL12B2A_nodes :
    sm_goal_1.nodes[540]'(by native_decide) = cL12B2ASm ∧
    pm_goal_1.nodes[1189]'(by native_decide) = cL12B2APm0 ∧
    pm_goal_1.nodes[1190]'(by native_decide) = cL12B2APm1 := by native_decide
private theorem cL12B2A_buddies :
    sm_goal_1.replicaBuddies cL12B2ASm = [cL12B2ASm] ∧
    pm_goal_1.replicaBuddies cL12B2APm0 = [cL12B2APm0, cL12B2APm1] ∧
    pm_goal_1.replicaBuddies cL12B2APm1 = [cL12B2APm0, cL12B2APm1] := by native_decide

private theorem cL12B2A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(541, 5666), (540, 5661), (540, 5662), (540, 5663),
      (540, 5664), (540, 5665)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL12B2A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1190, 9938), (1191, 9939),
      (1189, 9914), (1189, 9915), (1189, 9926), (1189, 9927),
      (1189, 9932), (1189, 9933), (1189, 5664), (1189, 5665),
      (1190, 9914), (1190, 9915), (1190, 9926), (1190, 9927),
      (1190, 9932), (1190, 9933), (1190, 5664), (1190, 5665)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L12 block 2 attention reduction. -/
theorem canonical_l12b2_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5666 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5661)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5662)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5663)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5664)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5665)
        16 4 64 64 true 0 := by
  refine cL12B2A_reduce5 sm_goal_1 initSM 540 cL12B2ASm 5661 5662 5663 5664 5665 5666
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL12B2A_nodes.1 ?_ (by native_decide)
    (cL12B2A_sm_nw 541 5666 (by decide)) (by native_decide)
    (cL12B2A_sm_nw 540 5661 (by decide)) (cL12B2A_sm_nw 540 5662 (by decide))
    (cL12B2A_sm_nw 540 5663 (by decide)) (cL12B2A_sm_nw 540 5664 (by decide))
    (cL12B2A_sm_nw 540 5665 (by decide))
  intro s
  have hb := cL12B2A_buddies.1
  unfold cL12B2ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L12 block 2 attention reduction uses ordinary K/V shards. -/
theorem canonical_l12b2_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9938 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9914,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9915]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9926,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9927]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9932,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9933]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5664)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5665)
        16 4 64 64 true 0 2 0 := by
  refine cL12B2A_reduce8 pm_goal_1 initPM 1189 cL12B2APm0
    9914 9915 9926 9927 9932 9933 5664 5665 9938
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL12B2A_nodes.2.1 ?_ (by native_decide)
    (cL12B2A_pm_nw 1190 9938 (by decide)) (by native_decide)
    (cL12B2A_pm_nw 1189 9914 (by decide)) (cL12B2A_pm_nw 1189 9915 (by decide))
    (cL12B2A_pm_nw 1189 9926 (by decide)) (cL12B2A_pm_nw 1189 9927 (by decide))
    (cL12B2A_pm_nw 1189 9932 (by decide)) (cL12B2A_pm_nw 1189 9933 (by decide))
    (cL12B2A_pm_nw 1189 5664 (by decide)) (cL12B2A_pm_nw 1189 5665 (by decide))
  intro s
  have hb := cL12B2A_buddies.2.1
  unfold cL12B2APm0 cL12B2APm1 at hb
  unfold cL12B2APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L12 block 2 attention reduction uses ordinary K/V shards. -/
theorem canonical_l12b2_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9939 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9914,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9915]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9926,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9927]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9932,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9933]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5664)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5665)
        16 4 64 64 true 0 2 1 := by
  refine cL12B2A_reduce8 pm_goal_1 initPM 1190 cL12B2APm1
    9914 9915 9926 9927 9932 9933 5664 5665 9939
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL12B2A_nodes.2.2 ?_ (by native_decide)
    (cL12B2A_pm_nw 1191 9939 (by decide)) (by native_decide)
    (cL12B2A_pm_nw 1190 9914 (by decide)) (cL12B2A_pm_nw 1190 9915 (by decide))
    (cL12B2A_pm_nw 1190 9926 (by decide)) (cL12B2A_pm_nw 1190 9927 (by decide))
    (cL12B2A_pm_nw 1190 9932 (by decide)) (cL12B2A_pm_nw 1190 9933 (by decide))
    (cL12B2A_pm_nw 1190 5664 (by decide)) (cL12B2A_pm_nw 1190 5665 (by decide))
  intro s
  have hb := cL12B2A_buddies.2.2
  unfold cL12B2APm0 cL12B2APm1 at hb
  unfold cL12B2APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L12 block 2 graph values. -/
theorem canonical_l12b2_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5661)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9914)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9915)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5662)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9926)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9927)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5663)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9932)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9933)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5664 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5664)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 5665 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5665)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5664 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9938)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9939)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [canonical_l12b2_attention_sm_reduce initSM,
    canonical_l12b2_attention_pm0_reduce initPM,
    canonical_l12b2_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The exact L12 block 2 attention relation exported from the sole computed incoming
interface plus the external ordinary K/V cache contract.  Q and both projected
K/V branches are closed internally at their real graph tids. -/
theorem canonical_l12b2_attention_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hContract : Goal1ExternalInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5666)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9938)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9939)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := canonical_l12b2_q_relation_from_incoming initSM initPM hPM hInit hIncoming
  have hK := canonical_l12b2_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l12b2_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := cL12B2A_external_input_eq initSM initPM hInit initGoal_5664
    (by native_decide) 5664 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := cL12B2A_external_input_eq initSM initPM hInit initGoal_5665
    (by native_decide) 5665 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuInit : initPM 5664 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5664 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [cL12B2A_external_input_pm_value initPM 5664 (by native_decide),
      cL12B2A_external_input_pm_value initPM 6252 (by native_decide), hcuInit]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [cL12B2A_external_input_pm_value initPM 6252 (by native_decide)]
    exact hContract.2.2.1.decoded_single
  exact canonical_l12b2_attention_from_qkv initSM initPM hQ hK hV hCuSM hCuKV
    hCuAlias hDecoded

/-- Complete canonical L12 block 2 attention residual at the exact graph values.  The incoming
L12 block 2 stream is the only computed-lineage premise; the cache and cumulative-sequence metadata
are external contracts, while Q/K/V, projection weights, and residual transport
are discharged internally. -/
theorem canonical_l12b2_attention_residual_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hContract : Goal1ExternalInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := canonical_l12b2_attention_from_incoming_and_cache initSM initPM
    hPM hInit hIncoming hCache hContract
  have hResidual := canonical_l12b2_residual_from_incoming initSM initPM hIncoming
  have hWeight := cL12B2A_external_input_eq initSM initPM hInit initGoal_5670
    (by native_decide) 5670 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5670).shape = [1024, 1024] := by
    rw [cL12B2A_external_input_pm_value initPM 5670 (by native_decide)]
    exact hPM 5670 [1024, 1024] (by native_decide)
  exact canonical_l12b2_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

#print axioms canonical_l12b2_attention_from_qkv
#print axioms canonical_l12b2_attention_from_incoming_and_cache
#print axioms canonical_l12b2_attention_residual_from_incoming_and_cache

end
end TrainVerify.Denote.GeneratedPatterns

