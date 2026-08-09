/- Canonical Goal 1 L18: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.CanonicalL18AttentionComposition
import denote.yoco_goals.CanonicalL18KAlignment
import denote.yoco_goals.CanonicalL18KVGraph
import denote.yoco_goals.CanonicalL18Upstream
import denote.yoco_goals.CanonicalL18Output

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

private theorem cL18A_reduce5
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

private theorem cL18A_reduce8
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

private theorem cL18A_init_singleton_eq (initSM initPM : Store)
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

private theorem cL18A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL18A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem cL18A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def cL18ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [6039, 6040, 6041, 6042, 6043], outs := [6044, 6045],
    params := [16, 4, 64, 64, 1, 0] }
private def cL18APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10992, 11004, 11010, 6042, 6043], outs := [11016, 6045],
    params := [16, 4, 64, 64, 1, 0] }
private def cL18APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10993, 11005, 11011, 6042, 6043], outs := [11017, 6045],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL18A_nodes :
    sm_goal_1.nodes[785]'(by native_decide) = cL18ASm ∧
    pm_goal_1.nodes[1721]'(by native_decide) = cL18APm0 ∧
    pm_goal_1.nodes[1722]'(by native_decide) = cL18APm1 := by native_decide
private theorem cL18A_buddies :
    sm_goal_1.replicaBuddies cL18ASm = [cL18ASm] ∧
    pm_goal_1.replicaBuddies cL18APm0 = [cL18APm0, cL18APm1] ∧
    pm_goal_1.replicaBuddies cL18APm1 = [cL18APm0, cL18APm1] := by native_decide

private theorem cL18A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(786, 6044), (785, 6039), (785, 6040), (785, 6041),
      (785, 6042), (785, 6043)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL18A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1722, 11016), (1723, 11017),
      (1721, 10992), (1721, 10993), (1721, 11004), (1721, 11005),
      (1721, 11010), (1721, 11011), (1721, 6042), (1721, 6043),
      (1722, 10992), (1722, 10993), (1722, 11004), (1722, 11005),
      (1722, 11010), (1722, 11011), (1722, 6042), (1722, 6043)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L18 attention reduction. -/
theorem canonical_l18_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6044 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6039)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6040)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6041)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6042)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6043)
        16 4 64 64 true 0 := by
  refine cL18A_reduce5 sm_goal_1 initSM 785 cL18ASm 6039 6040 6041 6042 6043 6044
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL18A_nodes.1 ?_ (by native_decide)
    (cL18A_sm_nw 786 6044 (by decide)) (by native_decide)
    (cL18A_sm_nw 785 6039 (by decide)) (cL18A_sm_nw 785 6040 (by decide))
    (cL18A_sm_nw 785 6041 (by decide)) (cL18A_sm_nw 785 6042 (by decide))
    (cL18A_sm_nw 785 6043 (by decide))
  intro s
  have hb := cL18A_buddies.1
  unfold cL18ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L18 attention reduction uses ordinary K/V shards. -/
theorem canonical_l18_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11016 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10992,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10993]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11004,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11005]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11010,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11011]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6042)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6043)
        16 4 64 64 true 0 2 0 := by
  refine cL18A_reduce8 pm_goal_1 initPM 1721 cL18APm0
    10992 10993 11004 11005 11010 11011 6042 6043 11016
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL18A_nodes.2.1 ?_ (by native_decide)
    (cL18A_pm_nw 1722 11016 (by decide)) (by native_decide)
    (cL18A_pm_nw 1721 10992 (by decide)) (cL18A_pm_nw 1721 10993 (by decide))
    (cL18A_pm_nw 1721 11004 (by decide)) (cL18A_pm_nw 1721 11005 (by decide))
    (cL18A_pm_nw 1721 11010 (by decide)) (cL18A_pm_nw 1721 11011 (by decide))
    (cL18A_pm_nw 1721 6042 (by decide)) (cL18A_pm_nw 1721 6043 (by decide))
  intro s
  have hb := cL18A_buddies.2.1
  unfold cL18APm0 cL18APm1 at hb
  unfold cL18APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L18 attention reduction uses ordinary K/V shards. -/
theorem canonical_l18_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11017 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10992,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10993]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11004,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11005]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11010,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11011]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6042)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6043)
        16 4 64 64 true 0 2 1 := by
  refine cL18A_reduce8 pm_goal_1 initPM 1722 cL18APm1
    10992 10993 11004 11005 11010 11011 6042 6043 11017
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL18A_nodes.2.2 ?_ (by native_decide)
    (cL18A_pm_nw 1723 11017 (by decide)) (by native_decide)
    (cL18A_pm_nw 1722 10992 (by decide)) (cL18A_pm_nw 1722 10993 (by decide))
    (cL18A_pm_nw 1722 11004 (by decide)) (cL18A_pm_nw 1722 11005 (by decide))
    (cL18A_pm_nw 1722 11010 (by decide)) (cL18A_pm_nw 1722 11011 (by decide))
    (cL18A_pm_nw 1722 6042 (by decide)) (cL18A_pm_nw 1722 6043 (by decide))
  intro s
  have hb := cL18A_buddies.2.2
  unfold cL18APm0 cL18APm1 at hb
  unfold cL18APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L18 graph values. -/
theorem canonical_l18_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6039)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10992)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10993)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6040)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11004)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11005)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6041)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11010)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11011)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 6042 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6042)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 6043 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6043)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6042 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11017)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [canonical_l18_attention_sm_reduce initSM,
    canonical_l18_attention_pm0_reduce initPM,
    canonical_l18_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The exact L18 attention relation exported from the sole computed incoming
interface plus the external ordinary K/V cache contract.  Q and both projected
K/V branches are closed internally at their real graph tids. -/
theorem canonical_l18_attention_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6042 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6044)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11016)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11017)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := canonical_l18_q_relation_from_incoming initSM initPM hPM hInit hIncoming
  have hK := canonical_l18_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l18_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := cL18A_external_input_eq initSM initPM hInit initGoal_6042
    (by native_decide) 6042 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := cL18A_external_input_eq initSM initPM hInit initGoal_6043
    (by native_decide) 6043 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact canonical_l18_attention_from_qkv initSM initPM hQ hK hV hCuSM hCuKV
    hCuAlias hDecoded

/-- Complete canonical L18 attention residual at the exact graph values.  The incoming
L18 stream is the only computed-lineage premise; the cache and cumulative-sequence metadata
are external contracts, while Q/K/V, projection weights, and residual transport
are discharged internally. -/
theorem canonical_l18_attention_residual_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6042 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := canonical_l18_attention_from_incoming_and_cache initSM initPM
    hPM hInit hIncoming hCache hCuAlias hDecoded
  have hResidual := canonical_l18_residual_from_incoming initSM initPM hIncoming
  have hWeight := cL18A_external_input_eq initSM initPM hInit initGoal_6048
    (by native_decide) 6048 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6048).shape = [1024, 1024] := by
    rw [cL18A_external_input_pm_value initPM 6048 (by native_decide)]
    exact hPM 6048 [1024, 1024] (by native_decide)
  exact canonical_l18_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

#print axioms canonical_l18_attention_from_qkv
#print axioms canonical_l18_attention_from_incoming_and_cache
#print axioms canonical_l18_attention_residual_from_incoming_and_cache

end
end TrainVerify.Denote.GeneratedPatterns
