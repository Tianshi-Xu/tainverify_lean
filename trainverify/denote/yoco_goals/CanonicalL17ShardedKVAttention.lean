/- Canonical Goal 1 L17: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.CanonicalL17AttentionComposition
import denote.yoco_goals.CanonicalL17KAlignment
import denote.yoco_goals.CanonicalL17KVGraph
import denote.yoco_goals.CanonicalL17Upstream
import denote.yoco_goals.CanonicalL17Output

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

private theorem cL17A_reduce5
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

private theorem cL17A_reduce8
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

private theorem cL17A_init_singleton_eq (initSM initPM : Store)
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

private theorem cL17A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL17A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem cL17A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def cL17ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5985, 5986, 5987, 5988, 5989], outs := [5990, 5991],
    params := [16, 4, 64, 64, 1, 0] }
private def cL17APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10838, 10850, 10856, 5988, 5989], outs := [10862, 5991],
    params := [16, 4, 64, 64, 1, 0] }
private def cL17APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10839, 10851, 10857, 5988, 5989], outs := [10863, 5991],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL17A_nodes :
    sm_goal_1.nodes[750]'(by native_decide) = cL17ASm ∧
    pm_goal_1.nodes[1645]'(by native_decide) = cL17APm0 ∧
    pm_goal_1.nodes[1646]'(by native_decide) = cL17APm1 := by native_decide
private theorem cL17A_buddies :
    sm_goal_1.replicaBuddies cL17ASm = [cL17ASm] ∧
    pm_goal_1.replicaBuddies cL17APm0 = [cL17APm0, cL17APm1] ∧
    pm_goal_1.replicaBuddies cL17APm1 = [cL17APm0, cL17APm1] := by native_decide

private theorem cL17A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(751, 5990), (750, 5985), (750, 5986), (750, 5987),
      (750, 5988), (750, 5989)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL17A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1646, 10862), (1647, 10863),
      (1645, 10838), (1645, 10839), (1645, 10850), (1645, 10851),
      (1645, 10856), (1645, 10857), (1645, 5988), (1645, 5989),
      (1646, 10838), (1646, 10839), (1646, 10850), (1646, 10851),
      (1646, 10856), (1646, 10857), (1646, 5988), (1646, 5989)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L17 attention reduction. -/
theorem canonical_l17_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5990 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5985)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5986)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5987)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5988)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5989)
        16 4 64 64 true 0 := by
  refine cL17A_reduce5 sm_goal_1 initSM 750 cL17ASm 5985 5986 5987 5988 5989 5990
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL17A_nodes.1 ?_ (by native_decide)
    (cL17A_sm_nw 751 5990 (by decide)) (by native_decide)
    (cL17A_sm_nw 750 5985 (by decide)) (cL17A_sm_nw 750 5986 (by decide))
    (cL17A_sm_nw 750 5987 (by decide)) (cL17A_sm_nw 750 5988 (by decide))
    (cL17A_sm_nw 750 5989 (by decide))
  intro s
  have hb := cL17A_buddies.1
  unfold cL17ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L17 attention reduction uses ordinary K/V shards. -/
theorem canonical_l17_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10862 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10838,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10839]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10850,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10851]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10856,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10857]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5988)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5989)
        16 4 64 64 true 0 2 0 := by
  refine cL17A_reduce8 pm_goal_1 initPM 1645 cL17APm0
    10838 10839 10850 10851 10856 10857 5988 5989 10862
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL17A_nodes.2.1 ?_ (by native_decide)
    (cL17A_pm_nw 1646 10862 (by decide)) (by native_decide)
    (cL17A_pm_nw 1645 10838 (by decide)) (cL17A_pm_nw 1645 10839 (by decide))
    (cL17A_pm_nw 1645 10850 (by decide)) (cL17A_pm_nw 1645 10851 (by decide))
    (cL17A_pm_nw 1645 10856 (by decide)) (cL17A_pm_nw 1645 10857 (by decide))
    (cL17A_pm_nw 1645 5988 (by decide)) (cL17A_pm_nw 1645 5989 (by decide))
  intro s
  have hb := cL17A_buddies.2.1
  unfold cL17APm0 cL17APm1 at hb
  unfold cL17APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L17 attention reduction uses ordinary K/V shards. -/
theorem canonical_l17_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10863 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10838,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10839]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10850,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10851]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10856,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10857]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5988)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5989)
        16 4 64 64 true 0 2 1 := by
  refine cL17A_reduce8 pm_goal_1 initPM 1646 cL17APm1
    10838 10839 10850 10851 10856 10857 5988 5989 10863
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL17A_nodes.2.2 ?_ (by native_decide)
    (cL17A_pm_nw 1647 10863 (by decide)) (by native_decide)
    (cL17A_pm_nw 1646 10838 (by decide)) (cL17A_pm_nw 1646 10839 (by decide))
    (cL17A_pm_nw 1646 10850 (by decide)) (cL17A_pm_nw 1646 10851 (by decide))
    (cL17A_pm_nw 1646 10856 (by decide)) (cL17A_pm_nw 1646 10857 (by decide))
    (cL17A_pm_nw 1646 5988 (by decide)) (cL17A_pm_nw 1646 5989 (by decide))
  intro s
  have hb := cL17A_buddies.2.2
  unfold cL17APm0 cL17APm1 at hb
  unfold cL17APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L17 graph values. -/
theorem canonical_l17_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5985)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10839)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5986)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10850)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10851)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5987)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10856)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10857)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5988 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5988)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 5989 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5989)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5988 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10863)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [canonical_l17_attention_sm_reduce initSM,
    canonical_l17_attention_pm0_reduce initPM,
    canonical_l17_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The exact L17 attention relation exported from the sole computed incoming
interface plus the external ordinary K/V cache contract.  Q and both projected
K/V branches are closed internally at their real graph tids. -/
theorem canonical_l17_attention_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5988 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5990)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10862)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10863)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := canonical_l17_q_relation_from_incoming initSM initPM hPM hInit hIncoming
  have hK := canonical_l17_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l17_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := cL17A_external_input_eq initSM initPM hInit initGoal_5988
    (by native_decide) 5988 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := cL17A_external_input_eq initSM initPM hInit initGoal_5989
    (by native_decide) 5989 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact canonical_l17_attention_from_qkv initSM initPM hQ hK hV hCuSM hCuKV
    hCuAlias hDecoded

/-- Complete canonical L17 attention residual at the exact graph values.  The incoming
L17 stream is the only computed-lineage premise; the cache and cumulative-sequence metadata
are external contracts, while Q/K/V, projection weights, and residual transport
are discharged internally. -/
theorem canonical_l17_attention_residual_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5988 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := canonical_l17_attention_from_incoming_and_cache initSM initPM
    hPM hInit hIncoming hCache hCuAlias hDecoded
  have hResidual := canonical_l17_residual_from_incoming initSM initPM hIncoming
  have hWeight := cL17A_external_input_eq initSM initPM hInit initGoal_5994
    (by native_decide) 5994 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5994).shape = [1024, 1024] := by
    rw [cL17A_external_input_pm_value initPM 5994 (by native_decide)]
    exact hPM 5994 [1024, 1024] (by native_decide)
  exact canonical_l17_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

#print axioms canonical_l17_attention_from_qkv
#print axioms canonical_l17_attention_from_incoming_and_cache
#print axioms canonical_l17_attention_residual_from_incoming_and_cache

end
end TrainVerify.Denote.GeneratedPatterns
