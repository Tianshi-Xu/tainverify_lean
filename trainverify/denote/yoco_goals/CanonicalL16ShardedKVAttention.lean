/- Canonical Goal 1 L16: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.CanonicalL16AttentionComposition
import denote.yoco_goals.CanonicalL16KAlignment
import denote.yoco_goals.CanonicalL16KVGraph
import denote.yoco_goals.CanonicalL16Upstream
import denote.yoco_goals.CanonicalL16Output

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

private theorem cL16A_reduce5
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

private theorem cL16A_reduce8
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

private theorem cL16A_init_singleton_eq (initSM initPM : Store)
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

private theorem cL16A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL16A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem cL16A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def cL16ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5931, 5932, 5933, 5934, 5935], outs := [5936, 5937],
    params := [16, 4, 64, 64, 1, 0] }
private def cL16APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10684, 10696, 10702, 5934, 5935], outs := [10708, 5937],
    params := [16, 4, 64, 64, 1, 0] }
private def cL16APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10685, 10697, 10703, 5934, 5935], outs := [10709, 5937],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL16A_nodes :
    sm_goal_1.nodes[715]'(by native_decide) = cL16ASm ∧
    pm_goal_1.nodes[1569]'(by native_decide) = cL16APm0 ∧
    pm_goal_1.nodes[1570]'(by native_decide) = cL16APm1 := by native_decide
private theorem cL16A_buddies :
    sm_goal_1.replicaBuddies cL16ASm = [cL16ASm] ∧
    pm_goal_1.replicaBuddies cL16APm0 = [cL16APm0, cL16APm1] ∧
    pm_goal_1.replicaBuddies cL16APm1 = [cL16APm0, cL16APm1] := by native_decide

private theorem cL16A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(716, 5936), (715, 5931), (715, 5932), (715, 5933),
      (715, 5934), (715, 5935)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL16A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1570, 10708), (1571, 10709),
      (1569, 10684), (1569, 10685), (1569, 10696), (1569, 10697),
      (1569, 10702), (1569, 10703), (1569, 5934), (1569, 5935),
      (1570, 10684), (1570, 10685), (1570, 10696), (1570, 10697),
      (1570, 10702), (1570, 10703), (1570, 5934), (1570, 5935)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L16 attention reduction. -/
theorem canonical_l16_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5936 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5931)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5932)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5933)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5934)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5935)
        16 4 64 64 true 0 := by
  refine cL16A_reduce5 sm_goal_1 initSM 715 cL16ASm 5931 5932 5933 5934 5935 5936
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL16A_nodes.1 ?_ (by native_decide)
    (cL16A_sm_nw 716 5936 (by decide)) (by native_decide)
    (cL16A_sm_nw 715 5931 (by decide)) (cL16A_sm_nw 715 5932 (by decide))
    (cL16A_sm_nw 715 5933 (by decide)) (cL16A_sm_nw 715 5934 (by decide))
    (cL16A_sm_nw 715 5935 (by decide))
  intro s
  have hb := cL16A_buddies.1
  unfold cL16ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L16 attention reduction uses ordinary K/V shards. -/
theorem canonical_l16_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10708 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10684,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10685]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10696,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10697]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10702,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10703]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5934)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5935)
        16 4 64 64 true 0 2 0 := by
  refine cL16A_reduce8 pm_goal_1 initPM 1569 cL16APm0
    10684 10685 10696 10697 10702 10703 5934 5935 10708
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL16A_nodes.2.1 ?_ (by native_decide)
    (cL16A_pm_nw 1570 10708 (by decide)) (by native_decide)
    (cL16A_pm_nw 1569 10684 (by decide)) (cL16A_pm_nw 1569 10685 (by decide))
    (cL16A_pm_nw 1569 10696 (by decide)) (cL16A_pm_nw 1569 10697 (by decide))
    (cL16A_pm_nw 1569 10702 (by decide)) (cL16A_pm_nw 1569 10703 (by decide))
    (cL16A_pm_nw 1569 5934 (by decide)) (cL16A_pm_nw 1569 5935 (by decide))
  intro s
  have hb := cL16A_buddies.2.1
  unfold cL16APm0 cL16APm1 at hb
  unfold cL16APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L16 attention reduction uses ordinary K/V shards. -/
theorem canonical_l16_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10709 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10684,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10685]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10696,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10697]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10702,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10703]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5934)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5935)
        16 4 64 64 true 0 2 1 := by
  refine cL16A_reduce8 pm_goal_1 initPM 1570 cL16APm1
    10684 10685 10696 10697 10702 10703 5934 5935 10709
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL16A_nodes.2.2 ?_ (by native_decide)
    (cL16A_pm_nw 1571 10709 (by decide)) (by native_decide)
    (cL16A_pm_nw 1570 10684 (by decide)) (cL16A_pm_nw 1570 10685 (by decide))
    (cL16A_pm_nw 1570 10696 (by decide)) (cL16A_pm_nw 1570 10697 (by decide))
    (cL16A_pm_nw 1570 10702 (by decide)) (cL16A_pm_nw 1570 10703 (by decide))
    (cL16A_pm_nw 1570 5934 (by decide)) (cL16A_pm_nw 1570 5935 (by decide))
  intro s
  have hb := cL16A_buddies.2.2
  unfold cL16APm0 cL16APm1 at hb
  unfold cL16APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L16 graph values. -/
theorem canonical_l16_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5931)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10684)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10685)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5932)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10696)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10697)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10702)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10703)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5934 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5934)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 5935 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5935)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5934 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5936)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10709)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [canonical_l16_attention_sm_reduce initSM,
    canonical_l16_attention_pm0_reduce initPM,
    canonical_l16_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The exact L16 attention relation exported from the sole computed incoming
interface plus the external ordinary K/V cache contract.  Q and both projected
K/V branches are closed internally at their real graph tids. -/
theorem canonical_l16_attention_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5923)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10675)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5934 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5936)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10708)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10709)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := canonical_l16_q_relation_from_incoming initSM initPM hPM hInit hIncoming
  have hK := canonical_l16_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l16_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := cL16A_external_input_eq initSM initPM hInit initGoal_5934
    (by native_decide) 5934 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := cL16A_external_input_eq initSM initPM hInit initGoal_5935
    (by native_decide) 5935 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact canonical_l16_attention_from_qkv initSM initPM hQ hK hV hCuSM hCuKV
    hCuAlias hDecoded

/-- Complete canonical L16 attention residual at the exact graph values.  The incoming
L16 stream is the only computed-lineage premise; the cache and cumulative-sequence metadata
are external contracts, while Q/K/V, projection weights, and residual transport
are discharged internally. -/
theorem canonical_l16_attention_residual_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5923)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10675)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5934 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := canonical_l16_attention_from_incoming_and_cache initSM initPM
    hPM hInit hIncoming hCache hCuAlias hDecoded
  have hResidual := canonical_l16_residual_from_incoming initSM initPM hIncoming
  have hWeight := cL16A_external_input_eq initSM initPM hInit initGoal_5940
    (by native_decide) 5940 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5940).shape = [1024, 1024] := by
    rw [cL16A_external_input_pm_value initPM 5940 (by native_decide)]
    exact hPM 5940 [1024, 1024] (by native_decide)
  exact canonical_l16_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

#print axioms canonical_l16_attention_from_qkv
#print axioms canonical_l16_attention_from_incoming_and_cache
#print axioms canonical_l16_attention_residual_from_incoming_and_cache

end
end TrainVerify.Denote.GeneratedPatterns
