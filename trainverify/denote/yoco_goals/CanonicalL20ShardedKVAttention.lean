/- Canonical Goal 1 L20: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.CanonicalL20AttentionComposition
import denote.yoco_goals.CanonicalL20KAlignment
import denote.yoco_goals.CanonicalL20KVGraph
import denote.yoco_goals.CanonicalL20Upstream
import denote.yoco_goals.CanonicalL20Output

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

private theorem cL20A_reduce5
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

private theorem cL20A_reduce8
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

private theorem cL20A_init_singleton_eq (initSM initPM : Store)
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

private theorem cL20A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL20A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem cL20A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def cL20ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [6147, 6148, 6149, 6150, 6151], outs := [6152, 6153],
    params := [16, 4, 64, 64, 1, 0] }
private def cL20APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11300, 11312, 11318, 6150, 6151], outs := [11324, 6153],
    params := [16, 4, 64, 64, 1, 0] }
private def cL20APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11301, 11313, 11319, 6150, 6151], outs := [11325, 6153],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL20A_nodes :
    sm_goal_1.nodes[855]'(by native_decide) = cL20ASm ∧
    pm_goal_1.nodes[1873]'(by native_decide) = cL20APm0 ∧
    pm_goal_1.nodes[1874]'(by native_decide) = cL20APm1 := by native_decide
private theorem cL20A_buddies :
    sm_goal_1.replicaBuddies cL20ASm = [cL20ASm] ∧
    pm_goal_1.replicaBuddies cL20APm0 = [cL20APm0, cL20APm1] ∧
    pm_goal_1.replicaBuddies cL20APm1 = [cL20APm0, cL20APm1] := by native_decide

private theorem cL20A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(856, 6152), (855, 6147), (855, 6148), (855, 6149),
      (855, 6150), (855, 6151)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL20A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1874, 11324), (1875, 11325),
      (1873, 11300), (1873, 11301), (1873, 11312), (1873, 11313),
      (1873, 11318), (1873, 11319), (1873, 6150), (1873, 6151),
      (1874, 11300), (1874, 11301), (1874, 11312), (1874, 11313),
      (1874, 11318), (1874, 11319), (1874, 6150), (1874, 6151)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L20 attention reduction. -/
theorem canonical_l20_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6152 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6147)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6148)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6149)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6150)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6151)
        16 4 64 64 true 0 := by
  refine cL20A_reduce5 sm_goal_1 initSM 855 cL20ASm 6147 6148 6149 6150 6151 6152
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL20A_nodes.1 ?_ (by native_decide)
    (cL20A_sm_nw 856 6152 (by decide)) (by native_decide)
    (cL20A_sm_nw 855 6147 (by decide)) (cL20A_sm_nw 855 6148 (by decide))
    (cL20A_sm_nw 855 6149 (by decide)) (cL20A_sm_nw 855 6150 (by decide))
    (cL20A_sm_nw 855 6151 (by decide))
  intro s
  have hb := cL20A_buddies.1
  unfold cL20ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L20 attention reduction uses ordinary K/V shards. -/
theorem canonical_l20_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11324 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11300,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11301]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11312,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11313]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11318,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11319]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6150)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6151)
        16 4 64 64 true 0 2 0 := by
  refine cL20A_reduce8 pm_goal_1 initPM 1873 cL20APm0
    11300 11301 11312 11313 11318 11319 6150 6151 11324
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL20A_nodes.2.1 ?_ (by native_decide)
    (cL20A_pm_nw 1874 11324 (by decide)) (by native_decide)
    (cL20A_pm_nw 1873 11300 (by decide)) (cL20A_pm_nw 1873 11301 (by decide))
    (cL20A_pm_nw 1873 11312 (by decide)) (cL20A_pm_nw 1873 11313 (by decide))
    (cL20A_pm_nw 1873 11318 (by decide)) (cL20A_pm_nw 1873 11319 (by decide))
    (cL20A_pm_nw 1873 6150 (by decide)) (cL20A_pm_nw 1873 6151 (by decide))
  intro s
  have hb := cL20A_buddies.2.1
  unfold cL20APm0 cL20APm1 at hb
  unfold cL20APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L20 attention reduction uses ordinary K/V shards. -/
theorem canonical_l20_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11325 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11300,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11301]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11312,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11313]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11318,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11319]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6150)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6151)
        16 4 64 64 true 0 2 1 := by
  refine cL20A_reduce8 pm_goal_1 initPM 1874 cL20APm1
    11300 11301 11312 11313 11318 11319 6150 6151 11325
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL20A_nodes.2.2 ?_ (by native_decide)
    (cL20A_pm_nw 1875 11325 (by decide)) (by native_decide)
    (cL20A_pm_nw 1874 11300 (by decide)) (cL20A_pm_nw 1874 11301 (by decide))
    (cL20A_pm_nw 1874 11312 (by decide)) (cL20A_pm_nw 1874 11313 (by decide))
    (cL20A_pm_nw 1874 11318 (by decide)) (cL20A_pm_nw 1874 11319 (by decide))
    (cL20A_pm_nw 1874 6150 (by decide)) (cL20A_pm_nw 1874 6151 (by decide))
  intro s
  have hb := cL20A_buddies.2.2
  unfold cL20APm0 cL20APm1 at hb
  unfold cL20APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L20 graph values. -/
theorem canonical_l20_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6147)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11300)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11301)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6148)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11312)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11313)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6149)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11318)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11319)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 6150 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6150)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 6151 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6151)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6150 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6152)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11325)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [canonical_l20_attention_sm_reduce initSM,
    canonical_l20_attention_pm0_reduce initPM,
    canonical_l20_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The exact L20 attention relation exported from the sole computed L19
interface plus the external ordinary K/V cache contract.  Q and both projected
K/V branches are closed internally at their real graph tids. -/
theorem canonical_l20_attention_from_l19_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hL19 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6139)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11291)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6150 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6152)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11325)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := canonical_l20_q_relation_from_l19 initSM initPM hPM hInit hL19
  have hK := canonical_l20_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l20_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := cL20A_external_input_eq initSM initPM hInit initGoal_6150
    (by native_decide) 6150 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := cL20A_external_input_eq initSM initPM hInit initGoal_6151
    (by native_decide) 6151 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact canonical_l20_attention_from_qkv initSM initPM hQ hK hV hCuSM hCuKV
    hCuAlias hDecoded

/-- Complete canonical L20 output at the exact values consumed by L21.  L19 is
the only computed-lineage premise; the cache and cumulative-sequence metadata
are external contracts, while Q/K/V, projection weights, and residual transport
are discharged internally. -/
theorem canonical_l20_output_from_l19_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hL19 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6139)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11291)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6150 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6160)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11354)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11355)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := canonical_l20_attention_from_l19_and_cache initSM initPM
    hPM hInit hL19 hCache hCuAlias hDecoded
  have hResidual := canonical_l20_residual_from_l19_output initSM initPM hL19
  have hWeight := cL20A_external_input_eq initSM initPM hInit initGoal_6156
    (by native_decide) 6156 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6156).shape = [1024, 1024] := by
    rw [cL20A_external_input_pm_value initPM 6156 (by native_decide)]
    exact hPM 6156 [1024, 1024] (by native_decide)
  exact canonical_l20_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

#print axioms canonical_l20_attention_from_qkv
#print axioms canonical_l20_attention_from_l19_and_cache
#print axioms canonical_l20_output_from_l19_and_cache

end
end TrainVerify.Denote.GeneratedPatterns
