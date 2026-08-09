/- Canonical Goal 1 L13: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.CanonicalL13AttentionComposition
import denote.yoco_goals.CanonicalL13KAlignment
import denote.yoco_goals.CanonicalL13KVGraph
import denote.yoco_goals.CanonicalL13Upstream
import denote.yoco_goals.CanonicalL13Output

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

private theorem cL13A_reduce5
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

private theorem cL13A_reduce8
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

private theorem cL13A_init_singleton_eq (initSM initPM : Store)
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

private theorem cL13A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL13A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem cL13A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def cL13ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5769, 5770, 5771, 5772, 5773], outs := [5774, 5775],
    params := [16, 4, 64, 64, 1, 0] }
private def cL13APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10222, 10234, 10240, 5772, 5773], outs := [10246, 5775],
    params := [16, 4, 64, 64, 1, 0] }
private def cL13APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10223, 10235, 10241, 5772, 5773], outs := [10247, 5775],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL13A_nodes :
    sm_goal_1.nodes[610]'(by native_decide) = cL13ASm ∧
    pm_goal_1.nodes[1341]'(by native_decide) = cL13APm0 ∧
    pm_goal_1.nodes[1342]'(by native_decide) = cL13APm1 := by native_decide
private theorem cL13A_buddies :
    sm_goal_1.replicaBuddies cL13ASm = [cL13ASm] ∧
    pm_goal_1.replicaBuddies cL13APm0 = [cL13APm0, cL13APm1] ∧
    pm_goal_1.replicaBuddies cL13APm1 = [cL13APm0, cL13APm1] := by native_decide

private theorem cL13A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(611, 5774), (610, 5769), (610, 5770), (610, 5771),
      (610, 5772), (610, 5773)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL13A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1342, 10246), (1343, 10247),
      (1341, 10222), (1341, 10223), (1341, 10234), (1341, 10235),
      (1341, 10240), (1341, 10241), (1341, 5772), (1341, 5773),
      (1342, 10222), (1342, 10223), (1342, 10234), (1342, 10235),
      (1342, 10240), (1342, 10241), (1342, 5772), (1342, 5773)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L13 attention reduction. -/
theorem canonical_l13_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5774 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5769)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5770)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5771)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5772)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5773)
        16 4 64 64 true 0 := by
  refine cL13A_reduce5 sm_goal_1 initSM 610 cL13ASm 5769 5770 5771 5772 5773 5774
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL13A_nodes.1 ?_ (by native_decide)
    (cL13A_sm_nw 611 5774 (by decide)) (by native_decide)
    (cL13A_sm_nw 610 5769 (by decide)) (cL13A_sm_nw 610 5770 (by decide))
    (cL13A_sm_nw 610 5771 (by decide)) (cL13A_sm_nw 610 5772 (by decide))
    (cL13A_sm_nw 610 5773 (by decide))
  intro s
  have hb := cL13A_buddies.1
  unfold cL13ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L13 attention reduction uses ordinary K/V shards. -/
theorem canonical_l13_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10246 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10222,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10223]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10234,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10235]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10240,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10241]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5772)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5773)
        16 4 64 64 true 0 2 0 := by
  refine cL13A_reduce8 pm_goal_1 initPM 1341 cL13APm0
    10222 10223 10234 10235 10240 10241 5772 5773 10246
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL13A_nodes.2.1 ?_ (by native_decide)
    (cL13A_pm_nw 1342 10246 (by decide)) (by native_decide)
    (cL13A_pm_nw 1341 10222 (by decide)) (cL13A_pm_nw 1341 10223 (by decide))
    (cL13A_pm_nw 1341 10234 (by decide)) (cL13A_pm_nw 1341 10235 (by decide))
    (cL13A_pm_nw 1341 10240 (by decide)) (cL13A_pm_nw 1341 10241 (by decide))
    (cL13A_pm_nw 1341 5772 (by decide)) (cL13A_pm_nw 1341 5773 (by decide))
  intro s
  have hb := cL13A_buddies.2.1
  unfold cL13APm0 cL13APm1 at hb
  unfold cL13APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L13 attention reduction uses ordinary K/V shards. -/
theorem canonical_l13_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10247 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10222,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10223]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10234,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10235]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10240,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10241]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5772)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5773)
        16 4 64 64 true 0 2 1 := by
  refine cL13A_reduce8 pm_goal_1 initPM 1342 cL13APm1
    10222 10223 10234 10235 10240 10241 5772 5773 10247
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL13A_nodes.2.2 ?_ (by native_decide)
    (cL13A_pm_nw 1343 10247 (by decide)) (by native_decide)
    (cL13A_pm_nw 1342 10222 (by decide)) (cL13A_pm_nw 1342 10223 (by decide))
    (cL13A_pm_nw 1342 10234 (by decide)) (cL13A_pm_nw 1342 10235 (by decide))
    (cL13A_pm_nw 1342 10240 (by decide)) (cL13A_pm_nw 1342 10241 (by decide))
    (cL13A_pm_nw 1342 5772 (by decide)) (cL13A_pm_nw 1342 5773 (by decide))
  intro s
  have hb := cL13A_buddies.2.2
  unfold cL13APm0 cL13APm1 at hb
  unfold cL13APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L13 graph values. -/
theorem canonical_l13_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5769)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10222)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10223)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5770)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10234)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10235)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5771)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10240)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10241)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5772 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5772)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 5773 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5773)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5772 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5774)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10247)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [canonical_l13_attention_sm_reduce initSM,
    canonical_l13_attention_pm0_reduce initPM,
    canonical_l13_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The exact L13 attention relation exported from the sole computed incoming
interface plus the external ordinary K/V cache contract.  Q and both projected
K/V branches are closed internally at their real graph tids. -/
theorem canonical_l13_attention_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5761)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10212)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10213)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5772 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5774)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10246)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10247)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := canonical_l13_q_relation_from_incoming initSM initPM hPM hInit hIncoming
  have hK := canonical_l13_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l13_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := cL13A_external_input_eq initSM initPM hInit initGoal_5772
    (by native_decide) 5772 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := cL13A_external_input_eq initSM initPM hInit initGoal_5773
    (by native_decide) 5773 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact canonical_l13_attention_from_qkv initSM initPM hQ hK hV hCuSM hCuKV
    hCuAlias hDecoded

/-- Complete canonical L13 attention residual at the exact graph values.  The incoming
L13 stream is the only computed-lineage premise; the cache and cumulative-sequence metadata
are external contracts, while Q/K/V, projection weights, and residual transport
are discharged internally. -/
theorem canonical_l13_attention_residual_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5761)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10212)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10213)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5772 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10276)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10277)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := canonical_l13_attention_from_incoming_and_cache initSM initPM
    hPM hInit hIncoming hCache hCuAlias hDecoded
  have hResidual := canonical_l13_residual_from_incoming initSM initPM hIncoming
  have hWeight := cL13A_external_input_eq initSM initPM hInit initGoal_5778
    (by native_decide) 5778 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5778).shape = [1024, 1024] := by
    rw [cL13A_external_input_pm_value initPM 5778 (by native_decide)]
    exact hPM 5778 [1024, 1024] (by native_decide)
  exact canonical_l13_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

#print axioms canonical_l13_attention_from_qkv
#print axioms canonical_l13_attention_from_incoming_and_cache
#print axioms canonical_l13_attention_residual_from_incoming_and_cache

end
end TrainVerify.Denote.GeneratedPatterns
