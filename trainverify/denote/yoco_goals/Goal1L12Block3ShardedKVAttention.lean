/- Canonical Goal 1 L12 block 3: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.Goal1L12Block3AttentionComposition
import denote.yoco_goals.Goal1L12Block3KAlignment
import denote.yoco_goals.Goal1L12Block3KVGraph
import denote.yoco_goals.Goal1L12Block3Upstream
import denote.yoco_goals.Goal1L12Block3Output

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

private theorem b3A_reduce5
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

private theorem b3A_reduce8
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

private theorem b3A_init_singleton_eq (initSM initPM : Store)
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

private theorem b3A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := b3A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem b3A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def b3ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5715, 5716, 5717, 5718, 5719], outs := [5720, 5721],
    params := [16, 4, 64, 64, 1, 0] }
private def b3APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10068, 10080, 10086, 5718, 5719], outs := [10092, 5721],
    params := [16, 4, 64, 64, 1, 0] }
private def b3APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10069, 10081, 10087, 5718, 5719], outs := [10093, 5721],
    params := [16, 4, 64, 64, 1, 0] }

private theorem b3A_nodes :
    sm_goal_1.nodes[575]'(by native_decide) = b3ASm ∧
    pm_goal_1.nodes[1265]'(by native_decide) = b3APm0 ∧
    pm_goal_1.nodes[1266]'(by native_decide) = b3APm1 := by native_decide
private theorem b3A_buddies :
    sm_goal_1.replicaBuddies b3ASm = [b3ASm] ∧
    pm_goal_1.replicaBuddies b3APm0 = [b3APm0, b3APm1] ∧
    pm_goal_1.replicaBuddies b3APm1 = [b3APm0, b3APm1] := by native_decide

private theorem b3A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(576, 5720), (575, 5715), (575, 5716), (575, 5717),
      (575, 5718), (575, 5719)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem b3A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1266, 10092), (1267, 10093),
      (1265, 10068), (1265, 10069), (1265, 10080), (1265, 10081),
      (1265, 10086), (1265, 10087), (1265, 5718), (1265, 5719),
      (1266, 10068), (1266, 10069), (1266, 10080), (1266, 10081),
      (1266, 10086), (1266, 10087), (1266, 5718), (1266, 5719)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L12 block 3 attention reduction. -/
theorem goal1_l12_block3_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5720 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5715)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5716)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5717)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5718)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5719)
        16 4 64 64 true 0 := by
  refine b3A_reduce5 sm_goal_1 initSM 575 b3ASm 5715 5716 5717 5718 5719 5720
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) b3A_nodes.1 ?_ (by native_decide)
    (b3A_sm_nw 576 5720 (by decide)) (by native_decide)
    (b3A_sm_nw 575 5715 (by decide)) (b3A_sm_nw 575 5716 (by decide))
    (b3A_sm_nw 575 5717 (by decide)) (b3A_sm_nw 575 5718 (by decide))
    (b3A_sm_nw 575 5719 (by decide))
  intro s
  have hb := b3A_buddies.1
  unfold b3ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L12 block 3 attention reduction uses ordinary K/V shards. -/
theorem goal1_l12_block3_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10092 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10068,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10069]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10080,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10081]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10086,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10087]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5718)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5719)
        16 4 64 64 true 0 2 0 := by
  refine b3A_reduce8 pm_goal_1 initPM 1265 b3APm0
    10068 10069 10080 10081 10086 10087 5718 5719 10092
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) b3A_nodes.2.1 ?_ (by native_decide)
    (b3A_pm_nw 1266 10092 (by decide)) (by native_decide)
    (b3A_pm_nw 1265 10068 (by decide)) (b3A_pm_nw 1265 10069 (by decide))
    (b3A_pm_nw 1265 10080 (by decide)) (b3A_pm_nw 1265 10081 (by decide))
    (b3A_pm_nw 1265 10086 (by decide)) (b3A_pm_nw 1265 10087 (by decide))
    (b3A_pm_nw 1265 5718 (by decide)) (b3A_pm_nw 1265 5719 (by decide))
  intro s
  have hb := b3A_buddies.2.1
  unfold b3APm0 b3APm1 at hb
  unfold b3APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L12 block 3 attention reduction uses ordinary K/V shards. -/
theorem goal1_l12_block3_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10093 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10068,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10069]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10080,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10081]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10086,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10087]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5718)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5719)
        16 4 64 64 true 0 2 1 := by
  refine b3A_reduce8 pm_goal_1 initPM 1266 b3APm1
    10068 10069 10080 10081 10086 10087 5718 5719 10093
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) b3A_nodes.2.2 ?_ (by native_decide)
    (b3A_pm_nw 1267 10093 (by decide)) (by native_decide)
    (b3A_pm_nw 1266 10068 (by decide)) (b3A_pm_nw 1266 10069 (by decide))
    (b3A_pm_nw 1266 10080 (by decide)) (b3A_pm_nw 1266 10081 (by decide))
    (b3A_pm_nw 1266 10086 (by decide)) (b3A_pm_nw 1266 10087 (by decide))
    (b3A_pm_nw 1266 5718 (by decide)) (b3A_pm_nw 1266 5719 (by decide))
  intro s
  have hb := b3A_buddies.2.2
  unfold b3APm0 b3APm1 at hb
  unfold b3APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L12 block 3 graph values. -/
theorem goal1_l12_block3_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5715)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10068)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10069)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5716)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10080)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10081)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5717)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10086)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10087)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5718)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 5719 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5719)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5720)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10093)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [goal1_l12_block3_attention_sm_reduce initSM,
    goal1_l12_block3_attention_pm0_reduce initPM,
    goal1_l12_block3_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The exact L12 block 3 attention relation exported from the sole computed incoming
interface plus the external ordinary K/V cache contract.  Q and both projected
K/V branches are closed internally at their real graph tids. -/
theorem goal1_l12_block3_attention_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5720)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10092)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10093)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := goal1_l12_block3_q_relation_from_incoming initSM initPM hPM hInit hIncoming
  have hK := goal1_l12_block3_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := goal1_l12_block3_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := b3A_external_input_eq initSM initPM hInit initGoal_5718
    (by native_decide) 5718 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := b3A_external_input_eq initSM initPM hInit initGoal_5719
    (by native_decide) 5719 rfl rfl rfl rfl (by native_decide) (by native_decide)
  exact goal1_l12_block3_attention_from_qkv initSM initPM hQ hK hV hCuSM hCuKV
    hCuAlias hDecoded

/-- Complete canonical L12 block 3 attention residual at the exact graph values.  The incoming
L12 block 3 stream is the only computed-lineage premise; the cache and cumulative-sequence metadata
are external contracts, while Q/K/V, projection weights, and residual transport
are discharged internally. -/
theorem goal1_l12_block3_attention_residual_from_incoming_and_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024])
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hAttention := goal1_l12_block3_attention_from_incoming_and_cache initSM initPM
    hPM hInit hIncoming hCache hCuAlias hDecoded
  have hResidual := goal1_l12_block3_residual_from_incoming initSM initPM hIncoming
  have hWeight := b3A_external_input_eq initSM initPM hInit initGoal_5724
    (by native_decide) 5724 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5724).shape = [1024, 1024] := by
    rw [b3A_external_input_pm_value initPM 5724 (by native_decide)]
    exact hPM 5724 [1024, 1024] (by native_decide)
  exact goal1_l12_block3_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

/-- The exact block-3 attention residual from the two permitted computed
interfaces.  Packed-cu facts come only from the external input contract. -/
theorem goal1_l12_block3_attention_residual_from_stream_cache
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1ExternalInputContract initSM initPM)
    (hStream : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5707)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024])
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5728)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10122)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10123)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hcuInit : initPM 5718 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5718 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [b3A_external_input_pm_value initPM 5718 (by native_decide),
      b3A_external_input_pm_value initPM 6252 (by native_decide), hcuInit]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [b3A_external_input_pm_value initPM 6252 (by native_decide)]
    exact hContract.2.2.1.decoded_single
  exact goal1_l12_block3_attention_residual_from_incoming_and_cache
    initSM initPM hPM hInit hStream hCache hCuAlias hDecoded

#print axioms goal1_l12_block3_attention_from_qkv
#print axioms goal1_l12_block3_attention_from_incoming_and_cache
#print axioms goal1_l12_block3_attention_residual_from_incoming_and_cache

end
end TrainVerify.Denote.GeneratedPatterns
