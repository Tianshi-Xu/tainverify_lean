/- Canonical Goal 1 L12: faithful reductions and mixed-layout sharded-K/V attention. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.CanonicalL12AttentionComposition
import denote.yoco_goals.CanonicalL12KAlignment
import denote.yoco_goals.CanonicalL12KVGraph
import denote.yoco_goals.CanonicalL12ZigzagEntry
import denote.yoco_goals.CanonicalL12Output

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

private theorem cL12A_reduce5
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

private theorem cL12A_reduce8
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

private theorem cL12A_init_singleton_eq (initSM initPM : Store)
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

private theorem cL12A_external_input_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsm : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL12A_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM tid (by native_decide) hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM tid (by native_decide) hpm,
    hi]

private theorem cL12A_external_input_pm_value (initPM : Store) (tid : Tid)
    (hnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hnw

private def cL12ASm : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5607, 5608, 5609, 5610, 5611], outs := [5612, 5613],
    params := [16, 4, 64, 64, 1, 0] }
private def cL12APm0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9754, 9766, 9774, 5610, 5611], outs := [9782, 5613],
    params := [16, 4, 64, 64, 1, 0] }
private def cL12APm1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9755, 9767, 9775, 5610, 5611], outs := [9783, 5613],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL12A_nodes :
    sm_goal_1.nodes[505]'(by native_decide) = cL12ASm ∧
    pm_goal_1.nodes[1113]'(by native_decide) = cL12APm0 ∧
    pm_goal_1.nodes[1114]'(by native_decide) = cL12APm1 := by native_decide
private theorem cL12A_buddies :
    sm_goal_1.replicaBuddies cL12ASm = [cL12ASm] ∧
    pm_goal_1.replicaBuddies cL12APm0 = [cL12APm0, cL12APm1] ∧
    pm_goal_1.replicaBuddies cL12APm1 = [cL12APm0, cL12APm1] := by native_decide

private theorem cL12A_sm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(506, 5612), (505, 5607), (505, 5608), (505, 5609),
      (505, 5610), (505, 5611)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL12A_pm_nw (k tid : Nat)
    (h : (k, tid) ∈ [(1114, 9782), (1115, 9783),
      (1113, 9754), (1113, 9755), (1113, 9766), (1113, 9767),
      (1113, 9774), (1113, 9775), (1113, 5610), (1113, 5611),
      (1114, 9754), (1114, 9755), (1114, 9766), (1114, 9767),
      (1114, 9774), (1114, 9775), (1114, 5610), (1114, 5611)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact faithful SM L12 attention reduction. -/
theorem canonical_l12_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5612 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5607)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5608)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5609)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5610)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5611)
        16 4 64 64 true 0 := by
  refine cL12A_reduce5 sm_goal_1 initSM 505 cL12ASm 5607 5608 5609 5610 5611 5612
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL12A_nodes.1 ?_ (by native_decide)
    (cL12A_sm_nw 506 5612 (by decide)) (by native_decide)
    (cL12A_sm_nw 505 5607 (by decide)) (cL12A_sm_nw 505 5608 (by decide))
    (cL12A_sm_nw 505 5609 (by decide)) (cL12A_sm_nw 505 5610 (by decide))
    (cL12A_sm_nw 505 5611 (by decide))
  intro s
  have hb := cL12A_buddies.1
  unfold cL12ASm at hb ⊢
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-0 L12 attention reduction uses ordinary K/V shards. -/
theorem canonical_l12_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9782 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9754,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9755]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9766,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9767]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9774,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9775]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5610)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5611)
        16 4 64 64 true 0 2 0 := by
  refine cL12A_reduce8 pm_goal_1 initPM 1113 cL12APm0
    9754 9755 9766 9767 9774 9775 5610 5611 9782
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL12A_nodes.2.1 ?_ (by native_decide)
    (cL12A_pm_nw 1114 9782 (by decide)) (by native_decide)
    (cL12A_pm_nw 1113 9754 (by decide)) (cL12A_pm_nw 1113 9755 (by decide))
    (cL12A_pm_nw 1113 9766 (by decide)) (cL12A_pm_nw 1113 9767 (by decide))
    (cL12A_pm_nw 1113 9774 (by decide)) (cL12A_pm_nw 1113 9775 (by decide))
    (cL12A_pm_nw 1113 5610 (by decide)) (cL12A_pm_nw 1113 5611 (by decide))
  intro s
  have hb := cL12A_buddies.2.1
  unfold cL12APm0 cL12APm1 at hb
  unfold cL12APm0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Exact faithful PM rank-1 L12 attention reduction uses ordinary K/V shards. -/
theorem canonical_l12_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9783 =
      fw_attn_zigzag_collective_sharded_kv
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9754,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9755]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9766,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9767]
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9774,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9775]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5610)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5611)
        16 4 64 64 true 0 2 1 := by
  refine cL12A_reduce8 pm_goal_1 initPM 1114 cL12APm1
    9754 9755 9766 9767 9774 9775 5610 5611 9783
    (fun q0 q1 k0 k1 v0 v1 cq ck => fw_attn_zigzag_collective_sharded_kv
      [q0, q1] [k0, k1] [v0, v1] cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL12A_nodes.2.2 ?_ (by native_decide)
    (cL12A_pm_nw 1115 9783 (by decide)) (by native_decide)
    (cL12A_pm_nw 1114 9754 (by decide)) (cL12A_pm_nw 1114 9755 (by decide))
    (cL12A_pm_nw 1114 9766 (by decide)) (cL12A_pm_nw 1114 9767 (by decide))
    (cL12A_pm_nw 1114 9774 (by decide)) (cL12A_pm_nw 1114 9775 (by decide))
    (cL12A_pm_nw 1114 5610 (by decide)) (cL12A_pm_nw 1114 5611 (by decide))
  intro s
  have hb := cL12A_buddies.2.2
  unfold cL12APm0 cL12APm1 at hb
  unfold cL12APm1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs storeSet
  simp only [List.map, List.find?_cons]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- Mixed-layout attention transport at the exact canonical L12 graph values. -/
theorem canonical_l12_attention_from_qkv
    (initSM initPM : Store)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5607)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9755)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5608)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9766)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9767)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5609)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9774)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9775)
      [4096, 4, 64] [2048, 4, 64])
    (hCuSM : denoteGraphDistributedFaithful sm_goal_1 initSM 5610 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5610)
    (hCuKV : denoteGraphDistributedFaithful sm_goal_1 initSM 5611 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5611)
    (hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5610 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5612)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9782)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9783)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  rw [canonical_l12_attention_sm_reduce initSM,
    canonical_l12_attention_pm0_reduce initPM,
    canonical_l12_attention_pm1_reduce initPM, hCuSM, hCuKV, hCuAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv _ _ _ _ _ _ _ _ _ _ _ _
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)


private def cL12ASmEntryMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5603], outs := [8500, 8504], params := [2] }
private def cL12APmEntryMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9750], outs := [16086, 16090], params := [2] }
private def cL12APmEntryMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9751], outs := [16094, 16098], params := [2] }

private theorem cL12A_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL12A_red_sm8504 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8504 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5603 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 474 cL12ASmEntryMulti
    5603 8504 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro st
  unfold cL12ASmEntryMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12A_apply_multiref_second sm_goal_1 st 0 5603 8500 8504 (by decide)

private theorem cL12A_red_pm16090 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16090 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9750 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1047 cL12APmEntryMulti0
    9750 16090 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro st
  unfold cL12APmEntryMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12A_apply_multiref_second pm_goal_1 st 0 9750 16086 16090 (by decide)

private theorem cL12A_red_pm16098 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 16098 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9751 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1049 cL12APmEntryMulti1
    9751 16098 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro st
  unfold cL12APmEntryMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12A_apply_multiref_second pm_goal_1 st 1 9751 16094 16098 (by decide)

private theorem canonical_l12_residual_from_entry (initSM initPM : Store)
    (hEntry : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5603)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9750)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9751)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8504)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16090)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16098)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  rw [cL12A_red_sm8504 initSM, cL12A_red_pm16090 initPM, cL12A_red_pm16098 initPM]
  exact hEntry

/-- Goal-1 exact-scope L12 attention front half, closed from external contracts.
The entry, RMSNorm, Q/K/V, sharded-K/V zigzag attention, projection, and attention
residual are all computed internally in `sm_goal_1` / `pm_goal_1`. -/
theorem goal1_external_to_l12_attention_residual
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1ExternalInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hEntry := goal1_external_to_l12_zigzag_entry initSM initPM hSM hPM hInit hContract
  have hCache := goal1_external_to_cache_faithful_composition initSM initPM hSM hPM hInit
  have hQ := canonical_l12_q_relation_from_entry initSM initPM hPM hInit hEntry
  have hK := canonical_l12_k_ordinary_relation initSM initPM hPM hInit hCache
  have hV := canonical_l12_v_ordinary_relation initSM initPM hPM hInit hCache
  have hCuSM := cL12A_external_input_eq initSM initPM hInit initGoal_5610
    (by native_decide) 5610 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hCuKV := cL12A_external_input_eq initSM initPM hInit initGoal_5611
    (by native_decide) 5611 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcuInit : initPM 5610 = initPM 6252 :=
    hContract.2.1.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hCuAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5610 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [cL12A_external_input_pm_value initPM 5610 (by native_decide),
      cL12A_external_input_pm_value initPM 6252 (by native_decide), hcuInit]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [cL12A_external_input_pm_value initPM 6252 (by native_decide)]
    exact hContract.2.2.1.decoded_single
  have hAttention := canonical_l12_attention_from_qkv initSM initPM hQ hK hV
    hCuSM hCuKV hCuAlias hDecoded
  have hResidual := canonical_l12_residual_from_entry initSM initPM hEntry
  have hWeight := cL12A_external_input_eq initSM initPM hInit initGoal_5616
    (by native_decide) 5616 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hWeightShape :
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5616).shape = [1024, 1024] := by
    rw [cL12A_external_input_pm_value initPM 5616 (by native_decide)]
    exact hPM 5616 [1024, 1024] (by native_decide)
  exact canonical_l12_output_from_inputs initSM initPM hResidual hAttention
    hWeight hWeightShape

#print axioms canonical_l12_attention_from_qkv
#print axioms goal1_external_to_l12_attention_residual

end
end TrainVerify.Denote.GeneratedPatterns
