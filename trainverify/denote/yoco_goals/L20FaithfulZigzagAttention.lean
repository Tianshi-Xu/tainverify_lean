import denote.yoco_goals.L19FaithfulBlockTail
import denote.yoco_goals.L19FaithfulZigzagAttention
import denote.yoco_goals.L2to11FaithfulKVBoundaryA
import denote.yoco_goals.L2to11FaithfulKVBoundaryB

/-!
# Block 8 faithful zigzag attention (goal 5739)

Structural clone of `L14FaithfulZigzagAttention` (block 7, goal 5690), shifted to
the fourth decoder block:

| | block 7 | block 8 |
|---|---|---|
| SM node | 750 | 785 |
| PM ranks | 1562 / 1563 → 10891 / 10892 | 1632 / 1633 → 11063 / 11064 |
| Q parent | `recon_zigzagGoal_5685_faithful` | `recon_zigzagGoal_5734_faithful` |
| K/V | 5686 / 5687 | 5735 / 5736 |
| cu | 5688 / 5689 | 5737 / 5738 |

No new axioms and no new hypotheses.
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

private theorem l20_dgdf_reduce5
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

private theorem l20_dgdf_reduce6
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 in5 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4) (s in5))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs)
    (hpre5 : ∀ n ∈ g.nodes.drop k, in5 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4)
        (denoteGraphDistributedFaithful g init in5) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4,
    denoteGraphDistributedFaithful_prefix_read g init k in5 hpreNil hpre5]

private def l20SmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5734, 5735, 5736, 5737, 5738], outs := [5739],
    params := [16, 4, 64, 64, 1, 0] }
private def l20PmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11039, 5735, 5736, 5737, 5738], outs := [11063],
    params := [16, 4, 64, 64, 1, 0] }
private def l20PmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11040, 5735, 5736, 5737, 5738], outs := [11064],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
private theorem l20_attn_native_facts :
    sm.nodes[785]'(by native_decide) = l20SmAttn ∧
    pm.nodes[1632]'(by native_decide) = l20PmAttn0 ∧
    pm.nodes[1633]'(by native_decide) = l20PmAttn1 ∧
    sm.replicaBuddies l20SmAttn = [l20SmAttn] ∧
    pm.replicaBuddies l20PmAttn0 = [l20PmAttn0, l20PmAttn1] ∧
    pm.replicaBuddies l20PmAttn1 = [l20PmAttn0, l20PmAttn1] := by
  native_decide

private theorem l20_faithful_nonempty_sm_5739 (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l20_faithful_nonempty_pm_5739 (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l20_attn_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(786, 5739), (785, 5734), (785, 5735), (785, 5736),
      (785, 5737), (785, 5738)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l20_attn_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1633, 11063), (1634, 11064),
      (1632, 11039), (1632, 11040), (1632, 5735), (1632, 5736),
      (1632, 5737), (1632, 5738), (1633, 11039), (1633, 11040),
      (1633, 5735), (1633, 5736), (1633, 5737), (1633, 5738)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l20_attn_metadata_not_written :
    (∀ n ∈ sm.nodes, 5688 ∉ n.outs ∧ 5737 ∉ n.outs ∧ 5738 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5688 ∉ n.outs ∧ 5737 ∉ n.outs ∧ 5738 ∉ n.outs) := by
  native_decide

private theorem l20_init_singleton_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid) :
    initSM tid = initPM tid := by
  have h := hInit g hg
  unfold InitGoalHolds at h
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, htp, hts, hgd] at hv
  simpa only [List.map, reconstructWithDim] using hv

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Block-8 faithful generated cross-decoder attention goal 5739.
theorem recon_zigzagGoal_5739_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5739)
      (denoteGraphDistributedFaithful pm initPM 11063)
      (denoteGraphDistributedFaithful pm initPM 11064)
      (denoteGraphDistributedFaithful pm initPM 5737)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := recon_zigzagGoal_5734_faithful initSM initPM hSM hPM hInit hValues hCu
  have hK := recon_intermediateGoal_5735_faithful initSM initPM hSM hPM hInit hValues hCu
  have hV := recon_intermediateGoal_5736_faithful initSM initPM hSM hPM hInit hValues hCu
  have hkval := oneTp_valeq intermediateGoal_5735 _ _ 5735 rfl rfl rfl rfl hK
  have hvval := oneTp_valeq intermediateGoal_5736 _ _ 5736 rfl rfl rfl rfl hV
  rcases l20_attn_native_facts with ⟨sn, pn0, pn1, sb, pb0, pb1⟩
  have sbLit := sb
  have pb0Lit := pb0
  have pb1Lit := pb1
  unfold l20SmAttn at sbLit
  unfold l20PmAttn0 l20PmAttn1 at pb0Lit pb1Lit
  rcases l20_attn_metadata_not_written with ⟨smnw, pmnw⟩
  have hqInit := l20_init_singleton_eq initSM initPM hInit initGoal_4694
    (by native_decide) 4694 rfl rfl rfl rfl
  have hkInit := l20_init_singleton_eq initSM initPM hInit initGoal_4695
    (by native_decide) 4695 rfl rfl rfl rfl
  have sm4694_5737 : initSM 4694 = initSM 5737 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4694_5737 : initPM 4694 = initPM 5737 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have sm4695_5738 : initSM 4695 = initSM 5738 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4695_5738 : initPM 4695 = initPM 5738 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_pm
      (by native_decide) (by native_decide)
  have smFinal (tid : Tid) (hw : ∀ n ∈ sm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful sm initSM tid = initSM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
      layer1_sm_nodes_nonempty hw
  have pmFinal (tid : Tid) (hw : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
      denoteGraphDistributedFaithful pm initPM tid = initPM tid := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hw
  have hcuQ : denoteGraphDistributedFaithful sm initSM 5737 =
      denoteGraphDistributedFaithful pm initPM 5737 := by
    rw [smFinal 5737 (fun n hn => (smnw n hn).2.1),
      pmFinal 5737 (fun n hn => (pmnw n hn).2.1), ← sm4694_5737,
      ← pm4694_5737, hqInit]
  have hcuKV : denoteGraphDistributedFaithful sm initSM 5738 =
      denoteGraphDistributedFaithful pm initPM 5738 := by
    rw [smFinal 5738 (fun n hn => (smnw n hn).2.2),
      pmFinal 5738 (fun n hn => (pmnw n hn).2.2), ← sm4695_5738,
      ← pm4695_5738, hkInit]
  have h5688_5737 : denoteGraphDistributedFaithful pm initPM 5688 =
      denoteGraphDistributedFaithful pm initPM 5737 := by
    rw [pmFinal 5688 (fun n hn => (pmnw n hn).1),
      pmFinal 5737 (fun n hn => (pmnw n hn).2.1)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5688).shape = [2] := by
    rw [pmFinal 5688 (fun n hn => (pmnw n hn).1)]
    exact hPM 5688 [2] (by native_decide)
  have hdecodedLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5688)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  rcases hQ with ⟨source0, source1, hs⟩
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5688) = [0, 4096] := by
    apply list_eq_pair_of_length_head_last _ 4096 hdecodedLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    exact ht.symm
  have hSMred : denoteGraphDistributedFaithful sm initSM 5739 =
      fw_attn_varlen (denoteGraphDistributedFaithful sm initSM 5734)
        (denoteGraphDistributedFaithful sm initSM 5735)
        (denoteGraphDistributedFaithful sm initSM 5736)
        (denoteGraphDistributedFaithful sm initSM 5737)
        (denoteGraphDistributedFaithful sm initSM 5738) 16 4 64 64 true 0 := by
    refine l20_dgdf_reduce5 sm initSM 785 l20SmAttn
      5734 5735 5736 5737 5738 5739
      (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
      (by native_decide) sn ?_ (l20_faithful_nonempty_sm_5739 786)
      (l20_attn_sm_not_written 786 5739 (by decide))
      (l20_faithful_nonempty_sm_5739 785)
      (l20_attn_sm_not_written 785 5734 (by decide))
      (l20_attn_sm_not_written 785 5735 (by decide))
      (l20_attn_sm_not_written 785 5736 (by decide))
      (l20_attn_sm_not_written 785 5737 (by decide))
      (l20_attn_sm_not_written 785 5738 (by decide))
    intro s
    unfold l20SmAttn
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [sbLit]
    rfl
  have hP0red : denoteGraphDistributedFaithful pm initPM 11063 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 11039,
         denoteGraphDistributedFaithful pm initPM 11040]
        (denoteGraphDistributedFaithful pm initPM 5735)
        (denoteGraphDistributedFaithful pm initPM 5736)
        (denoteGraphDistributedFaithful pm initPM 5737)
        (denoteGraphDistributedFaithful pm initPM 5738) 16 4 64 64 true 0 2 0 := by
    refine l20_dgdf_reduce6 pm initPM 1632 l20PmAttn0
      11039 11040 5735 5736 5737 5738 11063
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
      (by native_decide) pn0 ?_ (l20_faithful_nonempty_pm_5739 1633)
      (l20_attn_pm_not_written 1633 11063 (by decide))
      (l20_faithful_nonempty_pm_5739 1632)
      (l20_attn_pm_not_written 1632 11039 (by decide))
      (l20_attn_pm_not_written 1632 11040 (by decide))
      (l20_attn_pm_not_written 1632 5735 (by decide))
      (l20_attn_pm_not_written 1632 5736 (by decide))
      (l20_attn_pm_not_written 1632 5737 (by decide))
      (l20_attn_pm_not_written 1632 5738 (by decide))
    intro s
    unfold l20PmAttn0
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb0Lit]
    rfl
  have hP1red : denoteGraphDistributedFaithful pm initPM 11064 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 11039,
         denoteGraphDistributedFaithful pm initPM 11040]
        (denoteGraphDistributedFaithful pm initPM 5735)
        (denoteGraphDistributedFaithful pm initPM 5736)
        (denoteGraphDistributedFaithful pm initPM 5737)
        (denoteGraphDistributedFaithful pm initPM 5738) 16 4 64 64 true 0 2 1 := by
    refine l20_dgdf_reduce6 pm initPM 1633 l20PmAttn1
      11039 11040 5735 5736 5737 5738 11064
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
      (by native_decide) pn1 ?_ (l20_faithful_nonempty_pm_5739 1634)
      (l20_attn_pm_not_written 1634 11064 (by decide))
      (l20_faithful_nonempty_pm_5739 1633)
      (l20_attn_pm_not_written 1633 11039 (by decide))
      (l20_attn_pm_not_written 1633 11040 (by decide))
      (l20_attn_pm_not_written 1633 5735 (by decide))
      (l20_attn_pm_not_written 1633 5736 (by decide))
      (l20_attn_pm_not_written 1633 5737 (by decide))
      (l20_attn_pm_not_written 1633 5738 (by decide))
    intro s
    unfold l20PmAttn1
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb1Lit]
    rfl
  rw [hSMred, hP0red, hP1red, hkval, hvval, hcuQ, hcuKV]
  apply Zigzag2Rel.attn_zigzag
    (lDim := 2048) (qHeads := 16) (kvHeads := 4) (qDim := 64) (vDim := 64)
    (causal := true) (window := 0) (hrel := ⟨source0, source1, hs⟩)
  · exact h5688_5737.symm
  · simpa only [Nat.reduceMul] using hdecoded
  · decide
  · decide
  · decide
  · decide
  · decide

end
end TrainVerify.Denote.GeneratedPatterns
