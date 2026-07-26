import denote.yoco_goals.L16FaithfulBlockTail
import denote.yoco_goals.L16FaithfulZigzagAttention
import denote.yoco_goals.L2to11FaithfulKVBoundaryA
import denote.yoco_goals.L2to11FaithfulKVBoundaryB

/-!
# Block 5 faithful zigzag attention (goal 5592)

Structural clone of `L14FaithfulZigzagAttention` (block 4, goal 5543), shifted to
the fourth decoder block:

| | block 4 | block 5 |
|---|---|---|
| SM node | 645 | 680 |
| PM ranks | 1352 / 1353 → 10375 / 10376 | 1422 / 1423 → 10547 / 10548 |
| Q parent | `recon_zigzagGoal_5538_faithful` | `recon_zigzagGoal_5587_faithful` |
| K/V | 5539 / 5540 | 5588 / 5589 |
| cu | 5541 / 5542 | 5590 / 5591 |

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

private theorem l17_dgdf_reduce5
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

private theorem l17_dgdf_reduce6
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

private def l17SmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5587, 5588, 5589, 5590, 5591], outs := [5592],
    params := [16, 4, 64, 64, 1, 0] }
private def l17PmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10523, 5588, 5589, 5590, 5591], outs := [10547],
    params := [16, 4, 64, 64, 1, 0] }
private def l17PmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10524, 5588, 5589, 5590, 5591], outs := [10548],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
private theorem l17_attn_native_facts :
    sm.nodes[680]'(by native_decide) = l17SmAttn ∧
    pm.nodes[1422]'(by native_decide) = l17PmAttn0 ∧
    pm.nodes[1423]'(by native_decide) = l17PmAttn1 ∧
    sm.replicaBuddies l17SmAttn = [l17SmAttn] ∧
    pm.replicaBuddies l17PmAttn0 = [l17PmAttn0, l17PmAttn1] ∧
    pm.replicaBuddies l17PmAttn1 = [l17PmAttn0, l17PmAttn1] := by
  native_decide

private theorem l17_faithful_nonempty_sm_5592 (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l17_faithful_nonempty_pm_5592 (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l17_attn_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(681, 5592), (680, 5587), (680, 5588), (680, 5589),
      (680, 5590), (680, 5591)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l17_attn_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1423, 10547), (1424, 10548),
      (1422, 10523), (1422, 10524), (1422, 5588), (1422, 5589),
      (1422, 5590), (1422, 5591), (1423, 10523), (1423, 10524),
      (1423, 5588), (1423, 5589), (1423, 5590), (1423, 5591)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l17_attn_metadata_not_written :
    (∀ n ∈ sm.nodes, 5541 ∉ n.outs ∧ 5590 ∉ n.outs ∧ 5591 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5541 ∉ n.outs ∧ 5590 ∉ n.outs ∧ 5591 ∉ n.outs) := by
  native_decide

private theorem l17_init_singleton_eq (initSM initPM : Store)
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
-- Block-5 faithful generated cross-decoder attention goal 5592.
theorem recon_zigzagGoal_5592_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5592)
      (denoteGraphDistributedFaithful pm initPM 10547)
      (denoteGraphDistributedFaithful pm initPM 10548)
      (denoteGraphDistributedFaithful pm initPM 5590)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := recon_zigzagGoal_5587_faithful initSM initPM hSM hPM hInit hValues hCu
  have hK := recon_intermediateGoal_5588_faithful initSM initPM hSM hPM hInit hValues hCu
  have hV := recon_intermediateGoal_5589_faithful initSM initPM hSM hPM hInit hValues hCu
  have hkval := oneTp_valeq intermediateGoal_5588 _ _ 5588 rfl rfl rfl rfl hK
  have hvval := oneTp_valeq intermediateGoal_5589 _ _ 5589 rfl rfl rfl rfl hV
  rcases l17_attn_native_facts with ⟨sn, pn0, pn1, sb, pb0, pb1⟩
  have sbLit := sb
  have pb0Lit := pb0
  have pb1Lit := pb1
  unfold l17SmAttn at sbLit
  unfold l17PmAttn0 l17PmAttn1 at pb0Lit pb1Lit
  rcases l17_attn_metadata_not_written with ⟨smnw, pmnw⟩
  have hqInit := l17_init_singleton_eq initSM initPM hInit initGoal_4694
    (by native_decide) 4694 rfl rfl rfl rfl
  have hkInit := l17_init_singleton_eq initSM initPM hInit initGoal_4695
    (by native_decide) 4695 rfl rfl rfl rfl
  have sm4694_5590 : initSM 4694 = initSM 5590 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4694_5590 : initPM 4694 = initPM 5590 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have sm4695_5591 : initSM 4695 = initSM 5591 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4695_5591 : initPM 4695 = initPM 5591 :=
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
  have hcuQ : denoteGraphDistributedFaithful sm initSM 5590 =
      denoteGraphDistributedFaithful pm initPM 5590 := by
    rw [smFinal 5590 (fun n hn => (smnw n hn).2.1),
      pmFinal 5590 (fun n hn => (pmnw n hn).2.1), ← sm4694_5590,
      ← pm4694_5590, hqInit]
  have hcuKV : denoteGraphDistributedFaithful sm initSM 5591 =
      denoteGraphDistributedFaithful pm initPM 5591 := by
    rw [smFinal 5591 (fun n hn => (smnw n hn).2.2),
      pmFinal 5591 (fun n hn => (pmnw n hn).2.2), ← sm4695_5591,
      ← pm4695_5591, hkInit]
  have h5541_5590 : denoteGraphDistributedFaithful pm initPM 5541 =
      denoteGraphDistributedFaithful pm initPM 5590 := by
    rw [pmFinal 5541 (fun n hn => (pmnw n hn).1),
      pmFinal 5590 (fun n hn => (pmnw n hn).2.1)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5541).shape = [2] := by
    rw [pmFinal 5541 (fun n hn => (pmnw n hn).1)]
    exact hPM 5541 [2] (by native_decide)
  have hdecodedLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5541)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  rcases hQ with ⟨source0, source1, hs⟩
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5541) = [0, 4096] := by
    apply list_eq_pair_of_length_head_last _ 4096 hdecodedLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    exact ht.symm
  have hSMred : denoteGraphDistributedFaithful sm initSM 5592 =
      fw_attn_varlen (denoteGraphDistributedFaithful sm initSM 5587)
        (denoteGraphDistributedFaithful sm initSM 5588)
        (denoteGraphDistributedFaithful sm initSM 5589)
        (denoteGraphDistributedFaithful sm initSM 5590)
        (denoteGraphDistributedFaithful sm initSM 5591) 16 4 64 64 true 0 := by
    refine l17_dgdf_reduce5 sm initSM 680 l17SmAttn
      5587 5588 5589 5590 5591 5592
      (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
      (by native_decide) sn ?_ (l17_faithful_nonempty_sm_5592 681)
      (l17_attn_sm_not_written 681 5592 (by decide))
      (l17_faithful_nonempty_sm_5592 680)
      (l17_attn_sm_not_written 680 5587 (by decide))
      (l17_attn_sm_not_written 680 5588 (by decide))
      (l17_attn_sm_not_written 680 5589 (by decide))
      (l17_attn_sm_not_written 680 5590 (by decide))
      (l17_attn_sm_not_written 680 5591 (by decide))
    intro s
    unfold l17SmAttn
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [sbLit]
    rfl
  have hP0red : denoteGraphDistributedFaithful pm initPM 10547 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 10523,
         denoteGraphDistributedFaithful pm initPM 10524]
        (denoteGraphDistributedFaithful pm initPM 5588)
        (denoteGraphDistributedFaithful pm initPM 5589)
        (denoteGraphDistributedFaithful pm initPM 5590)
        (denoteGraphDistributedFaithful pm initPM 5591) 16 4 64 64 true 0 2 0 := by
    refine l17_dgdf_reduce6 pm initPM 1422 l17PmAttn0
      10523 10524 5588 5589 5590 5591 10547
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
      (by native_decide) pn0 ?_ (l17_faithful_nonempty_pm_5592 1423)
      (l17_attn_pm_not_written 1423 10547 (by decide))
      (l17_faithful_nonempty_pm_5592 1422)
      (l17_attn_pm_not_written 1422 10523 (by decide))
      (l17_attn_pm_not_written 1422 10524 (by decide))
      (l17_attn_pm_not_written 1422 5588 (by decide))
      (l17_attn_pm_not_written 1422 5589 (by decide))
      (l17_attn_pm_not_written 1422 5590 (by decide))
      (l17_attn_pm_not_written 1422 5591 (by decide))
    intro s
    unfold l17PmAttn0
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb0Lit]
    rfl
  have hP1red : denoteGraphDistributedFaithful pm initPM 10548 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 10523,
         denoteGraphDistributedFaithful pm initPM 10524]
        (denoteGraphDistributedFaithful pm initPM 5588)
        (denoteGraphDistributedFaithful pm initPM 5589)
        (denoteGraphDistributedFaithful pm initPM 5590)
        (denoteGraphDistributedFaithful pm initPM 5591) 16 4 64 64 true 0 2 1 := by
    refine l17_dgdf_reduce6 pm initPM 1423 l17PmAttn1
      10523 10524 5588 5589 5590 5591 10548
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
      (by native_decide) pn1 ?_ (l17_faithful_nonempty_pm_5592 1424)
      (l17_attn_pm_not_written 1424 10548 (by decide))
      (l17_faithful_nonempty_pm_5592 1423)
      (l17_attn_pm_not_written 1423 10523 (by decide))
      (l17_attn_pm_not_written 1423 10524 (by decide))
      (l17_attn_pm_not_written 1423 5588 (by decide))
      (l17_attn_pm_not_written 1423 5589 (by decide))
      (l17_attn_pm_not_written 1423 5590 (by decide))
      (l17_attn_pm_not_written 1423 5591 (by decide))
    intro s
    unfold l17PmAttn1
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb1Lit]
    rfl
  rw [hSMred, hP0red, hP1red, hkval, hvval, hcuQ, hcuKV]
  apply Zigzag2Rel.attn_zigzag
    (lDim := 2048) (qHeads := 16) (kvHeads := 4) (qDim := 64) (vDim := 64)
    (causal := true) (window := 0) (hrel := ⟨source0, source1, hs⟩)
  · exact h5541_5590.symm
  · simpa only [Nat.reduceMul] using hdecoded
  · decide
  · decide
  · decide
  · decide
  · decide

end
end TrainVerify.Denote.GeneratedPatterns
