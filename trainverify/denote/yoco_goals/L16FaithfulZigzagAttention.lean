import denote.yoco_goals.L15FaithfulBlockTail
import denote.yoco_goals.L15FaithfulZigzagAttention
import denote.yoco_goals.L2to11FaithfulKVBoundaryA
import denote.yoco_goals.L2to11FaithfulKVBoundaryB

/-!
# Block 4 faithful zigzag attention (goal 5543)

Structural clone of `L14FaithfulZigzagAttention` (block 3, goal 5494), shifted to
the fourth decoder block:

| | block 3 | block 4 |
|---|---|---|
| SM node | 610 | 645 |
| PM ranks | 1282 / 1283 → 10203 / 10204 | 1352 / 1353 → 10375 / 10376 |
| Q parent | `recon_zigzagGoal_5489_faithful` | `recon_zigzagGoal_5538_faithful` |
| K/V | 5490 / 5491 | 5539 / 5540 |
| cu | 5492 / 5493 | 5541 / 5542 |

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

private theorem l16_dgdf_reduce5
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

private theorem l16_dgdf_reduce6
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

private def l16SmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5538, 5539, 5540, 5541, 5542], outs := [5543],
    params := [16, 4, 64, 64, 1, 0] }
private def l16PmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10351, 5539, 5540, 5541, 5542], outs := [10375],
    params := [16, 4, 64, 64, 1, 0] }
private def l16PmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10352, 5539, 5540, 5541, 5542], outs := [10376],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
private theorem l16_attn_native_facts :
    sm.nodes[645]'(by native_decide) = l16SmAttn ∧
    pm.nodes[1352]'(by native_decide) = l16PmAttn0 ∧
    pm.nodes[1353]'(by native_decide) = l16PmAttn1 ∧
    sm.replicaBuddies l16SmAttn = [l16SmAttn] ∧
    pm.replicaBuddies l16PmAttn0 = [l16PmAttn0, l16PmAttn1] ∧
    pm.replicaBuddies l16PmAttn1 = [l16PmAttn0, l16PmAttn1] := by
  native_decide

private theorem l16_faithful_nonempty_sm_5543 (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l16_faithful_nonempty_pm_5543 (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l16_attn_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(646, 5543), (645, 5538), (645, 5539), (645, 5540),
      (645, 5541), (645, 5542)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16_attn_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1353, 10375), (1354, 10376),
      (1352, 10351), (1352, 10352), (1352, 5539), (1352, 5540),
      (1352, 5541), (1352, 5542), (1353, 10351), (1353, 10352),
      (1353, 5539), (1353, 5540), (1353, 5541), (1353, 5542)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l16_attn_metadata_not_written :
    (∀ n ∈ sm.nodes, 5492 ∉ n.outs ∧ 5541 ∉ n.outs ∧ 5542 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5492 ∉ n.outs ∧ 5541 ∉ n.outs ∧ 5542 ∉ n.outs) := by
  native_decide

private theorem l16_init_singleton_eq (initSM initPM : Store)
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
-- Block-4 faithful generated cross-decoder attention goal 5543.
theorem recon_zigzagGoal_5543_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5543)
      (denoteGraphDistributedFaithful pm initPM 10375)
      (denoteGraphDistributedFaithful pm initPM 10376)
      (denoteGraphDistributedFaithful pm initPM 5541)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := recon_zigzagGoal_5538_faithful initSM initPM hSM hPM hInit hValues hCu
  have hK := recon_intermediateGoal_5539_faithful initSM initPM hSM hPM hInit hValues hCu
  have hV := recon_intermediateGoal_5540_faithful initSM initPM hSM hPM hInit hValues hCu
  have hkval := oneTp_valeq intermediateGoal_5539 _ _ 5539 rfl rfl rfl rfl hK
  have hvval := oneTp_valeq intermediateGoal_5540 _ _ 5540 rfl rfl rfl rfl hV
  rcases l16_attn_native_facts with ⟨sn, pn0, pn1, sb, pb0, pb1⟩
  have sbLit := sb
  have pb0Lit := pb0
  have pb1Lit := pb1
  unfold l16SmAttn at sbLit
  unfold l16PmAttn0 l16PmAttn1 at pb0Lit pb1Lit
  rcases l16_attn_metadata_not_written with ⟨smnw, pmnw⟩
  have hqInit := l16_init_singleton_eq initSM initPM hInit initGoal_4694
    (by native_decide) 4694 rfl rfl rfl rfl
  have hkInit := l16_init_singleton_eq initSM initPM hInit initGoal_4695
    (by native_decide) 4695 rfl rfl rfl rfl
  have sm4694_5541 : initSM 4694 = initSM 5541 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4694_5541 : initPM 4694 = initPM 5541 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have sm4695_5542 : initSM 4695 = initSM 5542 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4695_5542 : initPM 4695 = initPM 5542 :=
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
  have hcuQ : denoteGraphDistributedFaithful sm initSM 5541 =
      denoteGraphDistributedFaithful pm initPM 5541 := by
    rw [smFinal 5541 (fun n hn => (smnw n hn).2.1),
      pmFinal 5541 (fun n hn => (pmnw n hn).2.1), ← sm4694_5541,
      ← pm4694_5541, hqInit]
  have hcuKV : denoteGraphDistributedFaithful sm initSM 5542 =
      denoteGraphDistributedFaithful pm initPM 5542 := by
    rw [smFinal 5542 (fun n hn => (smnw n hn).2.2),
      pmFinal 5542 (fun n hn => (pmnw n hn).2.2), ← sm4695_5542,
      ← pm4695_5542, hkInit]
  have h5492_5541 : denoteGraphDistributedFaithful pm initPM 5492 =
      denoteGraphDistributedFaithful pm initPM 5541 := by
    rw [pmFinal 5492 (fun n hn => (pmnw n hn).1),
      pmFinal 5541 (fun n hn => (pmnw n hn).2.1)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5492).shape = [2] := by
    rw [pmFinal 5492 (fun n hn => (pmnw n hn).1)]
    exact hPM 5492 [2] (by native_decide)
  have hdecodedLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5492)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  rcases hQ with ⟨source0, source1, hs⟩
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5492) = [0, 4096] := by
    apply list_eq_pair_of_length_head_last _ 4096 hdecodedLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    exact ht.symm
  have hSMred : denoteGraphDistributedFaithful sm initSM 5543 =
      fw_attn_varlen (denoteGraphDistributedFaithful sm initSM 5538)
        (denoteGraphDistributedFaithful sm initSM 5539)
        (denoteGraphDistributedFaithful sm initSM 5540)
        (denoteGraphDistributedFaithful sm initSM 5541)
        (denoteGraphDistributedFaithful sm initSM 5542) 16 4 64 64 true 0 := by
    refine l16_dgdf_reduce5 sm initSM 645 l16SmAttn
      5538 5539 5540 5541 5542 5543
      (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
      (by native_decide) sn ?_ (l16_faithful_nonempty_sm_5543 646)
      (l16_attn_sm_not_written 646 5543 (by decide))
      (l16_faithful_nonempty_sm_5543 645)
      (l16_attn_sm_not_written 645 5538 (by decide))
      (l16_attn_sm_not_written 645 5539 (by decide))
      (l16_attn_sm_not_written 645 5540 (by decide))
      (l16_attn_sm_not_written 645 5541 (by decide))
      (l16_attn_sm_not_written 645 5542 (by decide))
    intro s
    unfold l16SmAttn
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [sbLit]
    rfl
  have hP0red : denoteGraphDistributedFaithful pm initPM 10375 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 10351,
         denoteGraphDistributedFaithful pm initPM 10352]
        (denoteGraphDistributedFaithful pm initPM 5539)
        (denoteGraphDistributedFaithful pm initPM 5540)
        (denoteGraphDistributedFaithful pm initPM 5541)
        (denoteGraphDistributedFaithful pm initPM 5542) 16 4 64 64 true 0 2 0 := by
    refine l16_dgdf_reduce6 pm initPM 1352 l16PmAttn0
      10351 10352 5539 5540 5541 5542 10375
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
      (by native_decide) pn0 ?_ (l16_faithful_nonempty_pm_5543 1353)
      (l16_attn_pm_not_written 1353 10375 (by decide))
      (l16_faithful_nonempty_pm_5543 1352)
      (l16_attn_pm_not_written 1352 10351 (by decide))
      (l16_attn_pm_not_written 1352 10352 (by decide))
      (l16_attn_pm_not_written 1352 5539 (by decide))
      (l16_attn_pm_not_written 1352 5540 (by decide))
      (l16_attn_pm_not_written 1352 5541 (by decide))
      (l16_attn_pm_not_written 1352 5542 (by decide))
    intro s
    unfold l16PmAttn0
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb0Lit]
    rfl
  have hP1red : denoteGraphDistributedFaithful pm initPM 10376 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 10351,
         denoteGraphDistributedFaithful pm initPM 10352]
        (denoteGraphDistributedFaithful pm initPM 5539)
        (denoteGraphDistributedFaithful pm initPM 5540)
        (denoteGraphDistributedFaithful pm initPM 5541)
        (denoteGraphDistributedFaithful pm initPM 5542) 16 4 64 64 true 0 2 1 := by
    refine l16_dgdf_reduce6 pm initPM 1353 l16PmAttn1
      10351 10352 5539 5540 5541 5542 10376
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
      (by native_decide) pn1 ?_ (l16_faithful_nonempty_pm_5543 1354)
      (l16_attn_pm_not_written 1354 10376 (by decide))
      (l16_faithful_nonempty_pm_5543 1353)
      (l16_attn_pm_not_written 1353 10351 (by decide))
      (l16_attn_pm_not_written 1353 10352 (by decide))
      (l16_attn_pm_not_written 1353 5539 (by decide))
      (l16_attn_pm_not_written 1353 5540 (by decide))
      (l16_attn_pm_not_written 1353 5541 (by decide))
      (l16_attn_pm_not_written 1353 5542 (by decide))
    intro s
    unfold l16PmAttn1
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb1Lit]
    rfl
  rw [hSMred, hP0red, hP1red, hkval, hvval, hcuQ, hcuKV]
  apply Zigzag2Rel.attn_zigzag
    (lDim := 2048) (qHeads := 16) (kvHeads := 4) (qDim := 64) (vDim := 64)
    (causal := true) (window := 0) (hrel := ⟨source0, source1, hs⟩)
  · exact h5492_5541.symm
  · simpa only [Nat.reduceMul] using hdecoded
  · decide
  · decide
  · decide
  · decide
  · decide

end
end TrainVerify.Denote.GeneratedPatterns
