import denote.yoco_goals.L13FaithfulReplicatedBoundary
import denote.yoco_goals.L12FaithfulBlockTail
import denote.yoco_goals.L12FaithfulZigzagAttention

/-!
# Block 1 faithful zigzag attention (goal 5396)

Structural clone of `L12FaithfulZigzagAttention` (block 0, goal 5347), shifted to
the second decoder block:

| | block 0 | block 1 |
|---|---|---|
| SM node | 505 | 540 |
| PM ranks | 1072 / 1073 → 9687 / 9688 | 1142 / 1143 → 9859 / 9860 |
| Q parent | `recon_zigzagGoal_5342_distributed` | `recon_zigzagGoal_5391_faithful` |
| K/V | 5343 / 5344 | 5392 / 5393 |
| cu | 5345 / 5346 | 5394 / 5395 |

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

private theorem l13_dgdf_reduce5
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

private theorem l13_dgdf_reduce6
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

private def l13SmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5391, 5392, 5393, 5394, 5395], outs := [5396],
    params := [16, 4, 64, 64, 1, 0] }
private def l13PmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9835, 5392, 5393, 5394, 5395], outs := [9859],
    params := [16, 4, 64, 64, 1, 0] }
private def l13PmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9836, 5392, 5393, 5394, 5395], outs := [9860],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
private theorem l13_attn_native_facts :
    sm.nodes[540]'(by native_decide) = l13SmAttn ∧
    pm.nodes[1142]'(by native_decide) = l13PmAttn0 ∧
    pm.nodes[1143]'(by native_decide) = l13PmAttn1 ∧
    sm.replicaBuddies l13SmAttn = [l13SmAttn] ∧
    pm.replicaBuddies l13PmAttn0 = [l13PmAttn0, l13PmAttn1] ∧
    pm.replicaBuddies l13PmAttn1 = [l13PmAttn0, l13PmAttn1] := by
  native_decide

private theorem l13_faithful_nonempty_sm_5396 (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l13_faithful_nonempty_pm_5396 (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l13_attn_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(541, 5396), (540, 5391), (540, 5392), (540, 5393),
      (540, 5394), (540, 5395)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l13_attn_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1143, 9859), (1144, 9860),
      (1142, 9835), (1142, 9836), (1142, 5392), (1142, 5393),
      (1142, 5394), (1142, 5395), (1143, 9835), (1143, 9836),
      (1143, 5392), (1143, 5393), (1143, 5394), (1143, 5395)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l13_attn_metadata_not_written :
    (∀ n ∈ sm.nodes, 5345 ∉ n.outs ∧ 5394 ∉ n.outs ∧ 5395 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5345 ∉ n.outs ∧ 5394 ∉ n.outs ∧ 5395 ∉ n.outs) := by
  native_decide

private theorem l13_init_singleton_eq (initSM initPM : Store)
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
-- Block-1 faithful generated cross-decoder attention goal 5396.
theorem recon_zigzagGoal_5396_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5396)
      (denoteGraphDistributedFaithful pm initPM 9859)
      (denoteGraphDistributedFaithful pm initPM 9860)
      (denoteGraphDistributedFaithful pm initPM 5394)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := recon_zigzagGoal_5391_faithful initSM initPM hSM hPM hInit hValues hCu
  have hK := recon_intermediateGoal_5392_faithful initSM initPM hSM hPM hInit hValues hCu
  have hV := recon_intermediateGoal_5393_faithful initSM initPM hSM hPM hInit hValues hCu
  have hkval := oneTp_valeq intermediateGoal_5392 _ _ 5392 rfl rfl rfl rfl hK
  have hvval := oneTp_valeq intermediateGoal_5393 _ _ 5393 rfl rfl rfl rfl hV
  rcases l13_attn_native_facts with ⟨sn, pn0, pn1, sb, pb0, pb1⟩
  have sbLit := sb
  have pb0Lit := pb0
  have pb1Lit := pb1
  unfold l13SmAttn at sbLit
  unfold l13PmAttn0 l13PmAttn1 at pb0Lit pb1Lit
  rcases l13_attn_metadata_not_written with ⟨smnw, pmnw⟩
  have hqInit := l13_init_singleton_eq initSM initPM hInit initGoal_4694
    (by native_decide) 4694 rfl rfl rfl rfl
  have hkInit := l13_init_singleton_eq initSM initPM hInit initGoal_4695
    (by native_decide) 4695 rfl rfl rfl rfl
  have sm4694_5394 : initSM 4694 = initSM 5394 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4694_5394 : initPM 4694 = initPM 5394 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have sm4695_5395 : initSM 4695 = initSM 5395 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4695_5395 : initPM 4695 = initPM 5395 :=
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
  have hcuQ : denoteGraphDistributedFaithful sm initSM 5394 =
      denoteGraphDistributedFaithful pm initPM 5394 := by
    rw [smFinal 5394 (fun n hn => (smnw n hn).2.1),
      pmFinal 5394 (fun n hn => (pmnw n hn).2.1), ← sm4694_5394,
      ← pm4694_5394, hqInit]
  have hcuKV : denoteGraphDistributedFaithful sm initSM 5395 =
      denoteGraphDistributedFaithful pm initPM 5395 := by
    rw [smFinal 5395 (fun n hn => (smnw n hn).2.2),
      pmFinal 5395 (fun n hn => (pmnw n hn).2.2), ← sm4695_5395,
      ← pm4695_5395, hkInit]
  have h5345_5394 : denoteGraphDistributedFaithful pm initPM 5345 =
      denoteGraphDistributedFaithful pm initPM 5394 := by
    rw [pmFinal 5345 (fun n hn => (pmnw n hn).1),
      pmFinal 5394 (fun n hn => (pmnw n hn).2.1)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5345).shape = [2] := by
    rw [pmFinal 5345 (fun n hn => (pmnw n hn).1)]
    exact hPM 5345 [2] (by native_decide)
  have hdecodedLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5345)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  rcases hQ with ⟨source0, source1, hs⟩
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5345) = [0, 4096] := by
    apply list_eq_pair_of_length_head_last _ 4096 hdecodedLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    exact ht.symm
  have hSMred : denoteGraphDistributedFaithful sm initSM 5396 =
      fw_attn_varlen (denoteGraphDistributedFaithful sm initSM 5391)
        (denoteGraphDistributedFaithful sm initSM 5392)
        (denoteGraphDistributedFaithful sm initSM 5393)
        (denoteGraphDistributedFaithful sm initSM 5394)
        (denoteGraphDistributedFaithful sm initSM 5395) 16 4 64 64 true 0 := by
    refine l13_dgdf_reduce5 sm initSM 540 l13SmAttn
      5391 5392 5393 5394 5395 5396
      (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
      (by native_decide) sn ?_ (l13_faithful_nonempty_sm_5396 541)
      (l13_attn_sm_not_written 541 5396 (by decide))
      (l13_faithful_nonempty_sm_5396 540)
      (l13_attn_sm_not_written 540 5391 (by decide))
      (l13_attn_sm_not_written 540 5392 (by decide))
      (l13_attn_sm_not_written 540 5393 (by decide))
      (l13_attn_sm_not_written 540 5394 (by decide))
      (l13_attn_sm_not_written 540 5395 (by decide))
    intro s
    unfold l13SmAttn
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [sbLit]
    rfl
  have hP0red : denoteGraphDistributedFaithful pm initPM 9859 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 9835,
         denoteGraphDistributedFaithful pm initPM 9836]
        (denoteGraphDistributedFaithful pm initPM 5392)
        (denoteGraphDistributedFaithful pm initPM 5393)
        (denoteGraphDistributedFaithful pm initPM 5394)
        (denoteGraphDistributedFaithful pm initPM 5395) 16 4 64 64 true 0 2 0 := by
    refine l13_dgdf_reduce6 pm initPM 1142 l13PmAttn0
      9835 9836 5392 5393 5394 5395 9859
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
      (by native_decide) pn0 ?_ (l13_faithful_nonempty_pm_5396 1143)
      (l13_attn_pm_not_written 1143 9859 (by decide))
      (l13_faithful_nonempty_pm_5396 1142)
      (l13_attn_pm_not_written 1142 9835 (by decide))
      (l13_attn_pm_not_written 1142 9836 (by decide))
      (l13_attn_pm_not_written 1142 5392 (by decide))
      (l13_attn_pm_not_written 1142 5393 (by decide))
      (l13_attn_pm_not_written 1142 5394 (by decide))
      (l13_attn_pm_not_written 1142 5395 (by decide))
    intro s
    unfold l13PmAttn0
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb0Lit]
    rfl
  have hP1red : denoteGraphDistributedFaithful pm initPM 9860 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 9835,
         denoteGraphDistributedFaithful pm initPM 9836]
        (denoteGraphDistributedFaithful pm initPM 5392)
        (denoteGraphDistributedFaithful pm initPM 5393)
        (denoteGraphDistributedFaithful pm initPM 5394)
        (denoteGraphDistributedFaithful pm initPM 5395) 16 4 64 64 true 0 2 1 := by
    refine l13_dgdf_reduce6 pm initPM 1143 l13PmAttn1
      9835 9836 5392 5393 5394 5395 9860
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
      (by native_decide) pn1 ?_ (l13_faithful_nonempty_pm_5396 1144)
      (l13_attn_pm_not_written 1144 9860 (by decide))
      (l13_faithful_nonempty_pm_5396 1143)
      (l13_attn_pm_not_written 1143 9835 (by decide))
      (l13_attn_pm_not_written 1143 9836 (by decide))
      (l13_attn_pm_not_written 1143 5392 (by decide))
      (l13_attn_pm_not_written 1143 5393 (by decide))
      (l13_attn_pm_not_written 1143 5394 (by decide))
      (l13_attn_pm_not_written 1143 5395 (by decide))
    intro s
    unfold l13PmAttn1
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb1Lit]
    rfl
  rw [hSMred, hP0red, hP1red, hkval, hvval, hcuQ, hcuKV]
  apply Zigzag2Rel.attn_zigzag
    (lDim := 2048) (qHeads := 16) (kvHeads := 4) (qDim := 64) (vDim := 64)
    (causal := true) (window := 0) (hrel := ⟨source0, source1, hs⟩)
  · exact h5345_5394.symm
  · simpa only [Nat.reduceMul] using hdecoded
  · decide
  · decide
  · decide
  · decide
  · decide

end
end TrainVerify.Denote.GeneratedPatterns
