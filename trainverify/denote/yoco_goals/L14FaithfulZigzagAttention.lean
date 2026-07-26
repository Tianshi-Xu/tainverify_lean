import denote.yoco_goals.L13FaithfulBlockTail
import denote.yoco_goals.L13FaithfulZigzagAttention
import denote.yoco_goals.L2to11FaithfulKVBoundaryA
import denote.yoco_goals.L2to11FaithfulKVBoundaryB

/-!
# Block 2 faithful zigzag attention (goal 5445)

Structural clone of `L13FaithfulZigzagAttention` (block 1, goal 5396), shifted to
the third decoder block:

| | block 1 | block 2 |
|---|---|---|
| SM node | 540 | 575 |
| PM ranks | 1142 / 1143 → 9859 / 9860 | 1212 / 1213 → 10031 / 10032 |
| Q parent | `recon_zigzagGoal_5391_faithful` | `recon_zigzagGoal_5440_faithful` |
| K/V | 5392 / 5393 | 5441 / 5442 |
| cu | 5394 / 5395 | 5443 / 5444 |

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

private theorem l14_dgdf_reduce5
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

private theorem l14_dgdf_reduce6
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

private def l14SmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5440, 5441, 5442, 5443, 5444], outs := [5445],
    params := [16, 4, 64, 64, 1, 0] }
private def l14PmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10007, 5441, 5442, 5443, 5444], outs := [10031],
    params := [16, 4, 64, 64, 1, 0] }
private def l14PmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10008, 5441, 5442, 5443, 5444], outs := [10032],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
private theorem l14_attn_native_facts :
    sm.nodes[575]'(by native_decide) = l14SmAttn ∧
    pm.nodes[1212]'(by native_decide) = l14PmAttn0 ∧
    pm.nodes[1213]'(by native_decide) = l14PmAttn1 ∧
    sm.replicaBuddies l14SmAttn = [l14SmAttn] ∧
    pm.replicaBuddies l14PmAttn0 = [l14PmAttn0, l14PmAttn1] ∧
    pm.replicaBuddies l14PmAttn1 = [l14PmAttn0, l14PmAttn1] := by
  native_decide

private theorem l14_faithful_nonempty_sm_5445 (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l14_faithful_nonempty_pm_5445 (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l14_attn_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(576, 5445), (575, 5440), (575, 5441), (575, 5442),
      (575, 5443), (575, 5444)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l14_attn_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1213, 10031), (1214, 10032),
      (1212, 10007), (1212, 10008), (1212, 5441), (1212, 5442),
      (1212, 5443), (1212, 5444), (1213, 10007), (1213, 10008),
      (1213, 5441), (1213, 5442), (1213, 5443), (1213, 5444)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l14_attn_metadata_not_written :
    (∀ n ∈ sm.nodes, 5394 ∉ n.outs ∧ 5443 ∉ n.outs ∧ 5444 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5394 ∉ n.outs ∧ 5443 ∉ n.outs ∧ 5444 ∉ n.outs) := by
  native_decide

private theorem l14_init_singleton_eq (initSM initPM : Store)
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
-- Block-2 faithful generated cross-decoder attention goal 5445.
theorem recon_zigzagGoal_5445_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5445)
      (denoteGraphDistributedFaithful pm initPM 10031)
      (denoteGraphDistributedFaithful pm initPM 10032)
      (denoteGraphDistributedFaithful pm initPM 5443)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := recon_zigzagGoal_5440_faithful initSM initPM hSM hPM hInit hValues hCu
  have hK := recon_intermediateGoal_5441_faithful initSM initPM hSM hPM hInit hValues hCu
  have hV := recon_intermediateGoal_5442_faithful initSM initPM hSM hPM hInit hValues hCu
  have hkval := oneTp_valeq intermediateGoal_5441 _ _ 5441 rfl rfl rfl rfl hK
  have hvval := oneTp_valeq intermediateGoal_5442 _ _ 5442 rfl rfl rfl rfl hV
  rcases l14_attn_native_facts with ⟨sn, pn0, pn1, sb, pb0, pb1⟩
  have sbLit := sb
  have pb0Lit := pb0
  have pb1Lit := pb1
  unfold l14SmAttn at sbLit
  unfold l14PmAttn0 l14PmAttn1 at pb0Lit pb1Lit
  rcases l14_attn_metadata_not_written with ⟨smnw, pmnw⟩
  have hqInit := l14_init_singleton_eq initSM initPM hInit initGoal_4694
    (by native_decide) 4694 rfl rfl rfl rfl
  have hkInit := l14_init_singleton_eq initSM initPM hInit initGoal_4695
    (by native_decide) 4695 rfl rfl rfl rfl
  have sm4694_5443 : initSM 4694 = initSM 5443 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4694_5443 : initPM 4694 = initPM 5443 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have sm4695_5444 : initSM 4695 = initSM 5444 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4695_5444 : initPM 4695 = initPM 5444 :=
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
  have hcuQ : denoteGraphDistributedFaithful sm initSM 5443 =
      denoteGraphDistributedFaithful pm initPM 5443 := by
    rw [smFinal 5443 (fun n hn => (smnw n hn).2.1),
      pmFinal 5443 (fun n hn => (pmnw n hn).2.1), ← sm4694_5443,
      ← pm4694_5443, hqInit]
  have hcuKV : denoteGraphDistributedFaithful sm initSM 5444 =
      denoteGraphDistributedFaithful pm initPM 5444 := by
    rw [smFinal 5444 (fun n hn => (smnw n hn).2.2),
      pmFinal 5444 (fun n hn => (pmnw n hn).2.2), ← sm4695_5444,
      ← pm4695_5444, hkInit]
  have h5394_5443 : denoteGraphDistributedFaithful pm initPM 5394 =
      denoteGraphDistributedFaithful pm initPM 5443 := by
    rw [pmFinal 5394 (fun n hn => (pmnw n hn).1),
      pmFinal 5443 (fun n hn => (pmnw n hn).2.1)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5394).shape = [2] := by
    rw [pmFinal 5394 (fun n hn => (pmnw n hn).1)]
    exact hPM 5394 [2] (by native_decide)
  have hdecodedLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5394)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  rcases hQ with ⟨source0, source1, hs⟩
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5394) = [0, 4096] := by
    apply list_eq_pair_of_length_head_last _ 4096 hdecodedLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    exact ht.symm
  have hSMred : denoteGraphDistributedFaithful sm initSM 5445 =
      fw_attn_varlen (denoteGraphDistributedFaithful sm initSM 5440)
        (denoteGraphDistributedFaithful sm initSM 5441)
        (denoteGraphDistributedFaithful sm initSM 5442)
        (denoteGraphDistributedFaithful sm initSM 5443)
        (denoteGraphDistributedFaithful sm initSM 5444) 16 4 64 64 true 0 := by
    refine l14_dgdf_reduce5 sm initSM 575 l14SmAttn
      5440 5441 5442 5443 5444 5445
      (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
      (by native_decide) sn ?_ (l14_faithful_nonempty_sm_5445 576)
      (l14_attn_sm_not_written 576 5445 (by decide))
      (l14_faithful_nonempty_sm_5445 575)
      (l14_attn_sm_not_written 575 5440 (by decide))
      (l14_attn_sm_not_written 575 5441 (by decide))
      (l14_attn_sm_not_written 575 5442 (by decide))
      (l14_attn_sm_not_written 575 5443 (by decide))
      (l14_attn_sm_not_written 575 5444 (by decide))
    intro s
    unfold l14SmAttn
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [sbLit]
    rfl
  have hP0red : denoteGraphDistributedFaithful pm initPM 10031 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 10007,
         denoteGraphDistributedFaithful pm initPM 10008]
        (denoteGraphDistributedFaithful pm initPM 5441)
        (denoteGraphDistributedFaithful pm initPM 5442)
        (denoteGraphDistributedFaithful pm initPM 5443)
        (denoteGraphDistributedFaithful pm initPM 5444) 16 4 64 64 true 0 2 0 := by
    refine l14_dgdf_reduce6 pm initPM 1212 l14PmAttn0
      10007 10008 5441 5442 5443 5444 10031
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
      (by native_decide) pn0 ?_ (l14_faithful_nonempty_pm_5445 1213)
      (l14_attn_pm_not_written 1213 10031 (by decide))
      (l14_faithful_nonempty_pm_5445 1212)
      (l14_attn_pm_not_written 1212 10007 (by decide))
      (l14_attn_pm_not_written 1212 10008 (by decide))
      (l14_attn_pm_not_written 1212 5441 (by decide))
      (l14_attn_pm_not_written 1212 5442 (by decide))
      (l14_attn_pm_not_written 1212 5443 (by decide))
      (l14_attn_pm_not_written 1212 5444 (by decide))
    intro s
    unfold l14PmAttn0
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb0Lit]
    rfl
  have hP1red : denoteGraphDistributedFaithful pm initPM 10032 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 10007,
         denoteGraphDistributedFaithful pm initPM 10008]
        (denoteGraphDistributedFaithful pm initPM 5441)
        (denoteGraphDistributedFaithful pm initPM 5442)
        (denoteGraphDistributedFaithful pm initPM 5443)
        (denoteGraphDistributedFaithful pm initPM 5444) 16 4 64 64 true 0 2 1 := by
    refine l14_dgdf_reduce6 pm initPM 1213 l14PmAttn1
      10007 10008 5441 5442 5443 5444 10032
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
      (by native_decide) pn1 ?_ (l14_faithful_nonempty_pm_5445 1214)
      (l14_attn_pm_not_written 1214 10032 (by decide))
      (l14_faithful_nonempty_pm_5445 1213)
      (l14_attn_pm_not_written 1213 10007 (by decide))
      (l14_attn_pm_not_written 1213 10008 (by decide))
      (l14_attn_pm_not_written 1213 5441 (by decide))
      (l14_attn_pm_not_written 1213 5442 (by decide))
      (l14_attn_pm_not_written 1213 5443 (by decide))
      (l14_attn_pm_not_written 1213 5444 (by decide))
    intro s
    unfold l14PmAttn1
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb1Lit]
    rfl
  rw [hSMred, hP0red, hP1red, hkval, hvval, hcuQ, hcuKV]
  apply Zigzag2Rel.attn_zigzag
    (lDim := 2048) (qHeads := 16) (kvHeads := 4) (qDim := 64) (vDim := 64)
    (causal := true) (window := 0) (hrel := ⟨source0, source1, hs⟩)
  · exact h5394_5443.symm
  · simpa only [Nat.reduceMul] using hdecoded
  · decide
  · decide
  · decide
  · decide
  · decide

end
end TrainVerify.Denote.GeneratedPatterns
