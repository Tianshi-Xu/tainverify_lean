import denote.yoco_goals.L22FaithfulBlockTail
import denote.yoco_goals.L22FaithfulZigzagAttention
import denote.yoco_goals.L2to11FaithfulKVBoundaryA
import denote.yoco_goals.L2to11FaithfulKVBoundaryB

/-!
# Block 11 faithful zigzag attention (goal 5886)

Structural clone of `L14FaithfulZigzagAttention` (block 10, goal 5837), shifted to
the fourth decoder block:

| | block 10 | block 11 |
|---|---|---|
| SM node | 855 | 890 |
| PM ranks | 1772 / 1773 → 11407 / 11408 | 1842 / 1843 → 11579 / 11580 |
| Q parent | `recon_zigzagGoal_5832_faithful` | `recon_zigzagGoal_5881_faithful` |
| K/V | 5833 / 5834 | 5882 / 5883 |
| cu | 5835 / 5836 | 5884 / 5885 |

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

private theorem l23_dgdf_reduce5
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

private theorem l23_dgdf_reduce6
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

private def l23SmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5881, 5882, 5883, 5884, 5885], outs := [5886],
    params := [16, 4, 64, 64, 1, 0] }
private def l23PmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11555, 5882, 5883, 5884, 5885], outs := [11579],
    params := [16, 4, 64, 64, 1, 0] }
private def l23PmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11556, 5882, 5883, 5884, 5885], outs := [11580],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
private theorem l23_attn_native_facts :
    sm.nodes[890]'(by native_decide) = l23SmAttn ∧
    pm.nodes[1842]'(by native_decide) = l23PmAttn0 ∧
    pm.nodes[1843]'(by native_decide) = l23PmAttn1 ∧
    sm.replicaBuddies l23SmAttn = [l23SmAttn] ∧
    pm.replicaBuddies l23PmAttn0 = [l23PmAttn0, l23PmAttn1] ∧
    pm.replicaBuddies l23PmAttn1 = [l23PmAttn0, l23PmAttn1] := by
  native_decide

private theorem l23_faithful_nonempty_sm_5886 (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l23_faithful_nonempty_pm_5886 (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23_attn_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(891, 5886), (890, 5881), (890, 5882), (890, 5883),
      (890, 5884), (890, 5885)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23_attn_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1843, 11579), (1844, 11580),
      (1842, 11555), (1842, 11556), (1842, 5882), (1842, 5883),
      (1842, 5884), (1842, 5885), (1843, 11555), (1843, 11556),
      (1843, 5882), (1843, 5883), (1843, 5884), (1843, 5885)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23_attn_metadata_not_written :
    (∀ n ∈ sm.nodes, 5835 ∉ n.outs ∧ 5884 ∉ n.outs ∧ 5885 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5835 ∉ n.outs ∧ 5884 ∉ n.outs ∧ 5885 ∉ n.outs) := by
  native_decide

private theorem l23_init_singleton_eq (initSM initPM : Store)
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
-- Block-11 faithful generated cross-decoder attention goal 5886.
theorem recon_zigzagGoal_5886_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5886)
      (denoteGraphDistributedFaithful pm initPM 11579)
      (denoteGraphDistributedFaithful pm initPM 11580)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := recon_zigzagGoal_5881_faithful initSM initPM hSM hPM hInit hValues hCu
  have hK := recon_intermediateGoal_5882_faithful initSM initPM hSM hPM hInit hValues hCu
  have hV := recon_intermediateGoal_5883_faithful initSM initPM hSM hPM hInit hValues hCu
  have hkval := oneTp_valeq intermediateGoal_5882 _ _ 5882 rfl rfl rfl rfl hK
  have hvval := oneTp_valeq intermediateGoal_5883 _ _ 5883 rfl rfl rfl rfl hV
  rcases l23_attn_native_facts with ⟨sn, pn0, pn1, sb, pb0, pb1⟩
  have sbLit := sb
  have pb0Lit := pb0
  have pb1Lit := pb1
  unfold l23SmAttn at sbLit
  unfold l23PmAttn0 l23PmAttn1 at pb0Lit pb1Lit
  rcases l23_attn_metadata_not_written with ⟨smnw, pmnw⟩
  have hqInit := l23_init_singleton_eq initSM initPM hInit initGoal_4694
    (by native_decide) 4694 rfl rfl rfl rfl
  have hkInit := l23_init_singleton_eq initSM initPM hInit initGoal_4695
    (by native_decide) 4695 rfl rfl rfl rfl
  have sm4694_5884 : initSM 4694 = initSM 5884 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4694_5884 : initPM 4694 = initPM 5884 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have sm4695_5885 : initSM 4695 = initSM 5885 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4695_5885 : initPM 4695 = initPM 5885 :=
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
  have hcuQ : denoteGraphDistributedFaithful sm initSM 5884 =
      denoteGraphDistributedFaithful pm initPM 5884 := by
    rw [smFinal 5884 (fun n hn => (smnw n hn).2.1),
      pmFinal 5884 (fun n hn => (pmnw n hn).2.1), ← sm4694_5884,
      ← pm4694_5884, hqInit]
  have hcuKV : denoteGraphDistributedFaithful sm initSM 5885 =
      denoteGraphDistributedFaithful pm initPM 5885 := by
    rw [smFinal 5885 (fun n hn => (smnw n hn).2.2),
      pmFinal 5885 (fun n hn => (pmnw n hn).2.2), ← sm4695_5885,
      ← pm4695_5885, hkInit]
  have h5835_5884 : denoteGraphDistributedFaithful pm initPM 5835 =
      denoteGraphDistributedFaithful pm initPM 5884 := by
    rw [pmFinal 5835 (fun n hn => (pmnw n hn).1),
      pmFinal 5884 (fun n hn => (pmnw n hn).2.1)]
    exact hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5835).shape = [2] := by
    rw [pmFinal 5835 (fun n hn => (pmnw n hn).1)]
    exact hPM 5835 [2] (by native_decide)
  have hdecodedLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5835)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  rcases hQ with ⟨source0, source1, hs⟩
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5835) = [0, 4096] := by
    apply list_eq_pair_of_length_head_last _ 4096 hdecodedLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    exact ht.symm
  have hSMred : denoteGraphDistributedFaithful sm initSM 5886 =
      fw_attn_varlen (denoteGraphDistributedFaithful sm initSM 5881)
        (denoteGraphDistributedFaithful sm initSM 5882)
        (denoteGraphDistributedFaithful sm initSM 5883)
        (denoteGraphDistributedFaithful sm initSM 5884)
        (denoteGraphDistributedFaithful sm initSM 5885) 16 4 64 64 true 0 := by
    refine l23_dgdf_reduce5 sm initSM 890 l23SmAttn
      5881 5882 5883 5884 5885 5886
      (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
      (by native_decide) sn ?_ (l23_faithful_nonempty_sm_5886 891)
      (l23_attn_sm_not_written 891 5886 (by decide))
      (l23_faithful_nonempty_sm_5886 890)
      (l23_attn_sm_not_written 890 5881 (by decide))
      (l23_attn_sm_not_written 890 5882 (by decide))
      (l23_attn_sm_not_written 890 5883 (by decide))
      (l23_attn_sm_not_written 890 5884 (by decide))
      (l23_attn_sm_not_written 890 5885 (by decide))
    intro s
    unfold l23SmAttn
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [sbLit]
    rfl
  have hP0red : denoteGraphDistributedFaithful pm initPM 11579 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 11555,
         denoteGraphDistributedFaithful pm initPM 11556]
        (denoteGraphDistributedFaithful pm initPM 5882)
        (denoteGraphDistributedFaithful pm initPM 5883)
        (denoteGraphDistributedFaithful pm initPM 5884)
        (denoteGraphDistributedFaithful pm initPM 5885) 16 4 64 64 true 0 2 0 := by
    refine l23_dgdf_reduce6 pm initPM 1842 l23PmAttn0
      11555 11556 5882 5883 5884 5885 11579
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
      (by native_decide) pn0 ?_ (l23_faithful_nonempty_pm_5886 1843)
      (l23_attn_pm_not_written 1843 11579 (by decide))
      (l23_faithful_nonempty_pm_5886 1842)
      (l23_attn_pm_not_written 1842 11555 (by decide))
      (l23_attn_pm_not_written 1842 11556 (by decide))
      (l23_attn_pm_not_written 1842 5882 (by decide))
      (l23_attn_pm_not_written 1842 5883 (by decide))
      (l23_attn_pm_not_written 1842 5884 (by decide))
      (l23_attn_pm_not_written 1842 5885 (by decide))
    intro s
    unfold l23PmAttn0
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb0Lit]
    rfl
  have hP1red : denoteGraphDistributedFaithful pm initPM 11580 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 11555,
         denoteGraphDistributedFaithful pm initPM 11556]
        (denoteGraphDistributedFaithful pm initPM 5882)
        (denoteGraphDistributedFaithful pm initPM 5883)
        (denoteGraphDistributedFaithful pm initPM 5884)
        (denoteGraphDistributedFaithful pm initPM 5885) 16 4 64 64 true 0 2 1 := by
    refine l23_dgdf_reduce6 pm initPM 1843 l23PmAttn1
      11555 11556 5882 5883 5884 5885 11580
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
      (by native_decide) pn1 ?_ (l23_faithful_nonempty_pm_5886 1844)
      (l23_attn_pm_not_written 1844 11580 (by decide))
      (l23_faithful_nonempty_pm_5886 1843)
      (l23_attn_pm_not_written 1843 11555 (by decide))
      (l23_attn_pm_not_written 1843 11556 (by decide))
      (l23_attn_pm_not_written 1843 5882 (by decide))
      (l23_attn_pm_not_written 1843 5883 (by decide))
      (l23_attn_pm_not_written 1843 5884 (by decide))
      (l23_attn_pm_not_written 1843 5885 (by decide))
    intro s
    unfold l23PmAttn1
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb1Lit]
    rfl
  rw [hSMred, hP0red, hP1red, hkval, hvval, hcuQ, hcuKV]
  apply Zigzag2Rel.attn_zigzag
    (lDim := 2048) (qHeads := 16) (kvHeads := 4) (qDim := 64) (vDim := 64)
    (causal := true) (window := 0) (hrel := ⟨source0, source1, hs⟩)
  · exact h5835_5884.symm
  · simpa only [Nat.reduceMul] using hdecoded
  · decide
  · decide
  · decide
  · decide
  · decide

end
end TrainVerify.Denote.GeneratedPatterns
