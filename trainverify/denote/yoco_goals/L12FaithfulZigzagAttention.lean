import denote.yoco_goals.L12FaithfulReplicatedBoundary
import denote.yoco_goals.YOCInputValueClasses
import denote.yoco_goals.ZigzagAttentionRel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-- Local five-read reduction helper.  Keeping this at the new frontier avoids
invalidating every existing distributed proof module when only goal 5347 needs it. -/
private theorem denoteGraphDistributedFaithful_reduce5
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

/-- Reduce a faithful collective whose value reads one buddy input in addition
 to the node's five declared tensor inputs. -/
private theorem denoteGraphDistributedFaithful_reduce6
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

private def l12SmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5342, 5343, 5344, 5345, 5346], outs := [5347],
    params := [16, 4, 64, 64, 1, 0] }
private def l12PmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9659, 5343, 5344, 5345, 5346], outs := [9687],
    params := [16, 4, 64, 64, 1, 0] }
private def l12PmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9660, 5343, 5344, 5345, 5346], outs := [9688],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
private theorem l12_attn_native_facts :
    sm.nodes[505]'(by native_decide) = l12SmAttn ∧
    pm.nodes[1072]'(by native_decide) = l12PmAttn0 ∧
    pm.nodes[1073]'(by native_decide) = l12PmAttn1 ∧
    sm.replicaBuddies l12SmAttn = [l12SmAttn] ∧
    pm.replicaBuddies l12PmAttn0 = [l12PmAttn0, l12PmAttn1] ∧
    pm.replicaBuddies l12PmAttn1 = [l12PmAttn0, l12PmAttn1] := by
  native_decide

private theorem faithful_nonempty_sm_5347 (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem faithful_nonempty_pm_5347 (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12_attn_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(506, 5347), (505, 5342), (505, 5343), (505, 5344),
      (505, 5345), (505, 5346)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12_attn_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1073, 9687), (1074, 9688),
      (1072, 9659), (1072, 9660), (1072, 5343), (1072, 5344),
      (1072, 5345), (1072, 5346), (1073, 9659), (1073, 9660),
      (1073, 5343), (1073, 5344), (1073, 5345), (1073, 5346)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12_attn_metadata_not_written :
    (∀ n ∈ sm.nodes, 5337 ∉ n.outs ∧ 5345 ∉ n.outs ∧ 5346 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes, 5337 ∉ n.outs ∧ 5345 ∉ n.outs ∧ 5346 ∉ n.outs) := by
  native_decide

private theorem init_singleton_eq (initSM initPM : Store)
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
/-- First faithful generated cross-decoder attention goal.  The only extra contracts
are generated input-value aliases and the parent shuffle's cumulative-sequence WF. -/
theorem recon_zigzagGoal_5347_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5347)
      (denoteGraphDistributedFaithful pm initPM 9687)
      (denoteGraphDistributedFaithful pm initPM 9688)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 16, 64] [2048, 16, 64] := by
  have hQ := recon_zigzagGoal_5342_distributed initSM initPM hSM hPM hInit hCu
  have hK := recon_intermediateGoal_5343_faithful initSM initPM hSM hPM hInit
  have hV := recon_intermediateGoal_5344_faithful initSM initPM hSM hPM hInit
  have hkval := oneTp_valeq intermediateGoal_5343 _ _ 5343 rfl rfl rfl rfl hK
  have hvval := oneTp_valeq intermediateGoal_5344 _ _ 5344 rfl rfl rfl rfl hV
  rcases l12_attn_native_facts with ⟨sn, pn0, pn1, sb, pb0, pb1⟩
  have sbLit := sb
  have pb0Lit := pb0
  have pb1Lit := pb1
  unfold l12SmAttn at sbLit
  unfold l12PmAttn0 l12PmAttn1 at pb0Lit pb1Lit
  rcases l12_attn_metadata_not_written with ⟨smnw, pmnw⟩
  have hqInit := init_singleton_eq initSM initPM hInit initGoal_4694
    (by native_decide) 4694 rfl rfl rfl rfl
  have hkInit := init_singleton_eq initSM initPM hInit initGoal_4695
    (by native_decide) 4695 rfl rfl rfl rfl
  have sm4694_5345 : initSM 4694 = initSM 5345 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4694_5345 : initPM 4694 = initPM 5345 :=
    hValues.2.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqQClass_mem_pm
      (by native_decide) (by native_decide)
  have sm4695_5346 : initSM 4695 = initSM 5346 :=
    hValues.1.eq_of_mem TrainVerify.Denote.YOCInputValueClasses.cuseqKClass_mem_sm
      (by native_decide) (by native_decide)
  have pm4695_5346 : initPM 4695 = initPM 5346 :=
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
  have hcuQ : denoteGraphDistributedFaithful sm initSM 5345 =
      denoteGraphDistributedFaithful pm initPM 5345 := by
    rw [smFinal 5345 (fun n hn => (smnw n hn).2.1),
      pmFinal 5345 (fun n hn => (pmnw n hn).2.1), ← sm4694_5345,
      ← pm4694_5345, hqInit]
  have hcuKV : denoteGraphDistributedFaithful sm initSM 5346 =
      denoteGraphDistributedFaithful pm initPM 5346 := by
    rw [smFinal 5346 (fun n hn => (smnw n hn).2.2),
      pmFinal 5346 (fun n hn => (pmnw n hn).2.2), ← sm4695_5346,
      ← pm4695_5346, hkInit]
  have h5337_5345 : denoteGraphDistributedFaithful pm initPM 5337 =
      denoteGraphDistributedFaithful pm initPM 5345 := by
    rw [pmFinal 5337 (fun n hn => (pmnw n hn).1),
      pmFinal 5345 (fun n hn => (pmnw n hn).2.1)]
    exact TrainVerify.Denote.YOCInputValueClasses.pm_cuseq_q_5337_eq_5345 initPM hValues.2
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5337).shape = [2] := by
    rw [pmFinal 5337 (fun n hn => (pmnw n hn).1)]
    exact hPM 5337 [2] (by native_decide)
  have hdecodedLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5337)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  rcases hQ with ⟨source0, source1, hs⟩
  have hdecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5337) = [0, 4096] := by
    apply list_eq_pair_of_length_head_last _ 4096 hdecodedLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    exact ht.symm
  have hSMred : denoteGraphDistributedFaithful sm initSM 5347 =
      fw_attn_varlen (denoteGraphDistributedFaithful sm initSM 5342)
        (denoteGraphDistributedFaithful sm initSM 5343)
        (denoteGraphDistributedFaithful sm initSM 5344)
        (denoteGraphDistributedFaithful sm initSM 5345)
        (denoteGraphDistributedFaithful sm initSM 5346) 16 4 64 64 true 0 := by
    refine denoteGraphDistributedFaithful_reduce5 sm initSM 505 l12SmAttn
      5342 5343 5344 5345 5346 5347
      (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
      (by native_decide) sn ?_ (faithful_nonempty_sm_5347 506)
      (l12_attn_sm_not_written 506 5347 (by decide))
      (faithful_nonempty_sm_5347 505)
      (l12_attn_sm_not_written 505 5342 (by decide))
      (l12_attn_sm_not_written 505 5343 (by decide))
      (l12_attn_sm_not_written 505 5344 (by decide))
      (l12_attn_sm_not_written 505 5345 (by decide))
      (l12_attn_sm_not_written 505 5346 (by decide))
    intro s
    unfold l12SmAttn
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [sbLit]
    rfl
  have hP0red : denoteGraphDistributedFaithful pm initPM 9687 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 9659,
         denoteGraphDistributedFaithful pm initPM 9660]
        (denoteGraphDistributedFaithful pm initPM 5343)
        (denoteGraphDistributedFaithful pm initPM 5344)
        (denoteGraphDistributedFaithful pm initPM 5345)
        (denoteGraphDistributedFaithful pm initPM 5346) 16 4 64 64 true 0 2 0 := by
    refine denoteGraphDistributedFaithful_reduce6 pm initPM 1072 l12PmAttn0
      9659 9660 5343 5344 5345 5346 9687
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
      (by native_decide) pn0 ?_ (faithful_nonempty_pm_5347 1073)
      (l12_attn_pm_not_written 1073 9687 (by decide))
      (faithful_nonempty_pm_5347 1072)
      (l12_attn_pm_not_written 1072 9659 (by decide))
      (l12_attn_pm_not_written 1072 9660 (by decide))
      (l12_attn_pm_not_written 1072 5343 (by decide))
      (l12_attn_pm_not_written 1072 5344 (by decide))
      (l12_attn_pm_not_written 1072 5345 (by decide))
      (l12_attn_pm_not_written 1072 5346 (by decide))
    intro s
    unfold l12PmAttn0
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb0Lit]
    rfl
  have hP1red : denoteGraphDistributedFaithful pm initPM 9688 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm initPM 9659,
         denoteGraphDistributedFaithful pm initPM 9660]
        (denoteGraphDistributedFaithful pm initPM 5343)
        (denoteGraphDistributedFaithful pm initPM 5344)
        (denoteGraphDistributedFaithful pm initPM 5345)
        (denoteGraphDistributedFaithful pm initPM 5346) 16 4 64 64 true 0 2 1 := by
    refine denoteGraphDistributedFaithful_reduce6 pm initPM 1073 l12PmAttn1
      9659 9660 5343 5344 5345 5346 9688
      (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
        [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
      (by native_decide) pn1 ?_ (faithful_nonempty_pm_5347 1074)
      (l12_attn_pm_not_written 1074 9688 (by decide))
      (faithful_nonempty_pm_5347 1073)
      (l12_attn_pm_not_written 1073 9659 (by decide))
      (l12_attn_pm_not_written 1073 9660 (by decide))
      (l12_attn_pm_not_written 1073 5343 (by decide))
      (l12_attn_pm_not_written 1073 5344 (by decide))
      (l12_attn_pm_not_written 1073 5345 (by decide))
      (l12_attn_pm_not_written 1073 5346 (by decide))
    intro s
    unfold l12PmAttn1
    rw [applyNodeDistributedFaithful_zigzag_attn_out]
    unfold applyNodeFaithfulZigzagAttnValue
    rw [pb1Lit]
    rfl
  rw [hSMred, hP0red, hP1red, hkval, hvval, hcuQ, hcuKV]
  apply Zigzag2Rel.attn_zigzag
    (lDim := 2048) (qHeads := 16) (kvHeads := 4) (qDim := 64) (vDim := 64)
    (causal := true) (window := 0) (hrel := ⟨source0, source1, hs⟩)
  · exact h5337_5345.symm
  · simpa only [Nat.reduceMul] using hdecoded
  · decide
  · decide
  · decide
  · decide
  · decide

end
end TrainVerify.Denote.GeneratedPatterns
