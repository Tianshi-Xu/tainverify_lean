/- Layer-1 migration of the second MoE reconstruction boundary (tid 4768)
   to the canonical full-expert distributed denotation. -/
import denote.yoco_goals.Layer0DistributedMigration
import denote.yoco_goals.L2Reconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ## Semantics-generic non-MoE reduction gears

These are the distributed counterparts of the opaque ring gears.  The proof is
pure fold algebra; in particular it does not use graph well-formedness. -/

theorem distributed_node_core (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (outTid : Tid)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      applyNodeRingAttn g ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid := by
  have hstep := congrFun (foldl_take_succ (applyNodeDistributed g) g.nodes init k hk) outTid
  conv_lhs => rw [denoteGraphDistributed]
  rw [foldl_prefix_distributed g g.nodes init outTid (k + 1) hdrop_nil hdrop,
    hstep, hnode, applyNodeDistributed_eq_ring_of_not_moe g _ node hmoe]

theorem distributed_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributed g) init) tid =
      denoteGraphDistributed g init tid :=
  foldl_take_distributed_eq g init tid k hpre_nil hpre

theorem distributed_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeRingAttn g s node outTid = opfun (s inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraphDistributed g init outTid = opfun (denoteGraphDistributed g init inTid) := by
  rw [distributed_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, distributed_prefix_read g init k inTid hpre_nil hpre]

theorem distributed_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in1 in2 outTid : Tid) (opfun : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeRingAttn g s node outTid = opfun (s in1) (s in2))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      opfun (denoteGraphDistributed g init in1) (denoteGraphDistributed g init in2) := by
  rw [distributed_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, distributed_prefix_read g init k in1 hpre_nil hpre1,
    distributed_prefix_read g init k in2 hpre_nil hpre2]

def StoresAgreeOutside (bad : List Tid) (a b : Store) : Prop :=
  ∀ t, t ∉ bad → a t = b t

theorem applyNodeRingAttn_agreeOutside_of_safe (g : GraphDecl) (bad : List Tid)
    (a b : Store) (n : NodeDecl)
    (hab : StoresAgreeOutside bad a b)
    (hins : ∀ t ∈ n.ins, t ∉ bad)
    (houts : ∀ t ∈ bad, t ∉ n.outs)
    (hz : n.op ≠ "OpName.FW_attn_zigzag")
    (hs : n.op ≠ "OpName.FW_attn_sliding_window") :
    StoresAgreeOutside bad (applyNodeRingAttn g a n) (applyNodeRingAttn g b n) := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g a n hz hs,
    applyNodeRingAttn_eq_applyNode_of_not_ring g b n hz hs]
  intro t ht
  unfold applyNode
  have hm : n.ins.map a = n.ins.map b := by
    apply List.map_congr_left
    intro x hx
    exact hab x (hins x hx)
  rw [hm]
  unfold storeSet
  rw [hab t ht]

theorem foldl_distributed_agree_ring_outside (g : GraphDecl) (bad : List Tid)
    (pre : List NodeDecl) (a b : Store)
    (hab : StoresAgreeOutside bad a b)
    (hnil : ∀ n ∈ pre, n.outs ≠ [])
    (hstep : ∀ n ∈ pre,
      (∀ t ∈ n.outs, t ∈ bad) ∨
      (n.op ≠ "OpName.FW_all2all_moe_gmm" ∧
       n.op ≠ "OpName.FW_attn_zigzag" ∧
       n.op ≠ "OpName.FW_attn_sliding_window" ∧
       (∀ t ∈ n.ins, t ∉ bad) ∧ (∀ t ∈ bad, t ∉ n.outs))) :
    StoresAgreeOutside bad
      (pre.foldl (applyNodeDistributed g) a)
      (pre.foldl (applyNodeRingAttn g) b) := by
  induction pre generalizing a b with
  | nil => exact hab
  | cons n rest ih =>
    simp only [List.foldl]
    apply ih
    · intro t ht
      rcases hstep n List.mem_cons_self with hbad | hsafe
      · rw [applyNodeDistributed_skip g a n t (hnil n List.mem_cons_self)
            (fun hmem => ht (hbad t hmem)),
          applyNodeRingAttn_skip g b n t (hnil n List.mem_cons_self)
            (fun hmem => ht (hbad t hmem))]
        exact hab t ht
      · rw [applyNodeDistributed_eq_ring_of_not_moe g a n hsafe.1]
        exact applyNodeRingAttn_agreeOutside_of_safe g bad a b n hab
          hsafe.2.2.2.1 hsafe.2.2.2.2 hsafe.2.1 hsafe.2.2.1 t ht
    · intro m hm; exact hnil m (List.mem_cons_of_mem _ hm)
    · intro m hm; exact hstep m (List.mem_cons_of_mem _ hm)

set_option maxRecDepth 1000000 in
theorem layer1_sm_safe4733_cert : ∀ n ∈ (sm.nodes.drop 31).take 7,
    (∀ t ∈ n.outs, t ∈ [4714]) ∨
    (n.op ≠ "OpName.FW_all2all_moe_gmm" ∧
     n.op ≠ "OpName.FW_attn_zigzag" ∧
     n.op ≠ "OpName.FW_attn_sliding_window" ∧
     (∀ t ∈ n.ins, t ∉ [4714]) ∧ (∀ t ∈ [4714], t ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_safe4733_cert : ∀ n ∈ (pm.nodes.drop 104).take 14,
    (∀ t ∈ n.outs, t ∈ [7491, 7492, 4714]) ∨
    (n.op ≠ "OpName.FW_all2all_moe_gmm" ∧
     n.op ≠ "OpName.FW_attn_zigzag" ∧
     n.op ≠ "OpName.FW_attn_sliding_window" ∧
     (∀ t ∈ n.ins, t ∉ [7491, 7492, 4714]) ∧
     (∀ t ∈ [7491, 7492, 4714], t ∉ n.outs)) := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_sm_take38_nonempty : ∀ n ∈ (sm.nodes.drop 31).take 7, n.outs ≠ [] := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_take118_nonempty : ∀ n ∈ (pm.nodes.drop 104).take 14, n.outs ≠ [] := by native_decide

set_option maxRecDepth 10000000 in
theorem layer1_4733_distributed_bridge (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4733 = denoteGraphDistributed pm initPM 4733 := by
  have hspre : (sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM =
      (sm.nodes.take 31).foldl (applyNodeRingAttn sm) initSM :=
    foldl_distributed_eq_ring_of_no_moe sm (sm.nodes.take 31) initSM (by native_decide)
  have hppre : (pm.nodes.take 104).foldl (applyNodeDistributed pm) initPM =
      (pm.nodes.take 104).foldl (applyNodeRingAttn pm) initPM :=
    foldl_distributed_eq_ring_of_no_moe pm (pm.nodes.take 104) initPM (by native_decide)
  have hsagree := foldl_distributed_agree_ring_outside sm [4714]
    ((sm.nodes.drop 31).take 7)
    ((sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM)
    ((sm.nodes.take 31).foldl (applyNodeRingAttn sm) initSM)
    (fun t _ => congrFun hspre t)
    layer1_sm_take38_nonempty layer1_sm_safe4733_cert
  have hpagree := foldl_distributed_agree_ring_outside pm [7491, 7492, 4714]
    ((pm.nodes.drop 104).take 14)
    ((pm.nodes.take 104).foldl (applyNodeDistributed pm) initPM)
    ((pm.nodes.take 104).foldl (applyNodeRingAttn pm) initPM)
    (fun t _ => congrFun hppre t)
    layer1_pm_take118_nonempty layer1_pm_safe4733_cert
  have hs : denoteGraphDistributed sm initSM 4733 = denoteGraph_ringAttn sm initSM 4733 := by
    rw [denoteGraphDistributed, denoteGraph_ringAttn,
      foldl_prefix_distributed sm sm.nodes initSM 4733 38 (by native_decide) (by native_decide),
      foldl_prefix_ring_g12 sm sm.nodes initSM 4733 38 (by native_decide) (by native_decide)]
    rw [show sm.nodes.take 38 = sm.nodes.take 31 ++ (sm.nodes.drop 31).take 7 by native_decide,
      List.foldl_append]
    exact hsagree 4733 (by decide)
  have hp : denoteGraphDistributed pm initPM 4733 = denoteGraph_ringAttn pm initPM 4733 := by
    rw [denoteGraphDistributed, denoteGraph_ringAttn,
      foldl_prefix_distributed pm pm.nodes initPM 4733 118 (by native_decide) (by native_decide),
      foldl_prefix_ring_g12 pm pm.nodes initPM 4733 118 (by native_decide) (by native_decide)]
    rw [show pm.nodes.take 118 = pm.nodes.take 104 ++ (pm.nodes.drop 104).take 14 by native_decide,
      List.foldl_append]
    exact hpagree 4733 (by decide)
  have hr := recon_intermediateGoal_4733_ringAttn initSM initPM hSM hPM hInit
  have hrv : denoteGraph_ringAttn sm initSM 4733 = denoteGraph_ringAttn pm initPM 4733 :=
    oneTp_valeq intermediateGoal_4733 _ _ 4733 rfl rfl rfl rfl hr
  rw [hs, hp, hrv]

/-! ## 4734 — residual add after the first Layer-1 MoE branch -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4734_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4734
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4714 := recon_intermediateGoal_4714_distributed initSM initPM hSM hPM hInit
  have hv4714 : denoteGraphDistributed sm initSM 4714 =
      denoteGraphDistributed pm initPM 4714 :=
    oneTp_valeq intermediateGoal_4714 _ _ 4714 rfl rfl rfl rfl h4714
  have hs4714 : (denoteGraphDistributed sm initSM 4714).shape = [4096, 1024] := by
    have hs := h4714.1
    simpa [intermediateGoal_4714] using hs
  have hv4733 := layer1_4733_distributed_bridge initSM initPM hSM hPM hInit
  have h4733ring := recon_intermediateGoal_4733_ringAttn initSM initPM hSM hPM hInit
  have hs4733ring : (denoteGraph_ringAttn sm initSM 4733).shape = [4096, 1024] := by
    have hs := h4733ring.1
    simpa [intermediateGoal_4733] using hs
  have hspre : (sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM =
      (sm.nodes.take 31).foldl (applyNodeRingAttn sm) initSM :=
    foldl_distributed_eq_ring_of_no_moe sm (sm.nodes.take 31) initSM (by native_decide)
  have hsagree := foldl_distributed_agree_ring_outside sm [4714]
    ((sm.nodes.drop 31).take 7)
    ((sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM)
    ((sm.nodes.take 31).foldl (applyNodeRingAttn sm) initSM)
    (fun t _ => congrFun hspre t)
    layer1_sm_take38_nonempty layer1_sm_safe4733_cert
  have hd4733 : denoteGraphDistributed sm initSM 4733 =
      denoteGraph_ringAttn sm initSM 4733 := by
    rw [denoteGraphDistributed, denoteGraph_ringAttn,
      foldl_prefix_distributed sm sm.nodes initSM 4733 38 (by native_decide) (by native_decide),
      foldl_prefix_ring_g12 sm sm.nodes initSM 4733 38 (by native_decide) (by native_decide)]
    rw [show sm.nodes.take 38 = sm.nodes.take 31 ++ (sm.nodes.drop 31).take 7 by native_decide,
      List.foldl_append]
    exact hsagree 4733 (by decide)
  have hs4733 : (denoteGraphDistributed sm initSM 4733).shape = [4096, 1024] := by
    rw [hd4733]
    exact hs4733ring
  have rSM : denoteGraphDistributed sm initSM 4734 =
      elemwiseAdd (denoteGraphDistributed sm initSM 4714)
        (denoteGraphDistributed sm initSM 4733) :=
    distributed_reduce2 sm initSM 38
      { rank := 0, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] }
      4714 4733 4734 elemwiseAdd (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 4714 4733 4734)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4734 =
      elemwiseAdd (denoteGraphDistributed pm initPM 4714)
        (denoteGraphDistributed pm initPM 4733) :=
    distributed_reduce2 pm initPM 119
      { rank := 1, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] }
      4714 4733 4734 elemwiseAdd (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 4714 4733 4734)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4734 =
      denoteGraphDistributed pm initPM 4734 := by
    rw [rSM, rPM, hv4714, hv4733]
  have hshape : (denoteGraphDistributed sm initSM 4734).shape = [4096, 1024] := by
    rw [rSM]
    exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] hs4714 hs4733
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4734 4734 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

#print axioms recon_intermediateGoal_4734_distributed

/-! ## 4735–4738 — mechanical post-MoE chain

All nodes in this chain are reduced directly in the distributed denotation.  The
only ring bridge below is for 4703, whose defining prefix is strictly before the
first MoE node. -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4735_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4735
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4734 := recon_intermediateGoal_4734_distributed initSM initPM hSM hPM hInit
  have hv4734 : denoteGraphDistributed sm initSM 4734 =
      denoteGraphDistributed pm initPM 4734 :=
    oneTp_valeq intermediateGoal_4734 _ _ 4734 rfl rfl rfl rfl h4734
  have hs4734 : (denoteGraphDistributed sm initSM 4734).shape = [4096, 1024] := by
    have hs := h4734.1
    simpa [intermediateGoal_4734] using hs
  have rSM : denoteGraphDistributed sm initSM 4735 =
      id (denoteGraphDistributed sm initSM 4734) :=
    distributed_reduce1 sm initSM 39
      { rank := 0, op := "OpName.FW_float", ins := [4734], outs := [4735] }
      4734 4735 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4734 4735 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4735 =
      id (denoteGraphDistributed pm initPM 4734) :=
    distributed_reduce1 pm initPM 121
      { rank := 1, op := "OpName.FW_float", ins := [4734], outs := [4735] }
      4734 4735 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 4734 4735 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rPM
  have hval : denoteGraphDistributed sm initSM 4735 =
      denoteGraphDistributed pm initPM 4735 := by
    rw [rSM, rPM, hv4734]
  have hshape : (denoteGraphDistributed sm initSM 4735).shape = [4096, 1024] := by
    rw [rSM]
    exact hs4734
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4735 4735 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4736_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4736
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  -- 4703 is before the first MoE (SM node 31 / PM node 104), so this is the
  -- unique permitted distributed-to-ring transport in the post-MoE chain.
  have hs4703bridge : denoteGraphDistributed sm initSM 4703 =
      denoteGraph_ringAttn sm initSM 4703 :=
    denoteGraphDistributed_eq_ring_before_moe sm initSM 4703 31
      (by native_decide) (by native_decide) (by native_decide)
  have hp4703bridge : denoteGraphDistributed pm initPM 4703 =
      denoteGraph_ringAttn pm initPM 4703 :=
    denoteGraphDistributed_eq_ring_before_moe pm initPM 4703 104
      (by native_decide) (by native_decide) (by native_decide)
  have h4703ring := recon_intermediateGoal_4703_ringAttn initSM initPM hSM hPM hInit
  have hv4703ring : denoteGraph_ringAttn sm initSM 4703 =
      denoteGraph_ringAttn pm initPM 4703 :=
    oneTp_valeq intermediateGoal_4703 _ _ 4703 rfl rfl rfl rfl h4703ring
  have hs4703ring : (denoteGraph_ringAttn sm initSM 4703).shape = [4096, 1024] := by
    have hs := h4703ring.1
    simpa [intermediateGoal_4703] using hs
  have hv4703 : denoteGraphDistributed sm initSM 4703 =
      denoteGraphDistributed pm initPM 4703 := by
    rw [hs4703bridge, hp4703bridge, hv4703ring]
  have hs4703 : (denoteGraphDistributed sm initSM 4703).shape = [4096, 1024] := by
    rw [hs4703bridge]
    exact hs4703ring
  have s7408 : denoteGraphDistributed sm initSM 7408 =
      id (denoteGraphDistributed sm initSM 4703) :=
    distributed_reduce1 sm initSM 16
      { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }
      4703 7408 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4703 7404 7408 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14656 : denoteGraphDistributed pm initPM 14656 =
      id (denoteGraphDistributed pm initPM 4703) :=
    distributed_reduce1 pm initPM 65
      { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] }
      4703 14656 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 4703 14652 14656 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7408 p14656
  have hv7408 : denoteGraphDistributed sm initSM 7408 =
      denoteGraphDistributed pm initPM 14656 := by
    rw [s7408, p14656, hv4703]
  have hs7408 : (denoteGraphDistributed sm initSM 7408).shape = [4096, 1024] := by
    rw [s7408]
    exact hs4703
  have h4735 := recon_intermediateGoal_4735_distributed initSM initPM hSM hPM hInit
  have hv4735 : denoteGraphDistributed sm initSM 4735 =
      denoteGraphDistributed pm initPM 4735 :=
    oneTp_valeq intermediateGoal_4735 _ _ 4735 rfl rfl rfl rfl h4735
  have hs4735 : (denoteGraphDistributed sm initSM 4735).shape = [4096, 1024] := by
    have hs := h4735.1
    simpa [intermediateGoal_4735] using hs
  have rSM : denoteGraphDistributed sm initSM 4736 =
      elemwiseAdd (denoteGraphDistributed sm initSM 7408)
        (denoteGraphDistributed sm initSM 4735) :=
    distributed_reduce2 sm initSM 40
      { rank := 0, op := "OpName.FW_add", ins := [7408, 4735], outs := [4736] }
      7408 4735 4736 elemwiseAdd (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7408 4735 4736)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4736 =
      elemwiseAdd (denoteGraphDistributed pm initPM 14656)
        (denoteGraphDistributed pm initPM 4735) :=
    distributed_reduce2 pm initPM 123
      { rank := 1, op := "OpName.FW_add", ins := [14656, 4735], outs := [4736] }
      14656 4735 4736 elemwiseAdd (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14656 4735 4736)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4736 =
      denoteGraphDistributed pm initPM 4736 := by
    rw [rSM, rPM, hv7408, hv4735]
  have hshape : (denoteGraphDistributed sm initSM 4736).shape = [4096, 1024] := by
    rw [rSM]
    exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] hs7408 hs4735
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4736 4736 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4738_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4738
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4736 := recon_intermediateGoal_4736_distributed initSM initPM hSM hPM hInit
  have hv4736 : denoteGraphDistributed sm initSM 4736 =
      denoteGraphDistributed pm initPM 4736 :=
    oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl h4736
  have hs4736 : (denoteGraphDistributed sm initSM 4736).shape = [4096, 1024] := by
    have hs := h4736.1
    simpa [intermediateGoal_4736] using hs
  have s7435 : denoteGraphDistributed sm initSM 7435 =
      id (denoteGraphDistributed sm initSM 4736) :=
    distributed_reduce1 sm initSM 41
      { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439], params := [2] }
      4736 7435 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4736 7435 7439)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14668 : denoteGraphDistributed pm initPM 14668 =
      id (denoteGraphDistributed pm initPM 4736) :=
    distributed_reduce1 pm initPM 125
      { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672], params := [2] }
      4736 14668 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 4736 14668 14672)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7435 p14668
  have hweightInit : initSM 4737 = initPM 4737 := by
    have hg := hInit initGoal_4737 (by native_decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_4737, List.map, reconstructForGoal, List.headD] at hval
    exact hval
  have hsweight : denoteGraphDistributed sm initSM 4737 = initSM 4737 := by
    rw [denoteGraphDistributed]
    exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4737
      (by native_decide) (by native_decide)
  have hpweight : denoteGraphDistributed pm initPM 4737 = initPM 4737 := by
    rw [denoteGraphDistributed]
    exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 4737
      (by native_decide) (by native_decide)
  have hw4737 : denoteGraphDistributed sm initSM 4737 =
      denoteGraphDistributed pm initPM 4737 := by
    rw [hsweight, hpweight, hweightInit]
  have rSM : denoteGraphDistributed sm initSM 4738 =
      fw_rms_norm (denoteGraphDistributed sm initSM 7435)
        (denoteGraphDistributed sm initSM 4737) :=
    distributed_reduce2 sm initSM 42
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7435, 4737], outs := [4738] }
      7435 4737 4738 fw_rms_norm (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7435 4737 4738)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4738 =
      fw_rms_norm (denoteGraphDistributed pm initPM 14668)
        (denoteGraphDistributed pm initPM 4737) :=
    distributed_reduce2 pm initPM 127
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14668, 4737], outs := [4738] }
      14668 4737 4738 fw_rms_norm (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14668 4737 4738)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4738 =
      denoteGraphDistributed pm initPM 4738 := by
    rw [rSM, rPM, s7435, p14668, hv4736, hw4737]
  have hshape : (denoteGraphDistributed sm initSM 4738).shape = [4096, 1024] := by
    rw [rSM]
    exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s7435]; exact hs4736)
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4738 4738 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

#print axioms recon_intermediateGoal_4738_distributed

private def layer1SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7471, 4763, 4764, 4766, 4767], outs := [4768],
    params := [64, 0, 64, 8] }

private def layer1PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [11977, 7667, 7669, 7673, 7675], outs := [7677],
    params := [64, 0, 32, 8] }

private def layer1PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [11978, 7668, 7670, 7674, 7676], outs := [7678],
    params := [64, 32, 64, 8] }

/- Concrete graph certificates are deliberately split: asking the kernel to
   reduce the node, suffix, and buddy metadata in one term causes deep-recursion
   failures on the full generated graph. -/
set_option maxRecDepth 1000000 in
theorem layer1_sm_node70 : sm.nodes[70]'(by native_decide) = layer1SmMoe := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_sm_drop71_nonempty : ∀ n ∈ sm.nodes.drop 71, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_sm_drop71_no4768 : ∀ n ∈ sm.nodes.drop 71, 4768 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_node201 : pm.nodes[201]'(by native_decide) = layer1PmMoe0 := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_node202 : pm.nodes[202]'(by native_decide) = layer1PmMoe1 := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_drop202_nonempty : ∀ n ∈ pm.nodes.drop 202, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_drop202_no7677 : ∀ n ∈ pm.nodes.drop 202, 7677 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_drop203_nonempty : ∀ n ∈ pm.nodes.drop 203, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_drop203_no7678 : ∀ n ∈ pm.nodes.drop 203, 7678 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_sm_buddies : sm.replicaBuddies layer1SmMoe = [layer1SmMoe] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_buddies0 :
    pm.replicaBuddies layer1PmMoe0 = [layer1PmMoe0, layer1PmMoe1] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_buddies1 :
    pm.replicaBuddies layer1PmMoe1 = [layer1PmMoe0, layer1PmMoe1] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_sm_drop70_nonempty : ∀ n ∈ sm.nodes.drop 70, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_sm_drop70_no7471 : ∀ n ∈ sm.nodes.drop 70, 7471 ∉ n.outs := by
  native_decide
set_option maxRecDepth 1000000 in
theorem layer1_sm_drop70_no4763 : ∀ n ∈ sm.nodes.drop 70, 4763 ∉ n.outs := by
  native_decide
set_option maxRecDepth 1000000 in
theorem layer1_sm_drop70_no4764 : ∀ n ∈ sm.nodes.drop 70, 4764 ∉ n.outs := by
  native_decide
set_option maxRecDepth 1000000 in
theorem layer1_sm_drop70_no4766 : ∀ n ∈ sm.nodes.drop 70, 4766 ∉ n.outs := by
  native_decide
set_option maxRecDepth 1000000 in
theorem layer1_sm_drop70_no4767 : ∀ n ∈ sm.nodes.drop 70, 4767 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_nonempty : ∀ n ∈ pm.nodes.drop 201, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_no11977 : ∀ n ∈ pm.nodes.drop 201, 11977 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_no7667 : ∀ n ∈ pm.nodes.drop 201, 7667 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_no7669 : ∀ n ∈ pm.nodes.drop 201, 7669 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_no7673 : ∀ n ∈ pm.nodes.drop 201, 7673 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_no7674 : ∀ n ∈ pm.nodes.drop 201, 7674 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_no7675 : ∀ n ∈ pm.nodes.drop 201, 7675 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop201_no7676 : ∀ n ∈ pm.nodes.drop 201, 7676 ∉ n.outs := by native_decide

set_option maxRecDepth 1000000 in
theorem layer1_pm_drop202_no11978 : ∀ n ∈ pm.nodes.drop 202, 11978 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop202_no7668 : ∀ n ∈ pm.nodes.drop 202, 7668 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop202_no7670 : ∀ n ∈ pm.nodes.drop 202, 7670 ∉ n.outs := by native_decide

set_option maxRecDepth 10000000 in
theorem layer1_sm_moe_value (initSM : Store) :
    denoteGraphDistributed sm initSM 4768 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributed sm initSM 7471)
        (denoteGraphDistributed sm initSM 4763)
        (denoteGraphDistributed sm initSM 4764)
        [denoteGraphDistributed sm initSM 4766]
        [denoteGraphDistributed sm initSM 4767]
        64 8 (((10 : Nat) : Scalar)) := by
  have hk : 70 < sm.nodes.length := by native_decide
  rw [distributed_moe_reduce sm initSM 70 layer1SmMoe 4768 hk
    (show sm.nodes[70]'hk = layer1SmMoe from layer1_sm_node70)
    rfl rfl layer1_sm_drop71_nonempty layer1_sm_drop71_no4768]
  unfold applyNodeFullExpertMoE_value
  rw [layer1_sm_buddies]
  simp only [layer1SmMoe, List.map, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_some, Option.getD_none]
  rw [foldl_take_distributed_eq sm initSM 7471 70 layer1_sm_drop70_nonempty layer1_sm_drop70_no7471,
    foldl_take_distributed_eq sm initSM 4763 70 layer1_sm_drop70_nonempty layer1_sm_drop70_no4763,
    foldl_take_distributed_eq sm initSM 4764 70 layer1_sm_drop70_nonempty layer1_sm_drop70_no4764,
    foldl_take_distributed_eq sm initSM 4766 70 layer1_sm_drop70_nonempty layer1_sm_drop70_no4766,
    foldl_take_distributed_eq sm initSM 4767 70 layer1_sm_drop70_nonempty layer1_sm_drop70_no4767]

set_option maxRecDepth 10000000 in
theorem layer1_pm_moe0_value (initPM : Store) :
    denoteGraphDistributed pm initPM 7677 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributed pm initPM 11977)
        (denoteGraphDistributed pm initPM 7667)
        (denoteGraphDistributed pm initPM 7669)
        [denoteGraphDistributed pm initPM 7673, denoteGraphDistributed pm initPM 7674]
        [denoteGraphDistributed pm initPM 7675, denoteGraphDistributed pm initPM 7676]
        64 8 (((10 : Nat) : Scalar)) := by
  have hk : 201 < pm.nodes.length := by native_decide
  rw [distributed_moe_reduce pm initPM 201 layer1PmMoe0 7677 hk
    (show pm.nodes[201]'hk = layer1PmMoe0 from layer1_pm_node201)
    rfl rfl layer1_pm_drop202_nonempty layer1_pm_drop202_no7677]
  unfold applyNodeFullExpertMoE_value
  rw [layer1_pm_buddies0]
  simp only [layer1PmMoe0, layer1PmMoe1, List.map, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_some, Option.getD_none]
  rw [foldl_take_distributed_eq pm initPM 11977 201 layer1_pm_drop201_nonempty layer1_pm_drop201_no11977,
    foldl_take_distributed_eq pm initPM 7667 201 layer1_pm_drop201_nonempty layer1_pm_drop201_no7667,
    foldl_take_distributed_eq pm initPM 7669 201 layer1_pm_drop201_nonempty layer1_pm_drop201_no7669,
    foldl_take_distributed_eq pm initPM 7673 201 layer1_pm_drop201_nonempty layer1_pm_drop201_no7673,
    foldl_take_distributed_eq pm initPM 7674 201 layer1_pm_drop201_nonempty layer1_pm_drop201_no7674,
    foldl_take_distributed_eq pm initPM 7675 201 layer1_pm_drop201_nonempty layer1_pm_drop201_no7675,
    foldl_take_distributed_eq pm initPM 7676 201 layer1_pm_drop201_nonempty layer1_pm_drop201_no7676]

set_option maxRecDepth 10000000 in
theorem layer1_pm_moe1_value (initPM : Store) :
    denoteGraphDistributed pm initPM 7678 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributed pm initPM 11978)
        (denoteGraphDistributed pm initPM 7668)
        (denoteGraphDistributed pm initPM 7670)
        [denoteGraphDistributed pm initPM 7673, denoteGraphDistributed pm initPM 7674]
        [denoteGraphDistributed pm initPM 7675, denoteGraphDistributed pm initPM 7676]
        64 8 (((10 : Nat) : Scalar)) := by
  have hk : 202 < pm.nodes.length := by native_decide
  rw [distributed_moe_reduce pm initPM 202 layer1PmMoe1 7678 hk
    (show pm.nodes[202]'hk = layer1PmMoe1 from layer1_pm_node202)
    rfl rfl layer1_pm_drop203_nonempty layer1_pm_drop203_no7678]
  unfold applyNodeFullExpertMoE_value
  rw [layer1_pm_buddies1]
  simp only [layer1PmMoe0, layer1PmMoe1, List.map, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_some, Option.getD_none]
  rw [foldl_take_distributed_eq pm initPM 11978 202 layer1_pm_drop202_nonempty layer1_pm_drop202_no11978,
    foldl_take_distributed_eq pm initPM 7668 202 layer1_pm_drop202_nonempty layer1_pm_drop202_no7668,
    foldl_take_distributed_eq pm initPM 7670 202 layer1_pm_drop202_nonempty layer1_pm_drop202_no7670,
    foldl_take_distributed_eq pm initPM 7673 202 layer1_pm_drop202_nonempty (by native_decide),
    foldl_take_distributed_eq pm initPM 7674 202 layer1_pm_drop202_nonempty (by native_decide),
    foldl_take_distributed_eq pm initPM 7675 202 layer1_pm_drop202_nonempty (by native_decide),
    foldl_take_distributed_eq pm initPM 7676 202 layer1_pm_drop202_nonempty (by native_decide)]

end TrainVerify.Denote.GeneratedPatterns
