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

/-! ## Layer-1 Q/K/V and rotary fan-out

All leaves below are recovered directly from `hInit`; distributed never-written
facts lift them to the final stores.  Thus this post-MoE chain does not pass
through any ring reconstruction theorem. -/

theorem distributed_init_singleton_value (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid)
    (htp : gW.tps = [{ rank := 0, tid := W }]) (hgd : gW.gatherDim = 0)
    (hrep : gW.replicated = false) (hts : gW.ts = W)
    (hsmNil : ∀ n ∈ sm.nodes, n.outs ≠ []) (hsm : ∀ n ∈ sm.nodes, W ∉ n.outs)
    (hpmNil : ∀ n ∈ pm.nodes, n.outs ≠ []) (hpm : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    denoteGraphDistributed sm initSM W = denoteGraphDistributed pm initPM W := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  have hv := hg.2.2
  rw [reconstructForGoal_of_not_replicated gW pm.numRanks _ hrep, htp, hts, hgd] at hv
  simp only [List.map, reconstructWithDim] at hv
  rw [denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM W hsmNil hsm,
    denoteGraphDistributed, foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM W hpmNil hpm]
  exact hv

theorem distributed_init_singleton_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid) (sh : Shape)
    (htsShape : gW.tsShape = sh) (hts : gW.ts = W)
    (hsmNil : ∀ n ∈ sm.nodes, n.outs ≠ []) (hsm : ∀ n ∈ sm.nodes, W ∉ n.outs) :
    (denoteGraphDistributed sm initSM W).shape = sh := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  rw [denoteGraphDistributed,
    foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM W hsmNil hsm]
  rw [← hts, ← htsShape]
  exact hg.1

private def layer1SmFanout : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [4738],
    outs := [7444, 7448, 7452], params := [3] }
private def layer1PmFanout : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4738],
    outs := [14689, 14693, 14697], params := [3] }
private def layer1SmRotary : NodeDecl :=
  { rank := 0, op := "OpName.FW_rotary_embedding",
    ins := [4691, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }
private def layer1PmRotary : NodeDecl :=
  { rank := 1, op := "OpName.FW_rotary_embedding",
    ins := [11854, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }

-- Keep node and suffix reductions in separate kernel certificates.
set_option maxRecDepth 1000000 in
theorem layer1_sm_node43 : sm.nodes[43]'(by native_decide) = layer1SmFanout := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_node129 : pm.nodes[129]'(by native_decide) = layer1PmFanout := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_sm_node47 : sm.nodes[47]'(by native_decide) = layer1SmRotary := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_node137 : pm.nodes[137]'(by native_decide) = layer1PmRotary := by native_decide
private def layer1PmCache : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4691],
    outs := (List.range 12).map (fun r => 11853 + r),
    params := [((List.range 12).map (fun r => 11853 + r)).length] }
set_option maxRecDepth 1000000 in
theorem layer1_pm_node14 : pm.nodes[14]'(by native_decide) = layer1PmCache := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop15_nonempty : ∀ n ∈ pm.nodes.drop 15, n.outs ≠ [] := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop15_no11854 : ∀ n ∈ pm.nodes.drop 15, 11854 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop14_nonempty : ∀ n ∈ pm.nodes.drop 14, n.outs ≠ [] := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_drop14_no4691 : ∀ n ∈ pm.nodes.drop 14, 4691 ∉ n.outs := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_sm_nodes_nonempty : ∀ n ∈ sm.nodes, n.outs ≠ [] := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_nodes_nonempty : ∀ n ∈ pm.nodes, n.outs ≠ [] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4740_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4740
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4738 := recon_intermediateGoal_4738_distributed initSM initPM hSM hPM hInit
  have hv4738 := oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl h4738
  have hs4738 : (denoteGraphDistributed sm initSM 4738).shape = [4096, 1024] := by
    have hs := h4738.1; simpa [intermediateGoal_4738] using hs
  have s7444 : denoteGraphDistributed sm initSM 7444 = id (denoteGraphDistributed sm initSM 4738) :=
    distributed_reduce1 sm initSM 43 layer1SmFanout 4738 7444 id (by native_decide)
      layer1_sm_node43 (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4738 7444 7448 7452)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14689 : denoteGraphDistributed pm initPM 14689 = id (denoteGraphDistributed pm initPM 4738) :=
    distributed_reduce1 pm initPM 129 layer1PmFanout 4738 14689 id (by native_decide)
      layer1_pm_node129 (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 4738 14689 14693 14697)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7444 p14689
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4739
    (by native_decide) 4739 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hsw := distributed_init_singleton_shape initSM initPM hInit initGoal_4739
    (by native_decide) 4739 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have rSM : denoteGraphDistributed sm initSM 4740 =
      fw_per_head_linear (denoteGraphDistributed sm initSM 7444) (denoteGraphDistributed sm initSM 4739) :=
    distributed_reduce2 sm initSM 44
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7444, 4739], outs := [4740] }
      7444 4739 4740 fw_per_head_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7444 4739 4740 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4740 =
      fw_per_head_linear (denoteGraphDistributed pm initPM 14689) (denoteGraphDistributed pm initPM 4739) :=
    distributed_reduce2 pm initPM 133
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14689, 4739], outs := [4740] }
      14689 4739 4740 fw_per_head_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14689 4739 4740 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4740 = denoteGraphDistributed pm initPM 4740 := by
    rw [rSM, rPM, s7444, p14689, hv4738, hw]
  have hshape : (denoteGraphDistributed sm initSM 4740).shape = [4096, 16, 64] := by
    rw [rSM]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s7444]; exact hs4738) hsw
  exact wrap_1tp_gen _ _ intermediateGoal_4740 4740 [4096, 16, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4742_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4742
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4738 := recon_intermediateGoal_4738_distributed initSM initPM hSM hPM hInit
  have hv4738 := oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl h4738
  have hs4738 : (denoteGraphDistributed sm initSM 4738).shape = [4096, 1024] := by
    have hs := h4738.1; simpa [intermediateGoal_4738] using hs
  have s7448 : denoteGraphDistributed sm initSM 7448 = id (denoteGraphDistributed sm initSM 4738) :=
    distributed_reduce1 sm initSM 43 layer1SmFanout 4738 7448 id (by native_decide)
      layer1_sm_node43 (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4738 7444 7448 7452 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14693 : denoteGraphDistributed pm initPM 14693 = id (denoteGraphDistributed pm initPM 4738) :=
    distributed_reduce1 pm initPM 129 layer1PmFanout 4738 14693 id (by native_decide)
      layer1_pm_node129 (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 4738 14689 14693 14697 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7448 p14693
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4741
    (by native_decide) 4741 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hsw := distributed_init_singleton_shape initSM initPM hInit initGoal_4741
    (by native_decide) 4741 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have rSM : denoteGraphDistributed sm initSM 4742 =
      fw_per_head_linear (denoteGraphDistributed sm initSM 7448) (denoteGraphDistributed sm initSM 4741) :=
    distributed_reduce2 sm initSM 45
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7448, 4741], outs := [4742] }
      7448 4741 4742 fw_per_head_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7448 4741 4742 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4742 =
      fw_per_head_linear (denoteGraphDistributed pm initPM 14693) (denoteGraphDistributed pm initPM 4741) :=
    distributed_reduce2 pm initPM 134
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14693, 4741], outs := [4742] }
      14693 4741 4742 fw_per_head_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14693 4741 4742 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4742 = denoteGraphDistributed pm initPM 4742 := by
    rw [rSM, rPM, s7448, p14693, hv4738, hw]
  have hshape : (denoteGraphDistributed sm initSM 4742).shape = [4096, 4, 64] := by
    rw [rSM]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s7448]; exact hs4738) hsw
  exact wrap_1tp_gen _ _ intermediateGoal_4742 4742 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4744_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4744
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4738 := recon_intermediateGoal_4738_distributed initSM initPM hSM hPM hInit
  have hv4738 := oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl h4738
  have hs4738 : (denoteGraphDistributed sm initSM 4738).shape = [4096, 1024] := by
    have hs := h4738.1; simpa [intermediateGoal_4738] using hs
  have s7452 : denoteGraphDistributed sm initSM 7452 = id (denoteGraphDistributed sm initSM 4738) :=
    distributed_reduce1 sm initSM 43 layer1SmFanout 4738 7452 id (by native_decide)
      layer1_sm_node43 (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4738 7444 7448 7452 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14697 : denoteGraphDistributed pm initPM 14697 = id (denoteGraphDistributed pm initPM 4738) :=
    distributed_reduce1 pm initPM 129 layer1PmFanout 4738 14697 id (by native_decide)
      layer1_pm_node129 (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 4738 14689 14693 14697 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7452 p14697
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4743
    (by native_decide) 4743 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hsw := distributed_init_singleton_shape initSM initPM hInit initGoal_4743
    (by native_decide) 4743 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have rSM : denoteGraphDistributed sm initSM 4744 =
      fw_per_head_linear (denoteGraphDistributed sm initSM 7452) (denoteGraphDistributed sm initSM 4743) :=
    distributed_reduce2 sm initSM 46
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7452, 4743], outs := [4744] }
      7452 4743 4744 fw_per_head_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7452 4743 4744 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4744 =
      fw_per_head_linear (denoteGraphDistributed pm initPM 14697) (denoteGraphDistributed pm initPM 4743) :=
    distributed_reduce2 pm initPM 135
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14697, 4743], outs := [4744] }
      14697 4743 4744 fw_per_head_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14697 4743 4744 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4744 = denoteGraphDistributed pm initPM 4744 := by
    rw [rSM, rPM, s7452, p14697, hv4738, hw]
  have hshape : (denoteGraphDistributed sm initSM 4744).shape = [4096, 4, 64] := by
    rw [rSM]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s7452]; exact hs4738) hsw
  exact wrap_1tp_gen _ _ intermediateGoal_4744 4744 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

theorem layer1_rotary_cache_distributed (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11854 := by
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11854 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14 layer1PmCache 4691 11854 id (by native_decide)
      layer1_pm_node14 (by decide)
      (fun s => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm s layer1PmCache (by decide) (by decide)]
        unfold layer1PmCache
        rw [applyNode_fw_multiref_mem_out pm s 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11854 (by native_decide), id_eq])
      layer1_pm_drop15_nonempty layer1_pm_drop15_no11854
      layer1_pm_drop14_nonempty layer1_pm_drop14_no4691
  rw [hcopy, id_eq]
  exact hbase

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4746_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4746
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4740 := recon_intermediateGoal_4740_distributed initSM initPM hSM hPM hInit
  have hv4740 := oneTp_valeq intermediateGoal_4740 _ _ 4740 rfl rfl rfl rfl h4740
  have hs4740 : (denoteGraphDistributed sm initSM 4740).shape = [4096, 16, 64] := by
    have hs := h4740.1; simpa [intermediateGoal_4740] using hs
  have h4742 := recon_intermediateGoal_4742_distributed initSM initPM hSM hPM hInit
  have hv4742 := oneTp_valeq intermediateGoal_4742 _ _ 4742 rfl rfl rfl rfl h4742
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4745
    (by native_decide) 4745 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcache := layer1_rotary_cache_distributed initSM initPM hInit
  have rSM : denoteGraphDistributed sm initSM 4746 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691)
        (denoteGraphDistributed sm initSM 4745) (denoteGraphDistributed sm initSM 4740)
        (denoteGraphDistributed sm initSM 4742) 16 4).1 := by
    rw [distributed_node_core sm initSM 47 layer1SmRotary 4746 (by native_decide)
      layer1_sm_node47 (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ layer1SmRotary (by decide) (by decide)]
    rw [show layer1SmRotary =
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4745, 4740, 4742],
        outs := [4746, 4747], params := [16, 4] } by rfl,
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 47 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 47 4745 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 47 4740 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 47 4742 (by native_decide) (by native_decide)]
  have rPM : denoteGraphDistributed pm initPM 4746 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11854)
        (denoteGraphDistributed pm initPM 4745) (denoteGraphDistributed pm initPM 4740)
        (denoteGraphDistributed pm initPM 4742) 16 4).1 := by
    rw [distributed_node_core pm initPM 137 layer1PmRotary 4746 (by native_decide)
      layer1_pm_node137 (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ layer1PmRotary (by decide) (by decide)]
    rw [show layer1PmRotary =
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742],
        outs := [4746, 4747], params := [16, 4] } by rfl,
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 137 11854 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 137 4745 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 137 4740 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 137 4742 (by native_decide) (by native_decide)]
  have hval : denoteGraphDistributed sm initSM 4746 = denoteGraphDistributed pm initPM 4746 := by
    rw [rSM, rPM, hcache, hw, hv4740, hv4742]
  have hshape : (denoteGraphDistributed sm initSM 4746).shape = [4096, 16, 64] := by
    rw [rSM, fw_rotary_embedding_fst_shape]; exact hs4740
  exact wrap_1tp_gen _ _ intermediateGoal_4746 4746 [4096, 16, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4747_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4747
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4740 := recon_intermediateGoal_4740_distributed initSM initPM hSM hPM hInit
  have hv4740 := oneTp_valeq intermediateGoal_4740 _ _ 4740 rfl rfl rfl rfl h4740
  have h4742 := recon_intermediateGoal_4742_distributed initSM initPM hSM hPM hInit
  have hv4742 := oneTp_valeq intermediateGoal_4742 _ _ 4742 rfl rfl rfl rfl h4742
  have hs4742 : (denoteGraphDistributed sm initSM 4742).shape = [4096, 4, 64] := by
    have hs := h4742.1; simpa [intermediateGoal_4742] using hs
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4745
    (by native_decide) 4745 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcache := layer1_rotary_cache_distributed initSM initPM hInit
  have rSM : denoteGraphDistributed sm initSM 4747 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691)
        (denoteGraphDistributed sm initSM 4745) (denoteGraphDistributed sm initSM 4740)
        (denoteGraphDistributed sm initSM 4742) 16 4).2 := by
    rw [distributed_node_core sm initSM 47 layer1SmRotary 4747 (by native_decide)
      layer1_sm_node47 (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ layer1SmRotary (by decide) (by decide)]
    rw [show layer1SmRotary =
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4745, 4740, 4742],
        outs := [4746, 4747], params := [16, 4] } by rfl,
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4745 4740 4742 4746 4747 (by decide),
      distributed_prefix_read sm initSM 47 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 47 4745 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 47 4740 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 47 4742 (by native_decide) (by native_decide)]
  have rPM : denoteGraphDistributed pm initPM 4747 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11854)
        (denoteGraphDistributed pm initPM 4745) (denoteGraphDistributed pm initPM 4740)
        (denoteGraphDistributed pm initPM 4742) 16 4).2 := by
    rw [distributed_node_core pm initPM 137 layer1PmRotary 4747 (by native_decide)
      layer1_pm_node137 (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ layer1PmRotary (by decide) (by decide)]
    rw [show layer1PmRotary =
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742],
        outs := [4746, 4747], params := [16, 4] } by rfl,
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11854 4745 4740 4742 4746 4747 (by decide),
      distributed_prefix_read pm initPM 137 11854 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 137 4745 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 137 4740 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 137 4742 (by native_decide) (by native_decide)]
  have hval : denoteGraphDistributed sm initSM 4747 = denoteGraphDistributed pm initPM 4747 := by
    rw [rSM, rPM, hcache, hw, hv4740, hv4742]
  have hshape : (denoteGraphDistributed sm initSM 4747).shape = [4096, 4, 64] := by
    rw [rSM, fw_rotary_embedding_snd_shape]; exact hs4742
  exact wrap_1tp_gen _ _ intermediateGoal_4747 4747 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

#print axioms recon_intermediateGoal_4744_distributed
#print axioms recon_intermediateGoal_4746_distributed
#print axioms recon_intermediateGoal_4747_distributed

/-! ## Layer-1 sliding attention over distributed folds

The following gear keeps the production semantics visible: buddy shards are
contiguously gathered on dim 0, one full `fw_attn_varlen` (with the original
window parameter) is evaluated, and the result is chunked on dim 0. -/

private theorem foldl_take_split_at_not_written_distributed
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store) (tid : Tid)
    (j k : Nat) (hjk : j ≤ k)
    (hnil : ((nodes.take k).drop j).all (fun n => !n.outs.isEmpty) = true)
    (h : ((nodes.take k).drop j).all (fun n => !n.outs.contains tid) = true) :
    (nodes.take k).foldl (applyNodeDistributed g) s tid =
      (nodes.take j).foldl (applyNodeDistributed g) s tid := by
  have hnil' : ∀ n ∈ (nodes.take k).drop j, n.outs ≠ [] := by
    intro n hn
    have hn := (List.all_eq_true.mp hnil) n hn
    simpa using hn
  have h' : ∀ n ∈ (nodes.take k).drop j, tid ∉ n.outs := by
    intro n hn
    have ht := (List.all_eq_true.mp h) n hn
    simpa using ht
  have hsplit : nodes.take k = nodes.take j ++ (nodes.take k).drop j := by
    rw [show nodes.take j = (nodes.take k).take j by rw [List.take_take, min_eq_left hjk]]
    rw [List.take_append_drop]
  rw [hsplit, List.foldl_append]
  exact foldl_applyNodeDistributed_at_not_written g _ _ tid hnil' h'

private theorem recon_attn_sliding_window_2tp_distributed
    (initSM initPM : Store) (g : LineageGoal)
    (nSM nR0 nR1 : NodeDecl) (foldSM foldPM foldPM' : Store)
    (oSM oR0 oR1 : Tid) (L nh kh : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh)
    (hSMred : denoteGraphDistributed sm initSM oSM =
      applyNodeRingAttn_sliding_window sm foldSM nSM)
    (hR0red : denoteGraphDistributed pm initPM oR0 =
      applyNodeRingAttn_sliding_window pm foldPM nR0)
    (hR1red : denoteGraphDistributed pm initPM oR1 =
      applyNodeRingAttn_sliding_window pm foldPM' nR1)
    (hbridge : applyNodeRingAttn_sliding_window pm foldPM nR1 =
      applyNodeRingAttn_sliding_window pm foldPM' nR1)
    (hbuddySM : ringAttnBuddies sm nSM = [nSM])
    (hbuddyR0 : ringAttnBuddies pm nR0 = [nR0, nR1])
    (hbuddyR1 : ringAttnBuddies pm nR1 = [nR0, nR1])
    (hidx0 : (([nR0, nR1].findIdx? (fun m => m.rank = nR0.rank)).getD 0) = 0)
    (hidx1 : (([nR0, nR1].findIdx? (fun m => m.rank = nR1.rank)).getD 0) = 1)
    (hq : 0 < (foldSM (nSM.ins.getD 0 0)).shape.length)
    (hk : 0 < (foldSM (nSM.ins.getD 1 0)).shape.length)
    (hv : 0 < (foldSM (nSM.ins.getD 2 0)).shape.length)
    (hqfull : foldSM (nSM.ins.getD 0 0) = allGatherPrimDimN 0 2 0
      [foldPM (nR0.ins.getD 0 0), foldPM (nR1.ins.getD 0 0)])
    (hkfull : foldSM (nSM.ins.getD 1 0) = allGatherPrimDimN 0 2 0
      [foldPM (nR0.ins.getD 1 0), foldPM (nR1.ins.getD 1 0)])
    (hvfull : foldSM (nSM.ins.getD 2 0) = allGatherPrimDimN 0 2 0
      [foldPM (nR0.ins.getD 2 0), foldPM (nR1.ins.getD 2 0)])
    (hcuQ : foldSM (nSM.ins.getD 3 0) = foldPM (nR0.ins.getD 3 0))
    (hcuK : foldSM (nSM.ins.getD 4 0) = foldPM (nR0.ins.getD 4 0))
    (hcuQsame : foldPM (nR0.ins.getD 3 0) = foldPM (nR1.ins.getD 3 0))
    (hcuKsame : foldPM (nR0.ins.getD 4 0) = foldPM (nR1.ins.getD 4 0))
    (hparams : nSM.params = nR0.params) (hparams' : nR0.params = nR1.params)
    (hfullShape : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 0 0), foldPM (nR1.ins.getD 0 0)])
      (allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 1 0), foldPM (nR1.ins.getD 1 0)])
      (allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 2 0), foldPM (nR1.ins.getD 2 0)])
      (foldPM (nR0.ins.getD 3 0)) (foldPM (nR0.ins.getD 4 0))
      (nR0.params.getD 0 1) (nR0.params.getD 1 1) (nR0.params.getD 2 1)
      (nR0.params.getD 3 1) (decide (nR0.params.getD 4 0 ≠ 0))
      (nR0.params.getD 5 0)).shape = [2 * L, nh, kh])
    (hfullShape' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 0 0), foldPM' (nR1.ins.getD 0 0)])
      (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 1 0), foldPM' (nR1.ins.getD 1 0)])
      (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 2 0), foldPM' (nR1.ins.getD 2 0)])
      (foldPM' (nR1.ins.getD 3 0)) (foldPM' (nR1.ins.getD 4 0))
      (nR1.params.getD 0 1) (nR1.params.getD 1 1) (nR1.params.getD 2 1)
      (nR1.params.getD 3 1) (decide (nR1.params.getD 4 0 ≠ 0))
      (nR1.params.getD 5 0)).shape = [2 * L, nh, kh])
    (htp : g.tps = [{ rank := 0, tid := oR0 }, { rank := 1, tid := oR1 }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false)
    (hts : g.ts = oSM) (htss : g.tsShape = [2 * L, nh, kh])
    (htps : g.tpShapes = [[L, nh, kh], [L, nh, kh]]) :
    InitGoalHolds pm.numRanks g (denoteGraphDistributed sm initSM)
      (denoteGraphDistributed pm initPM) := by
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm pm foldSM foldPM nSM nR0 nR1 L nh kh hL hnh hkh hbuddySM hbuddyR0
    hbuddyR1 hidx0 hidx1 hq hk hv hqfull hkfull hvfull hcuQ hcuK hcuQsame
    hcuKsame hparams hparams' hfullShape
  have hval : denoteGraphDistributed sm initSM oSM = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM oR0, denoteGraphDistributed pm initPM oR1] := by
    rw [hSMred, hrec, hbridge, ← hR0red, ← hR1red, show pm.numRanks = 2 from rfl]
  have hs0 : (denoteGraphDistributed pm initPM oR0).shape = [L, nh, kh] := by
    rw [hR0red, applyNodeRingAttn_sliding_window_pair_eq_chunk pm foldPM nR0 nR0 nR1 0
      hbuddyR0 hidx0, chunkPrimDimN_shape 0 2 0 _ [2 * L, nh, kh] hfullShape (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [show 2 * L / 2 = L from by omega]
  have hs1 : (denoteGraphDistributed pm initPM oR1).shape = [L, nh, kh] := by
    rw [hR1red, applyNodeRingAttn_sliding_window_pair_eq_chunk pm foldPM' nR1 nR0 nR1 1
      hbuddyR1 hidx1, chunkPrimDimN_shape 0 2 1 _ [2 * L, nh, kh] hfullShape' (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [show 2 * L / 2 = L from by omega]
  have hs : (denoteGraphDistributed sm initSM oSM).shape = [2 * L, nh, kh] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 [denoteGraphDistributed pm initPM oR0,
        denoteGraphDistributed pm initPM oR1] [L, nh, kh] (by simpa using hs0)]
    simp only [List.set, List.getD_cons_zero]
    rw [show L * 2 = 2 * L from by omega]
  exact wrap_2tp_allGather_gen _ _ g oSM oR0 oR1 [2 * L, nh, kh] [L, nh, kh]
    htp hgd hrep hts htss htps (by intro h; simpa using congrArg List.length h)
    hval hs hs0 hs1

private def layer1SmSliding : NodeDecl := nSM_L1
private def layer1PmSliding0 : NodeDecl := nR0_L1
private def layer1PmSliding1 : NodeDecl := nR1_L1

-- Split concrete certificates keep native reduction away from the large proof term.
set_option maxRecDepth 1000000 in
theorem layer1_sm_node48 : sm.nodes[48]'(by native_decide) = layer1SmSliding := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_node144 : pm.nodes[144]'(by native_decide) = layer1PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_node145 : pm.nodes[145]'(by native_decide) = layer1PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_sm_buddy_sliding : ringAttnBuddies sm layer1SmSliding = [layer1SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_buddy_sliding0 : ringAttnBuddies pm layer1PmSliding0 = [layer1PmSliding0, layer1PmSliding1] := by native_decide
set_option maxRecDepth 1000000 in
theorem layer1_pm_buddy_sliding1 : ringAttnBuddies pm layer1PmSliding1 = [layer1PmSliding0, layer1PmSliding1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4750_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4750
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have gq := recon_intermediateGoal_4746_distributed initSM initPM hSM hPM hInit
  have gk := recon_intermediateGoal_4747_distributed initSM initPM hSM hPM hInit
  have gv := recon_intermediateGoal_4744_distributed initSM initPM hSM hPM hInit
  have hqv := oneTp_valeq intermediateGoal_4746 _ _ 4746 rfl rfl rfl rfl gq
  have hkv := oneTp_valeq intermediateGoal_4747 _ _ 4747 rfl rfl rfl rfl gk
  have hvv := oneTp_valeq intermediateGoal_4744 _ _ 4744 rfl rfl rfl rfl gv
  have hqs : (denoteGraphDistributed pm initPM 4746).shape = [2 * 2048, 16, 64] := by
    rw [← hqv]; exact gq.1
  have hks : (denoteGraphDistributed pm initPM 4747).shape = [2 * 2048, 4, 64] := by
    rw [← hkv]; exact gk.1
  have hvs : (denoteGraphDistributed pm initPM 4744).shape = [2 * 2048, 4, 64] := by
    rw [← hvv]; exact gv.1
  have hcu4748 := distributed_init_singleton_value initSM initPM hInit initGoal_4748
    (by native_decide) 4748 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu4749 := distributed_init_singleton_value initSM initPM hInit initGoal_4749
    (by native_decide) 4749 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have c7619 := distributed_reduce1 pm initPM 140
    {rank := 0, op := "OpName.ChunkPrim", ins := [4746], outs := [7619], params := [0]}
    4746 7619 (chunkPrimDimN 0 pm.numRanks 0) (by native_decide) (by native_decide)
    (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4746 7619 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c7620 := distributed_reduce1 pm initPM 142
    {rank := 1, op := "OpName.ChunkPrim", ins := [4746], outs := [7620], params := [0]}
    4746 7620 (chunkPrimDimN 0 pm.numRanks 1) (by native_decide) (by native_decide)
    (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4746 7620 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c7621 := distributed_reduce1 pm initPM 141
    {rank := 0, op := "OpName.ChunkPrim", ins := [4747], outs := [7621], params := [0]}
    4747 7621 (chunkPrimDimN 0 pm.numRanks 0) (by native_decide) (by native_decide)
    (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4747 7621 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c7622 := distributed_reduce1 pm initPM 143
    {rank := 1, op := "OpName.ChunkPrim", ins := [4747], outs := [7622], params := [0]}
    4747 7622 (chunkPrimDimN 0 pm.numRanks 1) (by native_decide) (by native_decide)
    (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4747 7622 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c7607 := distributed_reduce1 pm initPM 138
    {rank := 0, op := "OpName.ChunkPrim", ins := [4744], outs := [7607], params := [0]}
    4744 7607 (chunkPrimDimN 0 pm.numRanks 0) (by native_decide) (by native_decide)
    (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4744 7607 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c7608 := distributed_reduce1 pm initPM 139
    {rank := 1, op := "OpName.ChunkPrim", ins := [4744], outs := [7608], params := [0]}
    4744 7608 (chunkPrimDimN 0 pm.numRanks 1) (by native_decide) (by native_decide)
    (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4744 7608 0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  let fs := (sm.nodes.take 48).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 144).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 145).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 48, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 48, t ∉ n.outs) : fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 48 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 144, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 144, t ∉ n.outs) : fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 144 t hn hw
  have hqfull : fs 4746 = allGatherPrimDimN 0 2 0 [fp 7619, fp 7620] := by
    rw [bs 4746 (by native_decide) (by native_decide), bp 7619 (by native_decide) (by native_decide),
      bp 7620 (by native_decide) (by native_decide), c7619, c7620, hqv,
      show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega) _ hqs).symm
  have hkfull : fs 4747 = allGatherPrimDimN 0 2 0 [fp 7621, fp 7622] := by
    rw [bs 4747 (by native_decide) (by native_decide), bp 7621 (by native_decide) (by native_decide),
      bp 7622 (by native_decide) (by native_decide), c7621, c7622, hkv,
      show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega) _ hks).symm
  have hvfull : fs 4744 = allGatherPrimDimN 0 2 0 [fp 7607, fp 7608] := by
    rw [bs 4744 (by native_decide) (by native_decide), bp 7607 (by native_decide) (by native_decide),
      bp 7608 (by native_decide) (by native_decide), c7607, c7608, hvv,
      show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega) _ hvs).symm
  have hqpos : 0 < (fs (layer1SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 4746).shape.length
    rw [bs 4746 (by native_decide) (by native_decide), hqv, hqs]; decide
  have hkpos : 0 < (fs (layer1SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 4747).shape.length
    rw [bs 4747 (by native_decide) (by native_decide), hkv, hks]; decide
  have hvpos : 0 < (fs (layer1SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 4744).shape.length
    rw [bs 4744 (by native_decide) (by native_decide), hvv, hvs]; decide
  have hcuQ : fs 4748 = fp 4748 := by
    rw [bs 4748 (by native_decide) (by native_decide), bp 4748 (by native_decide) (by native_decide), hcu4748]
  have hcuK : fs 4749 = fp 4749 := by
    rw [bs 4749 (by native_decide) (by native_decide), bp 4749 (by native_decide) (by native_decide), hcu4749]
  have e7619 : fp 7619 = fp' 7619 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7619 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have e7620 : fp 7620 = fp' 7620 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7620 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have e7621 : fp 7621 = fp' 7621 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7621 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have e7622 : fp 7622 = fp' 7622 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7622 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have e7607 : fp 7607 = fp' 7607 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7607 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have e7608 : fp 7608 = fp' 7608 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7608 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have e4748 : fp 4748 = fp' 4748 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4748 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have e4749 : fp 4749 = fp' 4749 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4749 144 145
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer1PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer1PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer1_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7619
      · exact e7620
    · rw [layer1_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7621
      · exact e7622
    · rw [layer1_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7607
      · exact e7608
    · exact e4748
    · exact e4749
  have rSM : denoteGraphDistributed sm initSM 4750 =
      applyNodeRingAttn_sliding_window sm fs layer1SmSliding := by
    rw [distributed_node_core sm initSM 48 layer1SmSliding 4750 (by native_decide)
      layer1_sm_node48 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4746 4747 4744 4748 4749 4750
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 7623 =
      applyNodeRingAttn_sliding_window pm fp layer1PmSliding0 := by
    rw [distributed_node_core pm initPM 144 layer1PmSliding0 7623 (by native_decide)
      layer1_pm_node144 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 7619 7621 7607 4748 4749 7623
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 7624 =
      applyNodeRingAttn_sliding_window pm fp' layer1PmSliding1 := by
    rw [distributed_node_core pm initPM 145 layer1PmSliding1 7624 (by native_decide)
      layer1_pm_node145 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 7620 7622 7608 4748 4749 7624
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 7619, fp 7620])
      (allGatherPrimDimN 0 2 0 [fp 7621, fp 7622])
      (allGatherPrimDimN 0 2 0 [fp 7607, fp 7608])
      (fp 4748) (fp 4749) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 4746 (by native_decide) (by native_decide), hqv, hqs]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 7619, fp' 7620])
      (allGatherPrimDimN 0 2 0 [fp' 7621, fp' 7622])
      (allGatherPrimDimN 0 2 0 [fp' 7607, fp' 7608])
      (fp' 4748) (fp' 4749) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e7619, ← e7620, ← e7621, ← e7622, ← e7607, ← e7608,
      ← e4748, ← e4749]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_4750
    layer1SmSliding layer1PmSliding0 layer1PmSliding1 fs fp fp' 4750 7623 7624
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer1_sm_buddy_sliding layer1_pm_buddy_sliding0 layer1_pm_buddy_sliding1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

#print axioms recon_intermediateGoal_4750_distributed

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
