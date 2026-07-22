/- Layer-0 template for migrating MoE reconstruction to the canonical
   full-expert distributed denotation.  This file intentionally touches only
   intermediate goal 4714. -/
import denote.yoco_goals.MoEShardedReconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- Outside a MoE node, the distributed step is exactly the existing ring-aware
    step.  This is the fold/apply bridge used by the migration template. -/
theorem applyNodeDistributed_eq_ring_of_not_moe (g : GraphDecl) (s : Store)
    (n : NodeDecl) (h : n.op ≠ "OpName.FW_all2all_moe_gmm") :
    applyNodeDistributed g s n = applyNodeRingAttn g s n := by
  unfold applyNodeDistributed
  rw [if_neg h]

/-- A distributed step preserves a tid outside the node's output list. -/
theorem applyNodeDistributed_skip (g : GraphDecl) (s : Store) (n : NodeDecl) (tid : Tid)
    (hne : n.outs ≠ []) (h : tid ∉ n.outs) :
    applyNodeDistributed g s n tid = s tid := by
  by_cases hm : n.op = "OpName.FW_all2all_moe_gmm"
  · unfold applyNodeDistributed
    rw [if_pos hm]
    have hmem : n.outs.getD 0 0 ∈ n.outs := by
      cases ho : n.outs with
      | nil => exact absurd ho hne
      | cons a rest => rw [List.getD_cons_zero]; exact List.mem_cons_self
    apply storeSet_eq_of_not_mem_fst
    simpa using (fun heq : tid = n.outs.getD 0 0 => h (heq ▸ hmem))
  · rw [applyNodeDistributed_eq_ring_of_not_moe g s n hm]
    exact applyNodeRingAttn_skip g s n tid hne h

/-- A distributed fold preserves a tid never written by its node list. -/
theorem foldl_applyNodeDistributed_at_not_written
    (g : GraphDecl) (pre : List NodeDecl) (s : Store) (tid : Tid)
    (hnil : ∀ n ∈ pre, n.outs ≠ [])
    (h : ∀ n ∈ pre, tid ∉ n.outs) :
    (pre.foldl (applyNodeDistributed g) s) tid = s tid := by
  induction pre generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl]
    rw [ih]
    · exact applyNodeDistributed_skip g s a tid
        (hnil a List.mem_cons_self) (h a List.mem_cons_self)
    · intro n hn; exact hnil n (List.mem_cons_of_mem _ hn)
    · intro n hn; exact h n (List.mem_cons_of_mem _ hn)

/-- Distributed-fold prefix reduction, parallel to `foldl_prefix_ring_g12`. -/
theorem foldl_prefix_distributed (g : GraphDecl) (nodes : List NodeDecl)
    (s : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ nodes.drop k, n.outs ≠ [])
    (h : ∀ n ∈ nodes.drop k, tid ∉ n.outs) :
    nodes.foldl (applyNodeDistributed g) s tid =
      (nodes.take k).foldl (applyNodeDistributed g) s tid := by
  conv_lhs => rw [← List.take_append_drop k nodes, List.foldl_append]
  exact foldl_applyNodeDistributed_at_not_written g _ _ tid hnil h

theorem foldl_take_distributed_eq (g : GraphDecl)
    (s : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    (g.nodes.take k).foldl (applyNodeDistributed g) s tid =
      denoteGraphDistributed g s tid := by
  rw [denoteGraphDistributed]
  exact (foldl_prefix_distributed g g.nodes s tid k hnil hwrite).symm

/-- Before the first MoE node, distributed and ring-aware folds coincide. -/
theorem foldl_distributed_eq_ring_of_no_moe (g : GraphDecl) (pre : List NodeDecl)
    (s : Store) (h : ∀ n ∈ pre, n.op ≠ "OpName.FW_all2all_moe_gmm") :
    pre.foldl (applyNodeDistributed g) s = pre.foldl (applyNodeRingAttn g) s := by
  induction pre generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl]
    rw [applyNodeDistributed_eq_ring_of_not_moe g s a (h a List.mem_cons_self)]
    exact ih _ (fun n hn => h n (List.mem_cons_of_mem _ hn))

/-- A convenient concrete bridge: when `take k` contains no MoE and neither
    suffix writes `tid`, canonical distributed and ring denotations agree. -/
theorem denoteGraphDistributed_eq_ring_before_moe (g : GraphDecl) (init : Store)
    (tid : Tid) (k : Nat)
    (hno : ∀ n ∈ g.nodes.take k, n.op ≠ "OpName.FW_all2all_moe_gmm")
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributed g init tid = denoteGraph_ringAttn g init tid := by
  rw [denoteGraphDistributed, denoteGraph_ringAttn,
      foldl_prefix_distributed g g.nodes init tid k hnil hwrite,
      foldl_prefix_ring_g12 g g.nodes init tid k hnil hwrite,
      foldl_distributed_eq_ring_of_no_moe g (g.nodes.take k) init hno]

/-- Reduce one concrete distributed node to its faithful full-expert value. -/
theorem distributed_moe_reduce (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (outTid : Tid)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hop : node.op = "OpName.FW_all2all_moe_gmm")
    (hout : node.outs = [outTid])
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      applyNodeFullExpertMoE_value g
        ((g.nodes.take k).foldl (applyNodeDistributed g) init) node := by
  have hstep := congrFun (foldl_take_succ (applyNodeDistributed g) g.nodes init k hk) outTid
  rw [denoteGraphDistributed,
      foldl_prefix_distributed g g.nodes init outTid (k + 1) hdrop_nil hdrop,
      hstep, hnode]
  unfold applyNodeDistributed
  rw [if_pos hop]
  change storeSet _ [(node.outs.getD 0 0, _)] outTid = _
  rw [hout]
  unfold storeSet
  simp [List.find?]

theorem distributed_allGather2_reduce (g : GraphDecl) (init : Store) (k : Nat)
    (t0 t1 outTid dim : Tid)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk =
      { rank := 0, op := "OpName.AllGatherPrim", ins := [t0, t1],
        outs := [outTid], params := [dim] })
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, t0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, t1 ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      allGatherPrimDimN dim g.numRanks 0
        [denoteGraphDistributed g init t0, denoteGraphDistributed g init t1] := by
  have hstep := congrFun (foldl_take_succ (applyNodeDistributed g) g.nodes init k hk) outTid
  rw [denoteGraphDistributed,
    foldl_prefix_distributed g g.nodes init outTid (k + 1) hdrop_nil hdrop,
    hstep, hnode,
    applyNodeDistributed_eq_ring_of_not_moe g _ _ (by simp),
    applyNodeRingAttn_eq_applyNode_of_not_ring g _ _ (by simp) (by simp),
    applyNode_allGatherPrimDimN_out g _ 0 [t0, t1] outTid dim]
  simp only [List.map]
  rw [foldl_take_distributed_eq g init t0 k hpre_nil hpre0,
    foldl_take_distributed_eq g init t1 k hpre_nil hpre1]
  rfl

private def layer0SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7419, 4709, 4710, 4712, 4713], outs := [4714],
    params := [64, 0, 64, 8] }

private def layer0PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [11941, 7481, 7483, 7487, 7489], outs := [7491],
    params := [64, 0, 32, 8] }

private def layer0PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [11942, 7482, 7484, 7488, 7490], outs := [7492],
    params := [64, 32, 64, 8] }

private def layer0PmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [7491, 7492],
    outs := [4714], params := [0] }

set_option maxRecDepth 1000000 in
theorem layer0_sm_moe_value (initSM : Store) :
    denoteGraphDistributed sm initSM 4714 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributed sm initSM 7419) (denoteGraphDistributed sm initSM 4709)
        (denoteGraphDistributed sm initSM 4710) [denoteGraphDistributed sm initSM 4712]
        [denoteGraphDistributed sm initSM 4713] 64 8 (((10 : Nat) : Scalar)) := by
  rw [distributed_moe_reduce sm initSM 31 layer0SmMoe 4714
    (by native_decide) (by native_decide) rfl rfl
    (by native_decide) (by native_decide)]
  unfold applyNodeFullExpertMoE_value
  rw [show sm.replicaBuddies layer0SmMoe = [layer0SmMoe] by native_decide]
  simp only [layer0SmMoe, List.map, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_some, Option.getD_none]
  rw [show (sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM 7419 =
        denoteGraphDistributed sm initSM 7419 by
      rw [denoteGraphDistributed,
        foldl_prefix_distributed sm sm.nodes initSM 7419 31 (by native_decide) (by native_decide)],
    show (sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM 4709 =
        denoteGraphDistributed sm initSM 4709 by
      rw [denoteGraphDistributed,
        foldl_prefix_distributed sm sm.nodes initSM 4709 31 (by native_decide) (by native_decide)],
    show (sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM 4710 =
        denoteGraphDistributed sm initSM 4710 by
      rw [denoteGraphDistributed,
        foldl_prefix_distributed sm sm.nodes initSM 4710 31 (by native_decide) (by native_decide)],
    show (sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM 4712 =
        denoteGraphDistributed sm initSM 4712 by
      rw [denoteGraphDistributed,
        foldl_prefix_distributed sm sm.nodes initSM 4712 31 (by native_decide) (by native_decide)],
    show (sm.nodes.take 31).foldl (applyNodeDistributed sm) initSM 4713 =
        denoteGraphDistributed sm initSM 4713 by
      rw [denoteGraphDistributed,
        foldl_prefix_distributed sm sm.nodes initSM 4713 31 (by native_decide) (by native_decide)]]

set_option maxRecDepth 1000000 in
theorem layer0_pm_moe0_value (initPM : Store) :
    denoteGraphDistributed pm initPM 7491 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributed pm initPM 11941) (denoteGraphDistributed pm initPM 7481)
        (denoteGraphDistributed pm initPM 7483)
        [denoteGraphDistributed pm initPM 7487, denoteGraphDistributed pm initPM 7488]
        [denoteGraphDistributed pm initPM 7489, denoteGraphDistributed pm initPM 7490]
        64 8 (((10 : Nat) : Scalar)) := by
  rw [distributed_moe_reduce pm initPM 104 layer0PmMoe0 7491
    (by native_decide) (by native_decide) rfl rfl
    (by native_decide) (by native_decide)]
  unfold applyNodeFullExpertMoE_value
  rw [show pm.replicaBuddies layer0PmMoe0 = [layer0PmMoe0, layer0PmMoe1] by
    native_decide]
  simp only [layer0PmMoe0, layer0PmMoe1, List.map, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_some, Option.getD_none]
  rw [foldl_take_distributed_eq pm initPM 11941 104
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7481 104
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7483 104
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7487 104
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7488 104
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7489 104
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7490 104
      (by native_decide) (by native_decide)]

set_option maxRecDepth 1000000 in
theorem layer0_pm_moe1_value (initPM : Store) :
    denoteGraphDistributed pm initPM 7492 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributed pm initPM 11942) (denoteGraphDistributed pm initPM 7482)
        (denoteGraphDistributed pm initPM 7484)
        [denoteGraphDistributed pm initPM 7487, denoteGraphDistributed pm initPM 7488]
        [denoteGraphDistributed pm initPM 7489, denoteGraphDistributed pm initPM 7490]
        64 8 (((10 : Nat) : Scalar)) := by
  rw [distributed_moe_reduce pm initPM 105 layer0PmMoe1 7492
    (by native_decide) (by native_decide) rfl rfl
    (by native_decide) (by native_decide)]
  unfold applyNodeFullExpertMoE_value
  rw [show pm.replicaBuddies layer0PmMoe1 = [layer0PmMoe0, layer0PmMoe1] by
    native_decide]
  simp only [layer0PmMoe0, layer0PmMoe1, List.map, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_some, Option.getD_none]
  rw [foldl_take_distributed_eq pm initPM 11942 105
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7482 105
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7484 105
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7487 105
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7488 105
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7489 105
      (by native_decide) (by native_decide),
    foldl_take_distributed_eq pm initPM 7490 105
      (by native_decide) (by native_decide)]

set_option maxRecDepth 1000000 in
theorem layer0_pm_node108 : pm.nodes[108]'(by native_decide) = layer0PmGather := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer0_pm_drop108_nonempty : ∀ n ∈ pm.nodes.drop 108, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer0_pm_drop108_no7491 : ∀ n ∈ pm.nodes.drop 108, 7491 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer0_pm_drop108_no7492 : ∀ n ∈ pm.nodes.drop 108, 7492 ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer0_pm_drop109_nonempty : ∀ n ∈ pm.nodes.drop 109, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
theorem layer0_pm_drop109_no4714 : ∀ n ∈ pm.nodes.drop 109, 4714 ∉ n.outs := by
  native_decide

set_option maxRecDepth 10000000 in
theorem layer0_pm_gather_value (initPM : Store) :
    denoteGraphDistributed pm initPM 4714 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7491, denoteGraphDistributed pm initPM 7492] := by
  have hk : 108 < pm.nodes.length := by native_decide
  have hnode : pm.nodes[108]'hk =
      { rank := 0, op := "OpName.AllGatherPrim", ins := [7491, 7492],
        outs := [4714], params := [0] } := by
    rw [show pm.nodes[108]'hk = layer0PmGather from layer0_pm_node108]
    rfl
  have h := distributed_allGather2_reduce pm initPM 108 7491 7492 4714 0
    hk hnode layer0_pm_drop109_nonempty layer0_pm_drop109_no4714
    layer0_pm_drop108_nonempty layer0_pm_drop108_no7491 layer0_pm_drop108_no7492
  rw [show pm.numRanks = 2 from rfl] at h
  exact h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
/- **Exact layer-0 replacement for intermediate goal 4714.**  Under the
    canonical distributed semantics both PM MoE replicas evaluate the full
    expert set from the exact declared buddy group.  Consequently the existing
    full-expert split commute applies directly; no routing locality or
    disjointness hypothesis appears in the statement. -/
theorem recon_intermediateGoal_4714_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4714
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  -- Before the first MoE call, distributed and ring semantics are identical.
  have dsm (tid : Tid) (hw : ∀ n ∈ sm.nodes.drop 31, tid ∉ n.outs) :
      denoteGraphDistributed sm initSM tid = denoteGraph_ringAttn sm initSM tid :=
    denoteGraphDistributed_eq_ring_before_moe sm initSM tid 31
      (by native_decide) (by native_decide) hw
  have dpm (tid : Tid) (hw : ∀ n ∈ pm.nodes.drop 104, tid ∉ n.outs) :
      denoteGraphDistributed pm initPM tid = denoteGraph_ringAttn pm initPM tid :=
    denoteGraphDistributed_eq_ring_before_moe pm initPM tid 104
      (by native_decide) (by native_decide) hw
  have deq7419 := dsm 7419 (by native_decide)
  have deq4709 := dsm 4709 (by native_decide)
  have deq4710 := dsm 4710 (by native_decide)
  have deq4712 := dsm 4712 (by native_decide)
  have deq4713 := dsm 4713 (by native_decide)
  have deq11941 := dpm 11941 (by native_decide)
  have deq11942 := dpm 11942 (by native_decide)
  have deq7481 := dpm 7481 (by native_decide)
  have deq7482 := dpm 7482 (by native_decide)
  have deq7483 := dpm 7483 (by native_decide)
  have deq7484 := dpm 7484 (by native_decide)
  have deq7487 := dpm 7487 (by native_decide)
  have deq7488 := dpm 7488 (by native_decide)
  have deq7489 := dpm 7489 (by native_decide)
  have deq7490 := dpm 7490 (by native_decide)

  -- Reuse the already-proved pre-MoE ring reconstruction bridges.
  have h7419 := recon_intermediateGoal_7419_ringAttn initSM initPM hSM hPM hInit
  have h4709 := recon_intermediateGoal_4709_ringAttn initSM initPM hSM hPM hInit
  have h4710 := recon_intermediateGoal_4710_ringAttn initSM initPM hSM hPM hInit
  have hsInA_ring : (denoteGraph_ringAttn pm initPM 11941).shape = [2048, 1024] := by
    have hs := h7419.2.1
    simp only [intermediateGoal_7419, List.map, List.cons.injEq, and_true] at hs
    exact hs.1
  have hsInB_ring : (denoteGraph_ringAttn pm initPM 11942).shape = [2048, 1024] := by
    have hs := h7419.2.1
    simp only [intermediateGoal_7419, List.map, List.cons.injEq, and_true] at hs
    exact hs.2
  have hbrIn_ring : denoteGraph_ringAttn sm initSM 7419 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm initPM 11941, denoteGraph_ringAttn pm initPM 11942] := by
    have hv := h7419.2.2
    rw [reconstructForGoal_of_not_replicated intermediateGoal_7419 pm.numRanks _ rfl] at hv
    simp only [intermediateGoal_7419, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsInA_ring]; decide)] at hv
    exact hv
  have hbrRp_ring : denoteGraph_ringAttn sm initSM 4709 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm initPM 7481, denoteGraph_ringAttn pm initPM 7482] := by
    have hv := h4709.2.2
    rw [reconstructForGoal_of_not_replicated intermediateGoal_4709 pm.numRanks _ rfl] at hv
    simp only [intermediateGoal_4709, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by have hs := h4709.2.1
          simp only [intermediateGoal_4709, List.map, List.cons.injEq, and_true] at hs
          rw [hs.1]; decide)] at hv
    exact hv
  have hbrRm_ring : denoteGraph_ringAttn sm initSM 4710 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm initPM 7483, denoteGraph_ringAttn pm initPM 7484] := by
    have hv := h4710.2.2
    rw [reconstructForGoal_of_not_replicated intermediateGoal_4710 pm.numRanks _ rfl] at hv
    simp only [intermediateGoal_4710, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by have hs := h4710.2.1
          simp only [intermediateGoal_4710, List.map, List.cons.injEq, and_true] at hs
          rw [hs.1]; decide)] at hv
    exact hv
  have hbrW13_ring := veq_weight_dual_ring initSM initPM hInit initGoal_4712
    (by native_decide) 4712 7487 7488 [32, 1024, 1024] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hbrW2_ring := veq_weight_dual_ring initSM initPM hInit initGoal_4713
    (by native_decide) 4713 7489 7490 [32, 1024, 512] rfl rfl rfl rfl rfl (by decide)
    (by native_decide) (by native_decide) (by native_decide)

  have hbrIn : denoteGraphDistributed sm initSM 7419 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributed pm initPM 11941, denoteGraphDistributed pm initPM 11942] := by
    rw [deq7419, deq11941, deq11942]; exact hbrIn_ring
  have hbrRp : denoteGraphDistributed sm initSM 4709 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributed pm initPM 7481, denoteGraphDistributed pm initPM 7482] := by
    rw [deq4709, deq7481, deq7482]; exact hbrRp_ring
  have hbrRm : denoteGraphDistributed sm initSM 4710 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributed pm initPM 7483, denoteGraphDistributed pm initPM 7484] := by
    rw [deq4710, deq7483, deq7484]; exact hbrRm_ring
  have hbrW13 : denoteGraphDistributed sm initSM 4712 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributed pm initPM 7487, denoteGraphDistributed pm initPM 7488] := by
    rw [deq4712, deq7487, deq7488]; exact hbrW13_ring
  have hbrW2 : denoteGraphDistributed sm initSM 4713 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributed pm initPM 7489, denoteGraphDistributed pm initPM 7490] := by
    rw [deq4713, deq7489, deq7490]; exact hbrW2_ring

  -- Shape facts, transported from the unchanged pre-MoE prefix.
  have hsInA : (denoteGraphDistributed pm initPM 11941).shape = [2048, 1024] := by
    rw [deq11941]; exact hsInA_ring
  have hsInB : (denoteGraphDistributed pm initPM 11942).shape = [2048, 1024] := by
    rw [deq11942]; exact hsInB_ring
  have hsRpA : (denoteGraphDistributed pm initPM 7481).shape = [2048, 64] := by
    rw [deq7481]; have hs := h4709.2.1
    simp only [intermediateGoal_4709, List.map, List.cons.injEq, and_true] at hs; exact hs.1
  have hsRpB : (denoteGraphDistributed pm initPM 7482).shape = [2048, 64] := by
    rw [deq7482]; have hs := h4709.2.1
    simp only [intermediateGoal_4709, List.map, List.cons.injEq, and_true] at hs; exact hs.2
  have hsRmA : (denoteGraphDistributed pm initPM 7483).shape = [2048, 64] := by
    rw [deq7483]; have hs := h4710.2.1
    simp only [intermediateGoal_4710, List.map, List.cons.injEq, and_true] at hs; exact hs.1
  have hsRmB : (denoteGraphDistributed pm initPM 7484).shape = [2048, 64] := by
    rw [deq7484]; have hs := h4710.2.1
    simp only [intermediateGoal_4710, List.map, List.cons.injEq, and_true] at hs; exact hs.2
  have hpres := initGoals_preserved initSM initPM hInit
  have hsW13A : (denoteGraphDistributed pm initPM 7487).shape = [32, 1024, 1024] := by
    rw [deq7487]; have h := hpres initGoal_4712 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4712, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7487 (by native_decide)]; exact hs.1
  have hsW13B : (denoteGraphDistributed pm initPM 7488).shape = [32, 1024, 1024] := by
    rw [deq7488]; have h := hpres initGoal_4712 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4712, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7488 (by native_decide)]; exact hs.2
  have hsW2A : (denoteGraphDistributed pm initPM 7489).shape = [32, 1024, 512] := by
    rw [deq7489]; have h := hpres initGoal_4713 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4713, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7489 (by native_decide)]; exact hs.1
  have hsW2B : (denoteGraphDistributed pm initPM 7490).shape = [32, 1024, 512] := by
    rw [deq7490]; have h := hpres initGoal_4713 (by native_decide); unfold InitGoalHolds at h
    have hs := h.2.1; simp only [initGoal_4713, List.map, List.cons.injEq, and_true] at hs
    rw [pm_ring_eq initPM 7490 (by native_decide)]; exact hs.2

  have hSMout := layer0_sm_moe_value initSM
  have hP0 := layer0_pm_moe0_value initPM
  have hP1 := layer0_pm_moe1_value initPM
  have hPT := layer0_pm_gather_value initPM

  -- Collapse the SM singleton gathers, replace its full weights by the two PM
  -- shards, then apply the already-proved full-expert split commute exactly once.
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4712] =
      denoteGraphDistributed sm initSM 4712 := by
    have hshape : (denoteGraphDistributed sm initSM 4712).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hshape]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4713] =
      denoteGraphDistributed sm initSM 4713 := by
    have hshape : (denoteGraphDistributed sm initSM 4713).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hshape]; decide)
  have hSMfull : denoteGraphDistributed sm initSM 4714 =
      fw_all2all_moe_gmm_full
        (denoteGraphDistributed sm initSM 7419) (denoteGraphDistributed sm initSM 4709)
        (denoteGraphDistributed sm initSM 4710)
        [denoteGraphDistributed pm initPM 7487, denoteGraphDistributed pm initPM 7488]
        [denoteGraphDistributed pm initPM 7489, denoteGraphDistributed pm initPM 7490]
        64 8 (((10 : Nat) : Scalar)) := by
    rw [hSMout]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]

  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 11941) (denoteGraphDistributed pm initPM 11942)
    (denoteGraphDistributed pm initPM 7481) (denoteGraphDistributed pm initPM 7482)
    (denoteGraphDistributed pm initPM 7483) (denoteGraphDistributed pm initPM 7484)
    (denoteGraphDistributed pm initPM 7487) (denoteGraphDistributed pm initPM 7488)
    (denoteGraphDistributed pm initPM 7489) (denoteGraphDistributed pm initPM 7490)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by norm_num)
    hsInA hsInB hsRpA hsRpB hsRmA hsRmB hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 4714 = denoteGraphDistributed pm initPM 4714 := by
    rw [hSMfull, hbrIn, hbrRp, hbrRm, hc, ← hP0, ← hP1, ← hPT]
  have hSMshape : (denoteGraphDistributed sm initSM 4714).shape = [4096, 1024] := by
    rw [hSMfull]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed sm initSM 7419)
      (rp := denoteGraphDistributed sm initSM 4709)
      (rm := denoteGraphDistributed sm initSM 4710)
      (w13s := [denoteGraphDistributed pm initPM 7487,
        denoteGraphDistributed pm initPM 7488])
      (w2s := [denoteGraphDistributed pm initPM 7489,
        denoteGraphDistributed pm initPM 7490])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 4096) (hModel := 1024)
      (by rw [hbrIn, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsInA])]
          simp [List.set])
      (by rw [hbrIn, allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsInA])]
          simp [List.set])
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4714 4714 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hSMshape

#print axioms recon_intermediateGoal_4714_distributed

end TrainVerify.Denote.GeneratedPatterns
