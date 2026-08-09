import denote.yoco_goals.Goal_1
import denote.yoco_goals.CanonicalKVCacheOrdinaryOps
import denote.ChunkGatherDim0
import denote.MultirefGeneral
import denote.GraphGears
import denote.Gather2Rel

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l11o_node_core (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (outTid : Tid)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      applyNodeRingAttn g ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid := by
  rw [denoteGraphDistributed_eq_prefix g init outTid (k + 1) hdrop_nil hdrop]
  have hstep := congrFun (foldl_take_succ (applyNodeDistributed g) g.nodes init k hk) outTid
  rw [hstep, hnode]
  unfold applyNodeDistributed
  rw [if_neg hmoe]

private theorem l11o_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributed g) init) tid =
      denoteGraphDistributed g init tid :=
  (denoteGraphDistributed_eq_prefix g init tid k hpre_nil hpre).symm

private theorem l11o_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeRingAttn g s node outTid = opfun (s inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraphDistributed g init outTid = opfun (denoteGraphDistributed g init inTid) := by
  rw [l11o_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, l11o_prefix_read g init k inTid hpre_nil hpre]

private theorem l11o_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
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
  rw [l11o_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, l11o_prefix_read g init k in1 hpre_nil hpre1,
    l11o_prefix_read g init k in2 hpre_nil hpre2]

private theorem l11o_init_value (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid)
    (htp : gW.tps = [{ rank := 0, tid := W }]) (hgd : gW.gatherDim = 0)
    (hrep : gW.replicated = false) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm.nodes, W ∉ n.outs) (hpm : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    denoteGraphDistributed sm initSM W = denoteGraphDistributed pm initPM W := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  have hv := hg.2.2
  rw [reconstructForGoal_of_not_replicated gW pm.numRanks _ hrep, htp, hts, hgd] at hv
  simp only [List.map, reconstructWithDim] at hv
  rw [denoteGraphDistributed,
    foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM W (by native_decide) hsm,
    denoteGraphDistributed,
    foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM W (by native_decide) hpm]
  exact hv

private theorem l11o_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid) (sh : Shape)
    (htsShape : gW.tsShape = sh) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm.nodes, W ∉ n.outs) :
    (denoteGraphDistributed sm initSM W).shape = sh := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  rw [denoteGraphDistributed,
    foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM W (by native_decide) hsm]
  rw [← hts, ← htsShape]
  exact hg.1

private theorem l11o_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_rms_norm", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_rms_norm (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  l11o_reduce2 g init k _ x w o fw_rms_norm hk hn (by simp)
    (fun st => applyNode_fw_rms_norm_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l11o_apply_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs, params := [n] }
      outTid = s xTid := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

private theorem l11o_apply_per_head (g : GraphDecl) (s : Store) (rank x w o : Nat) :
    applyNodeRingAttn g s
      { rank := rank, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [x, w], outs := [o] } o = fw_per_head_linear (s x) (s w) := by
  rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s _ (by simp) (by simp)]
  unfold applyNode
  rw [show ([x, w] : List Tid).map s = [s x, s w] from rfl,
    show evalOp g.numRanks rank "OpName.FW_per_head_mix_precision_linear" [] [s x, s w] =
      [fw_per_head_linear (s x) (s w)] from rfl]
  change storeSet s [(o, fw_per_head_linear (s x) (s w))] o = _
  unfold storeSet
  simp [List.find?]

private theorem l11o_per_head (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_per_head_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  l11o_reduce2 g init k _ x w o fw_per_head_linear hk hn (by simp)
    (fun st => l11o_apply_per_head g st r x w o)
    hdn hdw hpn hpx hpw

private theorem l11o_per_head_shape (x w : Tensor) (b k hW dW : Nat)
    (hx : x.shape = [b, k]) (hw : w.shape = [hW, dW, k]) :
    (fw_per_head_linear x w).shape = [b, hW, dW] := by
  unfold fw_per_head_linear
  rw [hx, hw]
  rfl

/-- L11 ordinary V relation, derived only from the preceding output boundary and init weights. -/
theorem l11o_v5548_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributed sm initSM 5540)
      (denoteGraphDistributed pm initPM 9558) (denoteGraphDistributed pm initPM 9559)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5548)
      (denoteGraphDistributed pm initPM 9586) (denoteGraphDistributed pm initPM 9587)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l11o_reduce1 sm initSM 431
    { rank := 0, op := "OpName.FW_multiref", ins := [5540], outs := [8316, 8320], params := [2] }
    5540 8316 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5540 [8316, 8320] 2 rfl 8316 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11o_reduce1 pm initPM 956
    { rank := 0, op := "OpName.FW_multiref", ins := [9558], outs := [15790, 15794], params := [2] }
    9558 15790 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9558 [15790, 15794] 2 rfl 15790 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11o_reduce1 pm initPM 957
    { rank := 1, op := "OpName.FW_multiref", ins := [9559], outs := [15798, 15802], params := [2] }
    9559 15798 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9559 [15798, 15802] 2 rfl 15798 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l11o_init_value initSM initPM hInit initGoal_5541
    (by native_decide) 5541 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l11o_rms sm initSM 432 0 8316 5541 5542
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11o_rms pm initPM 958 0 15790 5541 9562
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11o_rms pm initPM 959 1 15798 5541 9563
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributed sm initSM 5542)
      (denoteGraphDistributed pm initPM 9562) (denoteGraphDistributed pm initPM 9563)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l11o_reduce1 sm initSM 433
    { rank := 0, op := "OpName.FW_multiref", ins := [5542], outs := [8325, 8329, 8333], params := [3] }
    5542 8333 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5542 [8325, 8329, 8333] 3 rfl 8333 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l11o_reduce1 pm initPM 960
    { rank := 0, op := "OpName.FW_multiref", ins := [9562], outs := [15380, 13744, 13752], params := [3] }
    9562 13752 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9562 [15380, 13744, 13752] 3 rfl 13752 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l11o_reduce1 pm initPM 961
    { rank := 1, op := "OpName.FW_multiref", ins := [9563], outs := [15382, 13745, 13753], params := [3] }
    9563 13753 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9563 [15382, 13745, 13753] 3 rfl 13753 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l11o_init_value initSM initPM hInit initGoal_5547
    (by native_decide) 5547 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l11o_init_shape initSM initPM hInit initGoal_5547
    (by native_decide) 5547 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5547).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l11o_per_head sm initSM 436 0 8333 5547 5548
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l11o_per_head pm initPM 963 0 13752 5547 9586
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l11o_per_head pm initPM 966 1 13753 5547 9587
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 13752).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 13753).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

end TrainVerify.Denote.GeneratedPatterns
