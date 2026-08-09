/- Small reusable gears for sliding a 1TP/2TP boundary through a distributed graph. -/
import denote.yoco_goals.Layer0DistributedMigration
import denote.Gather2Rel
import denote.MoEFullSplitCommute

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- Unpack the standard non-replicated, dim-0, two-rank goal into `Gather2Rel`. -/
theorem Gather2Rel.of_initGoalHolds
    (fullStore shardStore : Store) (goal : LineageGoal)
    (fullTid shardTid0 shardTid1 : Tid) (fullShape shardShape : Shape)
    (hts : goal.ts = fullTid)
    (htps : goal.tps = [{ rank := 0, tid := shardTid0 }, { rank := 1, tid := shardTid1 }])
    (htsShape : goal.tsShape = fullShape)
    (htpShapes : goal.tpShapes = [shardShape, shardShape])
    (hgather : goal.gatherDim = 0) (hrep : goal.replicated = false)
    (hnonscalar : shardShape ≠ [1])
    (h : InitGoalHolds 2 goal fullStore shardStore) :
    Gather2Rel (fullStore fullTid) (shardStore shardTid0) (shardStore shardTid1)
      fullShape shardShape := by
  unfold InitGoalHolds at h
  refine ⟨?_, ?_, ?_, ?_, hnonscalar⟩
  · have hv := h.2.2
    rw [reconstructForGoal_of_not_replicated goal 2 _ hrep,
      htps, hts, hgather] at hv
    simp only [List.map, reconstructWithDim, List.head?, Option.map, Option.getD] at hv
    have hshape0 : (shardStore shardTid0).shape = shardShape := by
      have hs := h.2.1
      rw [htps, htpShapes] at hs
      simp only [List.map, List.cons.injEq] at hs
      exact hs.1
    have hne0 : (shardStore shardTid0).shape ≠ [1] := by
      rw [hshape0]
      exact hnonscalar
    rw [if_neg hne0] at hv
    exact hv
  · rw [← hts, ← htsShape]
    exact h.1
  · have hs := h.2.1
    rw [htps, htpShapes] at hs
    simp only [List.map, List.cons.injEq] at hs
    exact hs.1
  · have hs := h.2.1
    rw [htps, htpShapes] at hs
    simp only [List.map, List.cons.injEq] at hs
    exact hs.2.1

/-- Pack `Gather2Rel` back into the standard two-rank `InitGoalHolds` pattern. -/
theorem Gather2Rel.to_initGoalHolds
    (fullStore shardStore : Store) (goal : LineageGoal)
    (fullTid shardTid0 shardTid1 : Tid) (fullShape shardShape : Shape)
    (hts : goal.ts = fullTid)
    (htps : goal.tps = [{ rank := 0, tid := shardTid0 }, { rank := 1, tid := shardTid1 }])
    (htsShape : goal.tsShape = fullShape)
    (htpShapes : goal.tpShapes = [shardShape, shardShape])
    (hgather : goal.gatherDim = 0) (hrep : goal.replicated = false)
    (h : Gather2Rel (fullStore fullTid) (shardStore shardTid0) (shardStore shardTid1)
      fullShape shardShape) :
    InitGoalHolds 2 goal fullStore shardStore := by
  unfold InitGoalHolds
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]
    exact h.full_shape
  · rw [htps, htpShapes]
    simp only [List.map, List.cons.injEq]
    exact ⟨h.shard0_shape, h.shard1_shape, True.intro⟩
  · rw [reconstructForGoal_of_not_replicated goal 2 _ hrep,
      htps, hts, hgather]
    simp only [List.map, reconstructWithDim, List.head?, Option.map, Option.getD]
    rw [h.shard0_shape, if_neg h.nonscalar]
    exact h.value

/-- Fixed-arity distributed-node reduction.  The operator consumes the input
    values in `inTids` order.  Unlike the old arity-specific reducers, `happly`
    only has to establish the equation at the concrete prefix store. -/
theorem distributed_reduce_fixed (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTids : List Tid) (outTid : Tid)
    (opfun : List Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : applyNodeRingAttn g
      ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid =
      opfun (inTids.map ((g.nodes.take k).foldl (applyNodeDistributed g) init)))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ tid ∈ inTids, ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      opfun (inTids.map (denoteGraphDistributed g init)) := by
  have hstep := congrFun (foldl_take_succ (applyNodeDistributed g) g.nodes init k hk) outTid
  conv_lhs => rw [denoteGraphDistributed]
  rw [foldl_prefix_distributed g g.nodes init outTid (k + 1) hdrop_nil hdrop,
    hstep, hnode, applyNodeDistributed_eq_ring_of_not_moe g _ node hmoe, happly]
  congr 1
  apply List.map_congr_left
  intro tid htid
  exact foldl_take_distributed_eq g init tid k hpre_nil (hpre tid htid)

/-- Arity-one specialization, demonstrating that the generic reducer has the
    same convenient result shape as `distributed_reduce1`. -/
theorem distributed_reduce_fixed_one (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : applyNodeRingAttn g
      ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid =
      opfun (((g.nodes.take k).foldl (applyNodeDistributed g) init) inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraphDistributed g init outTid = opfun (denoteGraphDistributed g init inTid) := by
  have h := distributed_reduce_fixed g init k node [inTid] outTid
    (fun xs => opfun (xs.getD 0 (zeroTensor []))) hk hnode hmoe happly
    hdrop_nil hdrop hpre_nil (by
      intro tid ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rw [ht]
      exact hpre)
  exact h

/-- Arity-two specialization; together with `distributed_reduce_fixed_one`
    this recovers both old reducers from one list-arity theorem. -/
theorem distributed_reduce_fixed_two (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in1 in2 outTid : Tid) (opfun : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : applyNodeRingAttn g
      ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid =
      opfun (((g.nodes.take k).foldl (applyNodeDistributed g) init) in1)
        (((g.nodes.take k).foldl (applyNodeDistributed g) init) in2))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs) :
    denoteGraphDistributed g init outTid =
      opfun (denoteGraphDistributed g init in1) (denoteGraphDistributed g init in2) := by
  have h := distributed_reduce_fixed g init k node [in1, in2] outTid
    (fun xs => opfun (xs.getD 0 (zeroTensor [])) (xs.getD 1 (zeroTensor [])))
    hk hnode hmoe happly hdrop_nil hdrop hpre_nil (by
      intro tid ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hpre1
      · exact hpre2)
  exact h

/-- A non-vacuous witness for the relation itself. -/
theorem gather2Rel_witness (a b : Tensor) (sh : Shape)
    (ha : a.shape = sh) (hb : b.shape = sh) (hne : sh ≠ [1]) :
    Gather2Rel (allGatherPrimDimN 0 2 0 [a, b]) a b
      (allGatherPrimDimN 0 2 0 [a, b]).shape sh := by
  exact ⟨rfl, rfl, ha, hb, hne⟩


end TrainVerify.Denote.GeneratedPatterns
