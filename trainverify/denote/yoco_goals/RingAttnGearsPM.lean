/- Worker #22 — PM-side whnf-safe ring node reduction gears.

   `RingAttnGears.ringAttn_reduce1`/`ringAttn_reduce2` close their goal with
   `congr 1; exact (foldl_prefix_ring_g12 …).symm`.  At a HIGH pm-graph node
   index (e.g. the rank-1 3-way `FW_multiref` at pm node 129) the `congr 1`
   tactic tries `isDefEq` on `opfun ((nodes.take k).foldl …) =?= opfun (nodes.foldl …)`,
   which forces whnf of the entire `k`-deep `applyNodeRingAttn` fold (including
   the sliding-window / zigzag ring branches) and blows up the elaborator.

   The variants below replace the terminal `congr 1` with an explicit,
   PURELY SYNTACTIC rewrite: they unfold the RHS `denoteGraph_ringAttn` and
   rewrite `nodes.foldl … inTid` into `(nodes.take k).foldl … inTid` with the
   very same `foldl_prefix_ring_g12` lemma, so both sides become the identical
   prefix-fold term and the goal closes by `rfl` — WITHOUT ever asking the
   kernel to reduce the fold.  Signatures are identical to the originals so
   call sites transfer verbatim.

   `ringAttn_node_core_pm_opaque` exposes the underlying opaque core
   (`outTid`-value = `applyNode` on the prefix store) for multi-input /
   multi-output nodes such as `FW_rotary_embedding`. -/
import denote.yoco_goals.RingAttnGears

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

/-- **Opaque node core (whnf-safe).**  For a non-ring node at position `k`
    whose output `outTid` is never rewritten by the suffix, the ring-denotation
    value at `outTid` equals `applyNode` of the node on the length-`k` PREFIX
    fold.  Only the LHS is manipulated (unfold + prefix-collapse + node-swap),
    so no full-fold `isDefEq` is triggered.  Downstream callers finish by
    rewriting each input read `((nodes.take k).foldl … inᵢ)` back to
    `denoteGraph_ringAttn g init inᵢ` via `foldl_prefix_ring_g12`. -/
theorem ringAttn_node_core_pm_opaque (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (outTid : Tid)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node)
    (hnr1 : node.op ≠ "OpName.FW_attn_zigzag")
    (hnr2 : node.op ≠ "OpName.FW_attn_sliding_window")
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraph_ringAttn g init outTid
      = applyNode g ((g.nodes.take k).foldl (applyNodeRingAttn g) init) node outTid := by
  have hstep := congrFun (foldl_take_succ (applyNodeRingAttn g) g.nodes init k hk) outTid
  conv_lhs => rw [denoteGraph_ringAttn]
  rw [foldl_prefix_ring_g12 g g.nodes init outTid (k + 1) hdrop_nil hdrop, hstep, hnode,
      applyNodeRingAttn_eq_applyNode_of_not_ring g _ _ hnr1 hnr2]

/-- Prefix read = full ring-denotation read, for a tid unwritten by the suffix
    `drop k`.  (`foldl_prefix_ring_g12` oriented for post-core rewriting.) -/
theorem ringAttn_prefix_read_pm (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeRingAttn g) init) tid
      = denoteGraph_ringAttn g init tid := by
  rw [denoteGraph_ringAttn]
  exact (foldl_prefix_ring_g12 g g.nodes init tid k hpre_nil hpre).symm

/-- **Whnf-safe single-input single-output ring reduction.**  Drop-in for
    `RingAttnGears.ringAttn_reduce1` (identical signature) that dodges the
    high-index `congr 1` whnf blowup. -/
theorem ringAttn_reduce1_pm_opaque (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node)
    (hnr1 : node.op ≠ "OpName.FW_attn_zigzag")
    (hnr2 : node.op ≠ "OpName.FW_attn_sliding_window")
    (happly : ∀ (s : Store), applyNode g s node outTid = opfun (s inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph_ringAttn g init outTid = opfun (denoteGraph_ringAttn g init inTid) := by
  rw [ringAttn_node_core_pm_opaque g init k node outTid hk hnode hnr1 hnr2 hdrop_nil hdrop,
      happly, ringAttn_prefix_read_pm g init k inTid hpre_nil hpre]

/-- **Whnf-safe two-input single-output ring reduction.**  Drop-in for
    `RingAttnGears.ringAttn_reduce2`. -/
theorem ringAttn_reduce2_pm_opaque (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in1 in2 outTid : Tid) (opfun : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node)
    (hnr1 : node.op ≠ "OpName.FW_attn_zigzag")
    (hnr2 : node.op ≠ "OpName.FW_attn_sliding_window")
    (happly : ∀ (s : Store), applyNode g s node outTid = opfun (s in1) (s in2))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs) :
    denoteGraph_ringAttn g init outTid
      = opfun (denoteGraph_ringAttn g init in1) (denoteGraph_ringAttn g init in2) := by
  rw [ringAttn_node_core_pm_opaque g init k node outTid hk hnode hnr1 hnr2 hdrop_nil hdrop,
      happly, ringAttn_prefix_read_pm g init k in1 hpre_nil hpre1,
      ringAttn_prefix_read_pm g init k in2 hpre_nil hpre2]

/-- Output shape of `fw_per_head_linear` for a 2-D activation `x : [b, k]` and a
    3-D per-head weight `w : [hW, dW, k]`: the result is `[b, hW, dW]`.  Pure
    shape reduction (no value reasoning). -/
theorem fw_per_head_linear_shape_3d (x w : Tensor) (b k hW dW : Nat)
    (hx : x.shape = [b, k]) (hw : w.shape = [hW, dW, k]) :
    (fw_per_head_linear x w).shape = [b, hW, dW] := by
  unfold fw_per_head_linear
  rw [hx, hw]
  rfl

end TrainVerify.Denote.GeneratedPatterns
