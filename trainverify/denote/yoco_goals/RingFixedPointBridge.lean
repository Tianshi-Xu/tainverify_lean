import denote.yoco_goals.BridgeKit
import denote.GraphSlicing

set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

/-- A non-ring node is fixed on a ring-aware full-graph final store once all of
its inputs have settled and none of its outputs is overwritten later. -/
theorem node_fixed_on_ring_final (g : GraphDecl) (init : Store) (k : Nat)
    (n : NodeDecl) (hk : k < g.nodes.length) (hn : g.nodes[k] = n)
    (hwf : IsWellFormedNode g n)
    (hNotZigzag : n.op ≠ "OpName.FW_attn_zigzag")
    (hNotSliding : n.op ≠ "OpName.FW_attn_sliding_window")
    (hNonempty : ∀ m ∈ g.nodes, m.outs ≠ [])
    (hIns : ∀ tid ∈ n.ins, ∀ m ∈ g.nodes.drop k, tid ∉ m.outs)
    (hOuts : ∀ tid ∈ n.outs, ∀ m ∈ g.nodes.drop (k + 1), tid ∉ m.outs) :
    applyNode g (denoteGraph_ringAttn g init) n = denoteGraph_ringAttn g init := by
  funext tid
  by_cases hout : tid ∈ n.outs
  · have hval : denoteGraph_ringAttn g init tid =
        applyNode g
          ((g.nodes.take k).foldl (applyNodeRingAttn g) init) n tid := by
      unfold denoteGraph_ringAttn
      calc
        (g.nodes.foldl (applyNodeRingAttn g) init) tid =
            ((g.nodes.take (k + 1) ++ g.nodes.drop (k + 1)).foldl
              (applyNodeRingAttn g) init) tid := by
                rw [List.take_append_drop]
        _ = ((g.nodes.take (k + 1)).foldl (applyNodeRingAttn g) init) tid := by
              rw [List.foldl_append]
              exact foldl_applyNodeRingAttn_at_not_written g _ _ tid
                (fun m hm => hNonempty m (List.mem_of_mem_drop hm)) (hOuts tid hout)
        _ = applyNode g ((g.nodes.take k).foldl (applyNodeRingAttn g) init) n tid := by
              rw [foldl_take_succ (applyNodeRingAttn g) g.nodes init k hk, hn]
              rw [applyNodeRingAttn_eq_applyNode_of_not_ring g _ n hNotZigzag hNotSliding]
    have hagree : applyNode g (denoteGraph_ringAttn g init) n tid =
        applyNode g ((g.nodes.take k).foldl (applyNodeRingAttn g) init) n tid := by
      apply applyNode_at_out_congr_of_ins_agree g n _ _ tid hwf hout
      intro t ht
      unfold denoteGraph_ringAttn
      calc
        (g.nodes.foldl (applyNodeRingAttn g) init) t =
            ((g.nodes.take k ++ g.nodes.drop k).foldl (applyNodeRingAttn g) init) t := by
              rw [List.take_append_drop]
        _ = ((g.nodes.take k).foldl (applyNodeRingAttn g) init) t := by
              rw [List.foldl_append]
              exact foldl_applyNodeRingAttn_at_not_written g _ _ t
                (fun m hm => hNonempty m (List.mem_of_mem_drop hm)) (hIns t ht)
    rw [hagree, ← hval]
  · exact applyNode_eq_of_not_mem_outs g _ n tid hout

/-- A cut consisting of nodes fixed on a store leaves that store unchanged. -/
theorem foldl_applyNode_fixed (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
    (h : ∀ n ∈ nodes, applyNode g s n = s) :
    nodes.foldl (applyNode g) s = s := by
  induction nodes with
  | nil => rfl
  | cons n ns ih =>
      rw [List.foldl_cons, h n (by simp)]
      apply ih
      intro m hm
      exact h m (by simp [hm])

end TrainVerify.Denote.GeneratedPatterns
