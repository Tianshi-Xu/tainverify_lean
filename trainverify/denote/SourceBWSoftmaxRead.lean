import denote.SourceValueRead

/-! Original BW_softmax reads saved INPUT logits, recomputing softmax internally.
This conditional read preserves both operands in the same successful final Store.
Source authority validates last-axis/dtype before invoking this Denote law. -/
namespace TrainVerify.Denote.SourceBWSoftmaxRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

theorem bw_softmax_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank grad saved dx : Nat) (params : List Nat) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_softmax", ins := [grad,saved], outs := [dx], params := params })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hsaved : ∀ row ∈ (sourceNode, none) :: after, saved ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = bw_softmax (t grad) (t saved) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad,saved] (fun a => bw_softmax (a grad) (a saved)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · have heq := List.mem_singleton.mp htid
      subst tid
      exact hsaved
  · intro a b hstep
    have hs : stepWithInputs g (scope sourceNode) (peer sourceNode) a sourceNode none =
        some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_softmax" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _ (by change ordinary "OpName.BW_softmax" = true; decide)
    have hb := Option.some.inj (hs.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_softmax_out_g234 g a rank grad saved dx params
  · intro a b hab
    rw [hab grad List.mem_cons_self, hab saved (List.mem_cons_of_mem grad List.mem_cons_self)]
  · exact hrun

#print axioms bw_softmax_value_of_split
end
end TrainVerify.Denote.SourceBWSoftmaxRead
