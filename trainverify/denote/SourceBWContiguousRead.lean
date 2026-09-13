import denote.SourceValueRead

/-!
Authenticated original BW_contiguous logical gradient read. The existing evaluator
returns G, not savedX. Both declared input reads retain nonwrite obligations.
Memory layout/allocation is not modeled here; this is not Torch refinement, and
no communication operation is reinterpreted as identity.
-/
namespace TrainVerify.Denote.SourceBWContiguousRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

theorem bw_contiguous_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad savedX dx : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_contiguous", ins := [grad, savedX],
        outs := [dx], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hsaved : ∀ row ∈ (sourceNode, none) :: after, savedX ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = t grad := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad, savedX]
    (fun a => a grad) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · have heq : tid = savedX := List.mem_singleton.mp htid
      subst tid
      exact hsaved
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_contiguous" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_contiguous" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_contiguous_out g a rank grad savedX dx
  · intro a b hab
    rw [hab grad List.mem_cons_self]
  · exact hrun

#print axioms bw_contiguous_value_of_split
end
end TrainVerify.Denote.SourceBWContiguousRead
