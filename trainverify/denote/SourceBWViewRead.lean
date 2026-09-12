import denote.SourceValueRead

/-!
Original BW_view read. The authenticated nonempty params are the FW input shape,
not the original FW output-size kwargs. The unchanged evaluator uses those params
and G; it ignores savedX values. This theorem supplies no saved-value premise and
makes no assertion equating shape metadata with runtime tensor values.
-/
namespace TrainVerify.Denote.SourceBWViewRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

theorem bw_view_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank hd : Nat) (tl : List Nat) (grad savedX dx : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_view", ins := [grad, savedX],
        outs := [dx], params := hd :: tl })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hsaved : ∀ row ∈ (sourceNode, none) :: after, savedX ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = fw_view (hd :: tl) (t grad) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad, savedX]
    (fun a => fw_view (hd :: tl) (a grad)) s t hsplit
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
        (by change "OpName.BW_view" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_view" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_view_out g a rank hd tl grad savedX dx
  · intro a b hab
    rw [hab grad List.mem_cons_self]
  · exact hrun

#print axioms bw_view_value_of_split
end
end TrainVerify.Denote.SourceBWViewRead
