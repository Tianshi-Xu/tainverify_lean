import denote.SourceValueRead

/-! Original [G,saved FW input] transpose read over the same successful run.
The two natural parameters are authenticated normalized Torch axes. Saved input
is retained in the complete nonwrite premise, but its values are not assumed to
be the derivative. This local theorem is not whole-model/Torch refinement. -/
namespace TrainVerify.Denote.SourceBWTransposeRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

theorem bw_transpose_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank d0 d1 : Nat) (grad savedX dx : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_transpose", ins := [grad, savedX],
        outs := [dx], params := [d0, d1] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hsaved : ∀ row ∈ (sourceNode, none) :: after, savedX ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = transposeAxes d0 d1 (t grad) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad, savedX]
    (fun a => transposeAxes d0 d1 (a grad)) s t hsplit
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
        (by change "OpName.BW_transpose" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_transpose" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_transposeAxes_out g a rank grad savedX dx d0 d1
  · intro a b hab
    rw [hab grad List.mem_cons_self]
  · exact hrun

#print axioms bw_transpose_value_of_split
end
end TrainVerify.Denote.SourceBWTransposeRead
