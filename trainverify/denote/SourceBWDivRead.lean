import denote.SourceValueRead

/-! Original scalar-constant BW_div: saved input is authenticated by the source
binder but its values do not enter G/c. The binder rejects unsupported scalar
encodings/rounding modes; this lemma states the exact Denote final-Store read. -/
namespace TrainVerify.Denote.SourceBWDivRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

theorem bw_div_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank grad saved dx divisor : Nat) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_div", ins := [grad,saved], outs := [dx], params := [divisor] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = bw_div (divisor : Scalar) (t grad) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad] (fun a => bw_div (divisor : Scalar) (a grad)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    have heq := List.mem_singleton.mp htid
    subst tid
    exact hgrad
  · intro a b hstep
    have hs : stepWithInputs g (scope sourceNode) (peer sourceNode) a sourceNode none =
        some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_div" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _ (by change ordinary "OpName.BW_div" = true; decide)
    have hb := Option.some.inj (hs.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_div_out_g128 g a rank divisor grad saved dx
  · intro a b hab
    rw [hab grad List.mem_cons_self]
  · exact hrun

#print axioms bw_div_value_of_split
end
end TrainVerify.Denote.SourceBWDivRead
