import denote.SourceValueRead

/-!
Read an ordinary source FW_linear in the SAME final Store returned by the
original successful runWithInputs. The exact source node has two input ports,
one output, empty params, and an explicit global request. The original request
split retains the complete checked evaluator and source order.

Nonwrites for input and weight cover both the selected node and its entire
suffix. Schedule output uniqueness supplies output nonoverwrite. This theorem
uses the existing Denote FW_linear semantics without additional shape or value
hypotheses.
-/
namespace TrainVerify.Denote.SourceLinearRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The original successful run determines the final linear value. The
ordinary success law and read extensionality are discharged internally. -/
theorem linear_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input weight output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_linear", ins := [input, weight],
        outs := [output], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hweight : ∀ row ∈ (sourceNode, none) :: after, weight ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = fw_linear (t input) (t weight) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input, weight]
    (fun a => fw_linear (a input) (a weight)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hinput
    · have heq : tid = weight := List.mem_singleton.mp htid
      subst tid
      exact hweight
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.FW_linear" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_linear" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_linear_out g a rank input weight output
  · intro a b hab
    rw [hab input List.mem_cons_self,
      hab weight (List.mem_cons_of_mem input List.mem_cons_self)]
  · exact hrun

#print axioms linear_value_of_split
end
end TrainVerify.Denote.SourceLinearRead
