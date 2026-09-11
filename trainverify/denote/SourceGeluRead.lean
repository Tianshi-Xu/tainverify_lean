import denote.SourceValueRead

/-!
Read exact GELU from the final Store of the original successful input-scheduled
run. The node has one input/output and empty parameters, with a global request.
The source boundary must authenticate the `approximate = none` variant; this
lemma uses the existing exact-erf `fw_gelu`, not a tanh or floating-point model.
Input nonwrites include the selected node and the complete suffix. No output
value, shape, alternate evaluator, or caller-supplied step-success premise.
-/
namespace TrainVerify.Denote.SourceGeluRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

theorem gelu_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_gelu", ins := [input], outs := [output], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = fw_gelu (t input) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input] (fun a => fw_gelu (a input)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    have heq : tid = input := List.mem_singleton.mp htid
    subst tid
    exact hinput
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.FW_gelu" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_gelu" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_gelu_out g a rank input output
  · intro a b hab
    exact congrArg fw_gelu (hab input List.mem_cons_self)
  · exact hrun

#print axioms TrainVerify.Denote.SourceGeluRead.gelu_value_of_split
end
end TrainVerify.Denote.SourceGeluRead
