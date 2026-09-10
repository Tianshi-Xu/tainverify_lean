import denote.SourceValueRead

/-!
Read an ordinary source FW_softmax in the SAME final Store returned by the
original successful runWithInputs. The exact source node has one input,
one output, empty parameters, and an explicit global request. The original
request split retains the complete checked evaluator and source order.

Input nonwrites cover the selected node and its entire suffix. Schedule
output uniqueness supplies output nonoverwrite. This is a value read for
existing Denote semantics, with no shape, value, axis, or dtype premises;
last-axis/dtype admission of original IR sources is a separate obligation.
-/
namespace TrainVerify.Denote.SourceSoftmaxRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The original successful run determines the final softmax value. The
ordinary success law and read extensionality are discharged internally. -/
theorem softmax_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_softmax", ins := [input],
        outs := [output], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = fw_softmax (t input) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input] (fun a => fw_softmax (a input)) s t hsplit
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
        (by change "OpName.FW_softmax" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_softmax" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_softmax_out_g43 g a rank input output []
  · intro a b hab
    rw [hab input List.mem_cons_self]
  · exact hrun

#print axioms softmax_value_of_split
end
end TrainVerify.Denote.SourceSoftmaxRead
