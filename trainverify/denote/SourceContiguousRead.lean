import denote.SourceValueRead

/-!
Read an ordinary source FW_contiguous in the SAME final Store returned by the
original successful runWithInputs. The exact node has one input, one output,
and empty parameters; its request is explicitly global. The original request
split retains the complete checked evaluator and source order.

Input nonwrites cover the selected node AND its entire suffix. Schedule output
uniqueness supplies output nonoverwrite. Selected-step success and read
extensionality are discharged internally, without shape or value premises.
This uses Denote's existing contiguous identity semantics: tensor value equality,
not a claim about physical storage, strides, allocation, or aliasing in PyTorch.
-/
namespace TrainVerify.Denote.SourceContiguousRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Read contiguous's identity value from the original final Store, without
caller-supplied output values, shape facts, or output nonoverwrite premises. -/
theorem contiguous_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_contiguous", ins := [input], outs := [output], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = t input := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input] (fun a => a input) s t hsplit
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
        (by change "OpName.FW_contiguous" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_contiguous" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_contiguous_out_g21 g a rank input output
  · intro a b hab
    exact hab input List.mem_cons_self
  · exact hrun

#print axioms contiguous_value_of_split
end
end TrainVerify.Denote.SourceContiguousRead
