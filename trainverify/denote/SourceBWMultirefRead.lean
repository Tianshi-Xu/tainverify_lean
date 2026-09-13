import denote.SourceValueRead

/-!
Original source `BW_multiref` is an ordered gradient `tensorSum`, not the
forward multiref identity. Inputs are an arbitrary list: this transport neither
sorts nor deduplicates contributions, nor invents rank/ID arithmetic. A source
binding can separately restrict the multiplicity of the original operation.

The successful original run supplies output freshness. Input nonwrites include
the selected node and the complete suffix, so BOTH sides read the SAME final
Store. No output equation, alternate run, or extra semantic axiom is assumed.
-/
namespace TrainVerify.Denote.SourceBWMultirefRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Read the ordered, arbitrary-length backward contribution sum from the
original successful run's final Store. -/
theorem bw_multiref_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (inputs : List Tid) (out : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_multiref", ins := inputs,
        outs := [out], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinputs : ∀ tid ∈ inputs, ∀ row ∈ (sourceNode, none) :: after, tid ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t out = tensorSum (inputs.map t) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode out inputs (fun a => tensorSum (inputs.map a)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · exact hinputs
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_multiref" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_multiref" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_multiref_out g a rank inputs out
  · intro a b hab
    apply congrArg tensorSum
    exact List.map_congr_left hab
  · exact hrun

#print axioms bw_multiref_value_of_split
end
end TrainVerify.Denote.SourceBWMultirefRead
