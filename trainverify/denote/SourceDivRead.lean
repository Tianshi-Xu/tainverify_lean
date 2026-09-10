import denote.SourceValueRead

/-!
Read an ordinary source FW_div in the SAME final Store returned by the
original successful runWithInputs. The exact source node has one input,
one output, the original singleton Nat parameter [c], and an explicit global
request. The original request split retains the complete checked evaluator
and source order.

Input nonwrites cover the selected node and its entire suffix. Schedule
output uniqueness supplies output nonoverwrite. This theorem uses the
existing Denote Nat-to-Scalar parameter path, not arbitrary floating-point
source division, and requires no shape, value, or nonzero-denominator premise.
-/
namespace TrainVerify.Denote.SourceDivRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The original successful run determines the final division value. The
ordinary success law and read extensionality are discharged internally. -/
theorem div_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank c : Nat) (input output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_div", ins := [input],
        outs := [output], params := [c] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = fw_div (c : Scalar) (t input) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input] (fun a => fw_div (c : Scalar) (a input)) s t hsplit
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
        (by change "OpName.FW_div" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_div" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_div_out_g92 g a rank c input output
  · intro a b hab
    rw [hab input List.mem_cons_self]
  · exact hrun

#print axioms div_value_of_split
end
end TrainVerify.Denote.SourceDivRead
