import denote.SourceValueRead

/-!
Read an ordinary source FW_matmul in the SAME final Store returned by the
original successful runWithInputs. The exact source node has two input ports
in their original order, one output, empty params, and an explicit global
request. The original request split retains the complete checked evaluator
and source order.

Nonwrites for both operands cover the selected node and its entire suffix.
Schedule output uniqueness supplies output nonoverwrite. This theorem uses
the existing Denote FW_matmul semantics without shape or value hypotheses.
-/
namespace TrainVerify.Denote.SourceMatmulRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The original successful run determines the final matmul value. The
ordinary success law and read extensionality are discharged internally. -/
theorem matmul_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (xTid yTid output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_matmul", ins := [xTid, yTid],
        outs := [output], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hx : ∀ row ∈ (sourceNode, none) :: after, xTid ∉ row.1.outs)
    (hy : ∀ row ∈ (sourceNode, none) :: after, yTid ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = fw_matmul (t xTid) (t yTid) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [xTid, yTid]
    (fun a => fw_matmul (a xTid) (a yTid)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hx
    · have heq : tid = yTid := List.mem_singleton.mp htid
      subst tid
      exact hy
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.FW_matmul" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_matmul" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_matmul_out g a rank xTid yTid output
  · intro a b hab
    rw [hab xTid List.mem_cons_self,
      hab yTid (List.mem_cons_of_mem xTid List.mem_cons_self)]
  · exact hrun

#print axioms matmul_value_of_split
end
end TrainVerify.Denote.SourceMatmulRead
