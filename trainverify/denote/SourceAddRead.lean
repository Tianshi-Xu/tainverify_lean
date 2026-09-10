import denote.SourceValueRead

/-!
Read a two-port ordinary source FW_add in the SAME final Store returned by the
original successful runWithInputs. The exact request split retains the complete
checked evaluator and source order. Operand nonwrites cover the selected node
and its suffix; schedule output uniqueness supplies output nonoverwrite.

This proves exactly the existing Denote FW_add semantics with empty params and
an explicit global request (no group). Authentication of raw source kwargs,
including alpha, is a separate caller-side obligation, not a refinement claim
made by this library theorem.
-/
namespace TrainVerify.Denote.SourceAddRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The original successful run determines the final addition value. Both the
ordinary step equation and read extensionality are discharged internally. -/
theorem add_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (rank : Nat) (left right out : Tid) (s t : Store)
    (hnode : n =
      { rank := rank, op := "OpName.FW_add", ins := [left, right],
        outs := [out], params := [] })
    (hsplit : requests = before ++ (n, none) :: after)
    (hscope : scope n = .global)
    (hleft : ∀ row ∈ (n, none) :: after, left ∉ row.1.outs)
    (hright : ∀ row ∈ (n, none) :: after, right ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t out = elemwiseAdd (t left) (t right) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after n
    out [left, right] (fun a => elemwiseAdd (a left) (a right)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hleft
    · have heq : tid = right := List.mem_singleton.mp htid
      subst tid
      exact hright
  · intro a b hstep
    have hselected : stepWithInputs g (scope n) (peer n) a n none =
        some (applyNode g a n) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.FW_add" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _ (by change ordinary "OpName.FW_add" = true; decide)
    have hb : applyNode g a n = b := Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_add2_out g a rank left right out
  · intro a b hab
    rw [hab left List.mem_cons_self,
      hab right (List.mem_cons_of_mem left List.mem_cons_self)]
  · exact hrun

#print axioms add_value_of_split
end
end TrainVerify.Denote.SourceAddRead
