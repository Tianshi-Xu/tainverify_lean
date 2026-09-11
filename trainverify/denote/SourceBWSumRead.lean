import denote.SourceValueRead

/-!
Read an ordinary source BW_sum in the SAME final Store returned by the original
successful runWithInputs. The exact source node consumes [seed, savedPrimal],
has one output, empty params, and an explicit global request. The original
request split retains the complete checked evaluator and source order.

Both read-ID nonwrites cover the selected node AND its entire suffix. Output
freshness comes from the checked InputSchedule inside SourceValueRead. The seed
is unrestricted: this is the existing BW_sum broadcast, not a unit-seed law or
a mean reduction with an extra scale. No output-value or shape-equality premise,
alternate run, or whole-model backward-equivalence claim is introduced.
-/
namespace TrainVerify.Denote.SourceBWSumRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Read BW_sum's value from the original successful run's final Store. -/
theorem bw_sum_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (seed savedPrimal output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_sum", ins := [seed, savedPrimal],
        outs := [output], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hseed : ∀ row ∈ (sourceNode, none) :: after, seed ∉ row.1.outs)
    (hprimal : ∀ row ∈ (sourceNode, none) :: after, savedPrimal ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = bw_sum (t seed) (t savedPrimal) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [seed, savedPrimal]
    (fun a => bw_sum (a seed) (a savedPrimal)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hseed
    · have heq : tid = savedPrimal := List.mem_singleton.mp htid
      subst tid
      exact hprimal
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_sum" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_sum" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_sum_out g a rank seed savedPrimal output
  · intro a b hab
    rw [hab seed List.mem_cons_self,
      hab savedPrimal (List.mem_cons_of_mem seed List.mem_cons_self)]
  · exact hrun

#print axioms bw_sum_value_of_split
end
end TrainVerify.Denote.SourceBWSumRead
