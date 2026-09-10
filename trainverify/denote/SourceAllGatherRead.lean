import denote.SourceValueRead

namespace TrainVerify.Denote.SourceAllGatherRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

-- Invert the original scoped step. Resolution supplies the ordered group's
-- numParts = rs.length and localIndex = rs.idxOf rank; no global-rank shortcut.
private theorem allGather_of_success
    (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s t : Store) (rank : Nat) (inputs : List Tid) (output dim : Nat)
    (h : stepWithInputs g (.group (some rs)) peer s
      {rank := rank, op := "OpName.AllGatherPrim", ins := inputs,
        outs := [output], params := [dim]} none = some t) :
    t output = allGatherPrimDimN dim rs.length (rs.idxOf rank) (inputs.map s) := by
  classical
  let n : NodeDecl := {rank := rank, op := "OpName.AllGatherPrim", ins := inputs, outs := [output], params := [dim]}
  change stepWithInputs g (.group (some rs)) peer s n none = some t at h
  rw [stepWithInputs_ordinary g _ peer s n
    (by change "OpName.AllGatherPrim" ≠ "OpName.DATALOADER"; decide),
    step_group g _ peer s n
      (by change "OpName.AllGatherPrim" ≠ "OpName.AllToAllPrim"; decide)
      (by change "OpName.AllGatherPrim" ≠ "OpName.CROSS_DP_WRED"; decide)] at h
  by_cases hv : GroupScopedEval.WellFormed g.numRanks rank rs
  · rw [GroupScopedEval.step_scoped g s n rs hv (by rfl)] at h
    cases Option.some.inj h
    change storeSet s
      [(output, allGatherPrimDimN dim rs.length (rs.idxOf rank) (inputs.map s))] output = _
    simp only [storeSet, List.find?, decide_true]
  · simp only [GroupScopedEval.step, n, GroupScopedEval.resolve_invalid _ _ _ hv] at h
    contradiction

/-- Read the original AllGatherPrim output from the same returned Store.
The complete ordered input list, singleton output, explicit dimension and scope
are retained. Both the step law and read extensionality are closed internally.
No extra shape or arity guard is imposed: this is the existing source evaluator's
AllGatherPrim read law, not an additional physical-collective fidelity claim. -/
theorem allGather_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (rank : Nat) (rs : List Nat) (inputs : List Tid) (output dim : Nat) (s t : Store)
    (hnode : n = {rank := rank, op := "OpName.AllGatherPrim", ins := inputs, outs := [output], params := [dim]})
    (hsplit : requests = before ++ (n, none) :: after)
    (hscope : scope n = .group (some rs))
    (hreads : ∀ tid ∈ inputs, ∀ row ∈ (n, none) :: after, tid ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = allGatherPrimDimN dim rs.length (rs.idxOf rank) (inputs.map t) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after n
    output inputs (fun a => allGatherPrimDimN dim rs.length (rs.idxOf rank) (inputs.map a))
    s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · exact hreads
  · intro a b hstep
    rw [hscope, hnode] at hstep
    exact allGather_of_success g rs _ a b rank inputs output dim hstep
  · intro a b hab
    apply congrArg (allGatherPrimDimN dim rs.length (rs.idxOf rank))
    exact List.map_congr_left hab
  · exact hrun

#print axioms allGather_value_of_split
end
end TrainVerify.Denote.SourceAllGatherRead
