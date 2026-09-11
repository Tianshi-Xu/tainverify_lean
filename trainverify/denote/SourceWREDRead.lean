import denote.SourceValueRead

/-!
Source-scoped WRED SUM reads in the original final Store. Parameter identity,
DP ownership and absence of replica scaling belong to source attachment, not
to WredContract or an output-value assumption. The checked successful step
supplies the group and equal-shape obligations internally.
-/
namespace TrainVerify.Denote.SourceWREDRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Invert the successful original checked WRED step. -/
theorem wred_of_success (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s t : Store) (rank output : Nat) (inputs : List Tid)
    (h : stepWithInputs g (.group (some rs)) peer s
      {rank := rank, op := "OpName.CROSS_DP_WRED", ins := inputs, outs := [output], params := []} none = some t) :
    t output = cross_dp_wred (inputs.map s) := by
  let n : NodeDecl := {rank := rank, op := "OpName.CROSS_DP_WRED", ins := inputs, outs := [output], params := []}
  change stepWithInputs g (.group (some rs)) peer s n none = some t at h
  rw [stepWithInputs_ordinary g _ peer s n
    (by change "OpName.CROSS_DP_WRED" ≠ "OpName.DATALOADER"; decide),
    step_wred g _ peer s n rfl] at h
  change (if GroupScopedEval.WellFormed g.numRanks rank rs ∧ WredContract rs peer s n
    then some (applyNode g s n) else none) = some t at h
  split at h
  · cases Option.some.inj h
    exact applyNode_cross_dp_wred_out g s rank inputs output
  · contradiction

/-- The original successful run determines the WRED value in that same final
Store. Read preservation includes the selected node and the complete suffix. -/
theorem wred_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (rank : Nat) (rs : List Nat) (inputs : List Tid) (output : Tid) (s t : Store)
    (hnode : n = {rank := rank, op := "OpName.CROSS_DP_WRED", ins := inputs, outs := [output], params := []})
    (hsplit : requests = before ++ (n, none) :: after)
    (hscope : scope n = .group (some rs))
    (hreads : ∀ tid ∈ inputs, ∀ row ∈ (n, none) :: after, tid ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = cross_dp_wred (inputs.map t) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after n
    output inputs (fun a => cross_dp_wred (inputs.map a)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · exact hreads
  · intro a b hstep
    rw [hscope, hnode] at hstep
    exact wred_of_success g rs _ a b rank output inputs hstep
  · intro a b hab
    exact congrArg cross_dp_wred (List.map_congr_left hab)
  · exact hrun

#print axioms wred_of_success
#print axioms wred_value_of_split
end
end TrainVerify.Denote.SourceWREDRead
