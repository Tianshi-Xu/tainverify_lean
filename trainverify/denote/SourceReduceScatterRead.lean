import denote.SourceValueRead

/-!
ReduceScatter reads in the SAME final Store of the original source-scoped run.
The selected primitive sums its ordered full inputs before chunking on `dim`;
its local chunk index is the position in the ordered group, not the world rank.

The baseline SourcePrimitiveSteps has no ReduceScatter success helper, so the
missing helper lives here rather than modifying that shared forward-owned file.
GroupScopedEval checks group validity, but does not check equal input shapes or
ordered peer attachment for this primitive. This is an exact evaluator read,
not a claim that success authenticates those extra source-fidelity conditions.
-/
namespace TrainVerify.Denote.SourceReduceScatterRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The existing reduction is exactly ordered tensorSum followed by chunk. -/
theorem reduceScatter_eq_chunk_tensorSum (dim numParts rank : Nat) (xs : List Tensor) :
    reduceScatterPrimDimN dim numParts rank xs =
      chunkPrimDimN dim numParts rank (tensorSum xs) := by
  cases xs <;> rfl

/-- Invert the original checked step; no alternate evaluator or output premise. -/
theorem reduceScatter_of_success (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s t : Store) (rank dim output : Nat) (inputs : List Tid)
    (h : stepWithInputs g (.group (some rs)) peer s
      {rank := rank, op := "OpName.ReduceScatterPrim", ins := inputs,
        outs := [output], params := [dim]} none = some t) :
    t output = reduceScatterPrimDimN dim rs.length (rs.idxOf rank) (inputs.map s) := by
  classical
  let n : NodeDecl := {rank := rank, op := "OpName.ReduceScatterPrim", ins := inputs, outs := [output], params := [dim]}
  change stepWithInputs g (.group (some rs)) peer s n none = some t at h
  rw [stepWithInputs_ordinary g _ peer s n
    (by change "OpName.ReduceScatterPrim" ≠ "OpName.DATALOADER"; decide),
    step_group g _ peer s n
      (by change "OpName.ReduceScatterPrim" ≠ "OpName.AllToAllPrim"; decide)
      (by change "OpName.ReduceScatterPrim" ≠ "OpName.CROSS_DP_WRED"; decide)] at h
  by_cases hv : GroupScopedEval.WellFormed g.numRanks rank rs
  · rw [GroupScopedEval.step_scoped g s n rs hv (by rfl)] at h
    cases Option.some.inj h
    change storeSet s [(output,
      reduceScatterPrimDimN dim rs.length (rs.idxOf rank) (inputs.map s))] output = _
    simp only [storeSet, List.find?, decide_true]
  · simp only [GroupScopedEval.step, n, GroupScopedEval.resolve_invalid _ _ _ hv] at h
    contradiction

/-- Success of the original run supplies the selected step and output freshness.
Read-ID nonwrites cover the selected node and the entire suffix, ensuring that
both sides use precisely its returned Store. No output/shape equation is assumed. -/
theorem reduceScatter_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (rank : Nat) (rs : List Nat) (inputs : List Tid) (output dim : Nat) (s t : Store)
    (hnode : n = {rank := rank, op := "OpName.ReduceScatterPrim", ins := inputs, outs := [output], params := [dim]})
    (hsplit : requests = before ++ (n, none) :: after)
    (hscope : scope n = .group (some rs))
    (hreads : ∀ tid ∈ inputs, ∀ row ∈ (n, none) :: after, tid ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = chunkPrimDimN dim rs.length (rs.idxOf rank) (tensorSum (inputs.map t)) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after n
    output inputs (fun a => chunkPrimDimN dim rs.length (rs.idxOf rank) (tensorSum (inputs.map a)))
    s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · exact hreads
  · intro a b hstep
    rw [hscope, hnode] at hstep
    exact (reduceScatter_of_success g rs _ a b rank dim output inputs hstep).trans
      (reduceScatter_eq_chunk_tensorSum dim rs.length (rs.idxOf rank) (inputs.map a))
  · intro a b hab
    exact congrArg (fun xs => chunkPrimDimN dim rs.length (rs.idxOf rank) (tensorSum xs))
      (List.map_congr_left hab)
  · exact hrun

#print axioms reduceScatter_eq_chunk_tensorSum
#print axioms reduceScatter_of_success
#print axioms reduceScatter_value_of_split
end
end TrainVerify.Denote.SourceReduceScatterRead
