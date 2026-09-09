import denote.SourceScopedEval

namespace TrainVerify.Denote.SourcePrimitiveSteps
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Invert the original checked Chunk step, not a second evaluator. -/
theorem chunk_of_success (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s t : Store) (rank input output dim : Nat)
    (h : stepWithInputs g (.group (some rs)) peer s
      {rank := rank, op := "OpName.ChunkPrim", ins := [input], outs := [output], params := [dim]} none = some t) :
    t output = chunkPrimDimN dim rs.length (rs.idxOf rank) (s input) := by
  classical
  let n : NodeDecl := {rank := rank, op := "OpName.ChunkPrim", ins := [input], outs := [output], params := [dim]}
  change stepWithInputs g (.group (some rs)) peer s n none = some t at h
  rw [stepWithInputs_ordinary g _ peer s n
    (by change "OpName.ChunkPrim" ≠ "OpName.DATALOADER"; decide),
    step_group g _ peer s n
      (by change "OpName.ChunkPrim" ≠ "OpName.AllToAllPrim"; decide)
      (by change "OpName.ChunkPrim" ≠ "OpName.CROSS_DP_WRED"; decide)] at h
  by_cases hv : GroupScopedEval.WellFormed g.numRanks rank rs
  · rw [GroupScopedEval.step_scoped g s n rs hv (by rfl)] at h
    cases Option.some.inj h
    change storeSet s [(output, chunkPrimDimN dim rs.length (rs.idxOf rank) (s input))] output = _
    simp only [storeSet, List.find?, decide_true]
  · simp only [GroupScopedEval.step, n, GroupScopedEval.resolve_invalid _ _ _ hv] at h
    contradiction

/-- Successful source AllToAll is sender-split followed by receiver gather.
The original scope and ordered peer inputs remain unchanged. -/
theorem allToAll_of_success (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s t : Store) (rank idim odim output : Nat) (inputs : List Tid)
    (h : stepWithInputs g (.group (some rs)) peer s
      {rank := rank, op := "OpName.AllToAllPrim", ins := inputs, outs := [output], params := [idim, odim]} none = some t) :
    t output = AllToAllSourceFaithful.tensor rs.length (rs.idxOf rank) idim odim (inputs.map s) := by
  classical
  let n : NodeDecl := {rank := rank, op := "OpName.AllToAllPrim", ins := inputs, outs := [output], params := [idim, odim]}
  change stepWithInputs g (.group (some rs)) peer s n none = some t at h
  rw [stepWithInputs_ordinary g _ peer s n
    (by change "OpName.AllToAllPrim" ≠ "OpName.DATALOADER"; decide),
    step_allToAll g _ peer s n rfl] at h
  by_cases hv : GroupScopedEval.WellFormed g.numRanks rank rs
  · simp only [AllToAllSourceFaithful.step, n, GroupScopedEval.resolve_valid _ _ _ hv] at h
    split at h
    · cases Option.some.inj h
      exact AllToAllSourceFaithful.localStep_out rs s n idim odim output rfl
    · contradiction
  · rw [AllToAllSourceFaithful.step_rejected g rs peer s n hv] at h
    contradiction

#print axioms chunk_of_success
#print axioms allToAll_of_success
end
end TrainVerify.Denote.SourcePrimitiveSteps
