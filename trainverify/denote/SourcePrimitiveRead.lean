import denote.SourceValueRead
import denote.SourcePrimitiveSteps

namespace TrainVerify.Denote.SourcePrimitiveRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Actual Chunk read on the same returned Store; only structural metadata
and the original successful run are required from the caller. -/
theorem chunk_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (rank : Nat) (rs : List Nat) (input output dim : Nat) (s t : Store)
    (hnode : n = {rank := rank, op := "OpName.ChunkPrim", ins := [input], outs := [output], params := [dim]})
    (hsplit : requests = before ++ (n, none) :: after)
    (hscope : scope n = .group (some rs))
    (hreads : ∀ row ∈ (n, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = chunkPrimDimN dim rs.length (rs.idxOf rank) (t input) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after n
    output [input] (fun a => chunkPrimDimN dim rs.length (rs.idxOf rank) (a input)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    have heq : tid = input := List.mem_singleton.mp htid
    subst tid
    exact hreads
  · intro a b hstep
    rw [hscope, hnode] at hstep
    exact SourcePrimitiveSteps.chunk_of_success g rs (peer n) a b rank input output dim hstep
  · intro a b hab
    exact congrArg (chunkPrimDimN dim rs.length (rs.idxOf rank)) (hab input List.mem_cons_self)
  · exact hrun

/-- Faithful AllToAll read: ordered sender split then receiver gather. The
primitive laws and read extensionality are discharged internally, not assumed
as final-store value hypotheses. -/
theorem allToAll_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (rank : Nat) (rs : List Nat) (inputs : List Tid) (output idim odim : Nat) (s t : Store)
    (hnode : n = {rank := rank, op := "OpName.AllToAllPrim", ins := inputs, outs := [output], params := [idim, odim]})
    (hsplit : requests = before ++ (n, none) :: after)
    (hscope : scope n = .group (some rs))
    (hreads : ∀ tid ∈ inputs, ∀ row ∈ (n, none) :: after, tid ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = AllToAllSourceFaithful.tensor rs.length (rs.idxOf rank) idim odim (inputs.map t) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after n
    output inputs (fun a => AllToAllSourceFaithful.tensor rs.length (rs.idxOf rank) idim odim (inputs.map a))
    s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · exact hreads
  · intro a b hstep
    rw [hscope, hnode] at hstep
    exact SourcePrimitiveSteps.allToAll_of_success g rs _ a b rank idim odim output inputs hstep
  · intro a b hab
    apply congrArg (AllToAllSourceFaithful.tensor rs.length (rs.idxOf rank) idim odim)
    exact List.map_congr_left hab
  · exact hrun

#print axioms chunk_value_of_split
#print axioms allToAll_value_of_split
end
end TrainVerify.Denote.SourcePrimitiveRead
