import denote.SourceValueRead
import denote.MultirefGeneral

/-!
Read every output of an ordinary source FW_multiref in the SAME final Store
returned by the original successful runWithInputs. The exact source node and
request split retain all outputs, their order, and the original params
[outs.length]. The input is exactly one port and the request is global.

Input nonwrites cover the selected node and its suffix. Schedule output
uniqueness supplies output nonoverwrite; no additional output distinctness
assumption or caller-supplied step/value equation is required.
-/
namespace TrainVerify.Denote.SourceMultirefRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Every output member of the original source multiref reads the input value
in the same final Store. The ordinary step law is discharged internally. -/
theorem multiref_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input : Tid) (outs : List Tid) (out : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_multiref", ins := [input],
        outs := outs, params := [outs.length] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hout : out ∈ outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t out = t input := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode out [input] (fun a => a input) s t hsplit
  · rw [hnode]
    exact hout
  · intro tid htid
    have heq : tid = input := List.mem_singleton.mp htid
    subst tid
    exact hinput
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.FW_multiref" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_multiref" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_multiref_at g a rank input outs outs.length rfl out hout
  · intro a b hab
    exact hab input List.mem_cons_self
  · exact hrun

/-- Retain the complete original output list, in source order and at arbitrary
arity: all its final reads are copies of the same final input read. -/
theorem multiref_values_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input : Tid) (outs : List Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_multiref", ins := [input],
        outs := outs, params := [outs.length] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    outs.map t = List.replicate outs.length (t input) := by
  have hvalues : ∀ out ∈ outs, t out = t input := by
    intro out hout
    exact multiref_value_of_split g scope peer nodes requests before after sourceNode
      rank input outs out s t hnode hsplit hscope hinput hout hrun
  have hmap : ∀ ids : List Tid, (∀ out ∈ ids, t out = t input) →
      ids.map t = List.replicate ids.length (t input) := by
    intro ids
    induction ids with
    | nil => intro _; rfl
    | cons out rest ih =>
      intro h
      change t out :: rest.map t = t input :: List.replicate rest.length (t input)
      rw [h out List.mem_cons_self,
        ih (fun tid htid => h tid (List.mem_cons_of_mem out htid))]
  exact hmap outs hvalues

#print axioms multiref_value_of_split
#print axioms multiref_values_of_split
end
end TrainVerify.Denote.SourceMultirefRead
