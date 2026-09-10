import denote.SourceValueRead

/-!
Read ordinary source layout operations in the SAME final Store returned by the
original successful runWithInputs. Exact source nodes retain their input/output
ports and parameters, and require an explicit global request. The original
request split preserves the complete checked evaluator and source order.

Input nonwrites cover both the selected node and its entire suffix. Schedule
output uniqueness supplies output nonoverwrite. Ordinary selected-step success
and read extensionality are discharged internally, without shape hypotheses.
The source FW_transpose tag uses transposeAxes with dimensions before the tensor.
-/
namespace TrainVerify.Denote.SourceLayoutRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Read a view with an arbitrary nonempty target shape from the original final
Store, using the existing Denote semantics without shape or value premises. -/
theorem view_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input output : Tid) (hd : Nat) (tl : List Nat) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_view", ins := [input], outs := [output], params := hd :: tl })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = fw_view (hd :: tl) (t input) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input] (fun a => fw_view (hd :: tl) (a input)) s t hsplit
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
        (by change "OpName.FW_view" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_view" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_view_out g a rank hd tl input output
  · intro a b hab
    rw [hab input List.mem_cons_self]
  · exact hrun

/-- Read the arbitrary-axis transpose selected by exact source parameters from
the original final Store. Dimensions precede the tensor in transposeAxes. -/
theorem transposeAxes_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input output : Tid) (d0 d1 : Nat) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_transpose", ins := [input], outs := [output], params := [d0, d1] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = transposeAxes d0 d1 (t input) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input] (fun a => transposeAxes d0 d1 (a input)) s t hsplit
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
        (by change "OpName.FW_transpose" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_transpose" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_transposeAxes_out g a rank input output d0 d1
  · intro a b hab
    rw [hab input List.mem_cons_self]
  · exact hrun

#print axioms view_value_of_split
#print axioms transposeAxes_value_of_split
end
end TrainVerify.Denote.SourceLayoutRead
