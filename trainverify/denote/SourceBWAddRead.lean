import denote.SourceValueRead

/-!
Both BW_add outputs in the SAME final Store of the original successful checked
run. Inputs are ordered [grad, left, right], outputs [dleft, dright], params empty,
with explicit global scope. Input nonwrites cover the selected node and complete
suffix; checked schedule uniqueness supplies output freshness. No shape or
output-value premise is introduced. The result retains broadcast reduction via
bw_add2, rather than assuming either output equals grad.
-/
namespace TrainVerify.Denote.SourceBWAddRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- First BW_add output, read from the original successful run's final Store. -/
theorem bw_add_dleft_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad left right dleft dright : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_add", ins := [grad, left, right],
        outs := [dleft, dright], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdistinct : dleft ≠ dright)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hleft : ∀ row ∈ (sourceNode, none) :: after, left ∉ row.1.outs)
    (hright : ∀ row ∈ (sourceNode, none) :: after, right ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dleft = (bw_add2 (t grad) (t left) (t right)).1 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dleft [grad, left, right]
    (fun a => (bw_add2 (a grad) (a left) (a right)).1) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · rcases List.mem_cons.mp htid with heq | htid
      · subst tid
        exact hleft
      · have heq : tid = right := List.mem_singleton.mp htid
        subst tid
        exact hright
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_add" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_add" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_add2_fst_out g a rank grad left right dleft dright hdistinct
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab left (List.mem_cons_of_mem grad List.mem_cons_self),
      hab right (List.mem_cons_of_mem grad (List.mem_cons_of_mem left List.mem_cons_self))]
  · exact hrun

/-- Second BW_add output; distinct IDs prevent first-entry shadowing. -/
theorem bw_add_dright_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad left right dleft dright : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_add", ins := [grad, left, right],
        outs := [dleft, dright], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdistinct : dleft ≠ dright)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hleft : ∀ row ∈ (sourceNode, none) :: after, left ∉ row.1.outs)
    (hright : ∀ row ∈ (sourceNode, none) :: after, right ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dright = (bw_add2 (t grad) (t left) (t right)).2 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dright [grad, left, right]
    (fun a => (bw_add2 (a grad) (a left) (a right)).2) s t hsplit
  · rw [hnode]
    exact List.mem_cons_of_mem dleft List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · rcases List.mem_cons.mp htid with heq | htid
      · subst tid
        exact hleft
      · have heq : tid = right := List.mem_singleton.mp htid
        subst tid
        exact hright
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_add" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_add" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_add2_snd_out g a rank grad left right dleft dright hdistinct
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab left (List.mem_cons_of_mem grad List.mem_cons_self),
      hab right (List.mem_cons_of_mem grad (List.mem_cons_of_mem left List.mem_cons_self))]
  · exact hrun

#print axioms bw_add_dleft_value_of_split
#print axioms bw_add_dright_value_of_split
end
end TrainVerify.Denote.SourceBWAddRead
