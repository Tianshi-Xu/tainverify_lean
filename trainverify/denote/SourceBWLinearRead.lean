import denote.SourceValueRead

/-!
Ordinary source BW_linear reads in the SAME final Store
returned by the original successful runWithInputs. The selected node has exactly
inputs [dy, x, w], outputs [dx, dw], empty params and an explicit global request.
The original request split retains the complete checked evaluator and order.

Read nonwrites include the selected node AND its entire suffix. Output freshness
comes from the successful run's checked InputSchedule inside SourceValueRead.
The distinct-output guard is passed to the separate existing first/second-output
Denote lemmas. No output-value, shape-equality, alternate-run, or KRank-algebra
hypothesis is added. These conditional source reads are not whole-model claims.
-/
namespace TrainVerify.Denote.SourceBWLinearRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- dX read from the original final Store, using the BW first-output law. -/
theorem bw_linear_dx_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad input weight dx dw : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_linear", ins := [grad, input, weight],
        outs := [dx, dw], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdistinct : dx ≠ dw)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hweight : ∀ row ∈ (sourceNode, none) :: after, weight ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = (bw_linear (t grad) (t input) (t weight)).1 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad, input, weight]
    (fun a => (bw_linear (a grad) (a input) (a weight)).1) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · rcases List.mem_cons.mp htid with heq | htid
      · subst tid
        exact hinput
      · have heq : tid = weight := List.mem_singleton.mp htid
        subst tid
        exact hweight
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_linear" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_linear" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_linear_fst_out g a rank grad input weight dx dw hdistinct
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab input (List.mem_cons_of_mem grad List.mem_cons_self),
      hab weight (List.mem_cons_of_mem grad (List.mem_cons_of_mem input List.mem_cons_self))]
  · exact hrun

/-- dW read from the original final Store, using the BW second-output law.
The distinct-output guard prevents the first storeSet entry shadowing dW. -/
theorem bw_linear_dw_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad input weight dx dw : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_linear", ins := [grad, input, weight],
        outs := [dx, dw], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdistinct : dx ≠ dw)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hweight : ∀ row ∈ (sourceNode, none) :: after, weight ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dw = (bw_linear (t grad) (t input) (t weight)).2 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dw [grad, input, weight]
    (fun a => (bw_linear (a grad) (a input) (a weight)).2) s t hsplit
  · rw [hnode]
    exact List.mem_cons_of_mem dx List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · rcases List.mem_cons.mp htid with heq | htid
      · subst tid
        exact hinput
      · have heq : tid = weight := List.mem_singleton.mp htid
        subst tid
        exact hweight
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_linear" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_linear" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_linear_snd_out g a rank grad input weight dx dw hdistinct
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab input (List.mem_cons_of_mem grad List.mem_cons_self),
      hab weight (List.mem_cons_of_mem grad (List.mem_cons_of_mem input List.mem_cons_self))]
  · exact hrun

#print axioms bw_linear_dx_value_of_split
#print axioms bw_linear_dw_value_of_split
end
end TrainVerify.Denote.SourceBWLinearRead
