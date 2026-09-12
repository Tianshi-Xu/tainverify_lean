import denote.SourceValueRead

/-!
Ordinary source BW_matmul reads in the SAME final Store
returned by the original successful runWithInputs. The selected node has exactly
inputs [g, x, y], outputs [dx, dy], empty params and an explicit global request.
The original request split retains the complete checked evaluator and order.

Read nonwrites include the selected node AND its entire suffix. Output freshness
comes from the successful run's checked InputSchedule inside SourceValueRead.
The distinct-output guard is passed to the separate existing first/second-output
Denote lemmas. No output-value, shape-equality, alternate-run, or KRank-algebra
hypothesis is added. These conditional source reads are not whole-model claims.
-/
namespace TrainVerify.Denote.SourceBWMatmulRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- dX read from the original final Store, using the BW first-output law. -/
theorem bw_matmul_dx_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad left right dx dy : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_matmul", ins := [grad, left, right],
        outs := [dx, dy], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdistinct : dx ≠ dy)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hleft : ∀ row ∈ (sourceNode, none) :: after, left ∉ row.1.outs)
    (hright : ∀ row ∈ (sourceNode, none) :: after, right ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = (bw_matmul (t grad) (t left) (t right)).1 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad, left, right]
    (fun a => (bw_matmul (a grad) (a left) (a right)).1) s t hsplit
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
        (by change "OpName.BW_matmul" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_matmul" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_matmul_fst_out g a rank grad left right dx dy hdistinct
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab left (List.mem_cons_of_mem grad List.mem_cons_self),
      hab right (List.mem_cons_of_mem grad (List.mem_cons_of_mem left List.mem_cons_self))]
  · exact hrun

/-- dY read from the original final Store, using the BW second-output law.
The distinct-output guard prevents the first storeSet entry shadowing dY. -/
theorem bw_matmul_dy_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad left right dx dy : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_matmul", ins := [grad, left, right],
        outs := [dx, dy], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdistinct : dx ≠ dy)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hleft : ∀ row ∈ (sourceNode, none) :: after, left ∉ row.1.outs)
    (hright : ∀ row ∈ (sourceNode, none) :: after, right ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dy = (bw_matmul (t grad) (t left) (t right)).2 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dy [grad, left, right]
    (fun a => (bw_matmul (a grad) (a left) (a right)).2) s t hsplit
  · rw [hnode]
    exact List.mem_cons_of_mem dx List.mem_cons_self
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
        (by change "OpName.BW_matmul" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_matmul" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_matmul_snd_out g a rank grad left right dx dy hdistinct
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab left (List.mem_cons_of_mem grad List.mem_cons_self),
      hab right (List.mem_cons_of_mem grad (List.mem_cons_of_mem left List.mem_cons_self))]
  · exact hrun

#print axioms bw_matmul_dx_value_of_split
#print axioms bw_matmul_dy_value_of_split
end
end TrainVerify.Denote.SourceBWMatmulRead
