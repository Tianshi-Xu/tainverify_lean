import denote.SourceValueRead

/-!
Ordinary source BW_layernorm reads in the SAME final Store returned by the
original successful runWithInputs. Inputs are [grad, input, gamma, beta], outputs
are [dx, dgamma, dbeta], params are empty, and the selected request is global.
All three pairwise output-ID inequalities are explicit in each public interface.
Read nonwrites cover the selected node and its complete suffix; the checked
InputSchedule supplies output freshness. No output shape/value is a premise.

These lemmas transport the existing Denote semantics (last-dimension layernorm,
layerNormEps = 1 / 100000); they neither re-prove layernorm mathematics nor
assert source/runtime authentication, which is a separate caller-side gate.
-/
namespace TrainVerify.Denote.SourceBWLayernormRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Read dx from the original final Store via the existing output law. -/
theorem bw_layernorm_dx_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad input gamma beta dx dgamma dbeta : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_layernorm", ins := [grad, input, gamma, beta],
        outs := [dx, dgamma, dbeta], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdx_dgamma : dx ≠ dgamma) (hdx_dbeta : dx ≠ dbeta)
    (hdgamma_dbeta : dgamma ≠ dbeta)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hgamma : ∀ row ∈ (sourceNode, none) :: after, gamma ∉ row.1.outs)
    (hbeta : ∀ row ∈ (sourceNode, none) :: after, beta ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dx = (bw_layernorm (t grad) (t input) (t gamma) (t beta)).1 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dx [grad, input, gamma, beta]
    (fun a => (bw_layernorm (a grad) (a input) (a gamma) (a beta)).1) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · rcases List.mem_cons.mp htid with heq | htid
      · subst tid
        exact hinput
      · rcases List.mem_cons.mp htid with heq | htid
        · subst tid
          exact hgamma
        · have heq : tid = beta := List.mem_singleton.mp htid
          subst tid
          exact hbeta
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_layernorm" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_layernorm" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_layernorm_dx_out g a rank grad input gamma beta dx dgamma dbeta
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab input (List.mem_cons_of_mem grad List.mem_cons_self),
      hab gamma (List.mem_cons_of_mem grad (List.mem_cons_of_mem input List.mem_cons_self)),
      hab beta (List.mem_cons_of_mem grad
        (List.mem_cons_of_mem input (List.mem_cons_of_mem gamma List.mem_cons_self)))]
  · exact hrun

/-- Read dgamma from the original final Store via the existing output law. -/
theorem bw_layernorm_dgamma_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad input gamma beta dx dgamma dbeta : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_layernorm", ins := [grad, input, gamma, beta],
        outs := [dx, dgamma, dbeta], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdx_dgamma : dx ≠ dgamma) (hdx_dbeta : dx ≠ dbeta)
    (hdgamma_dbeta : dgamma ≠ dbeta)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hgamma : ∀ row ∈ (sourceNode, none) :: after, gamma ∉ row.1.outs)
    (hbeta : ∀ row ∈ (sourceNode, none) :: after, beta ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dgamma = (bw_layernorm (t grad) (t input) (t gamma) (t beta)).2.1 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dgamma [grad, input, gamma, beta]
    (fun a => (bw_layernorm (a grad) (a input) (a gamma) (a beta)).2.1) s t hsplit
  · rw [hnode]
    exact List.mem_cons_of_mem dx List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · rcases List.mem_cons.mp htid with heq | htid
      · subst tid
        exact hinput
      · rcases List.mem_cons.mp htid with heq | htid
        · subst tid
          exact hgamma
        · have heq : tid = beta := List.mem_singleton.mp htid
          subst tid
          exact hbeta
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_layernorm" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_layernorm" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_layernorm_dw_out g a rank grad input gamma beta dx dgamma dbeta hdx_dgamma
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab input (List.mem_cons_of_mem grad List.mem_cons_self),
      hab gamma (List.mem_cons_of_mem grad (List.mem_cons_of_mem input List.mem_cons_self)),
      hab beta (List.mem_cons_of_mem grad
        (List.mem_cons_of_mem input (List.mem_cons_of_mem gamma List.mem_cons_self)))]
  · exact hrun

/-- Read dbeta from the original final Store via the existing output law. -/
theorem bw_layernorm_dbeta_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (grad input gamma beta dx dgamma dbeta : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.BW_layernorm", ins := [grad, input, gamma, beta],
        outs := [dx, dgamma, dbeta], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hdx_dgamma : dx ≠ dgamma) (hdx_dbeta : dx ≠ dbeta)
    (hdgamma_dbeta : dgamma ≠ dbeta)
    (hgrad : ∀ row ∈ (sourceNode, none) :: after, grad ∉ row.1.outs)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hgamma : ∀ row ∈ (sourceNode, none) :: after, gamma ∉ row.1.outs)
    (hbeta : ∀ row ∈ (sourceNode, none) :: after, beta ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t dbeta = (bw_layernorm (t grad) (t input) (t gamma) (t beta)).2.2 := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode dbeta [grad, input, gamma, beta]
    (fun a => (bw_layernorm (a grad) (a input) (a gamma) (a beta)).2.2) s t hsplit
  · rw [hnode]
    exact List.mem_cons_of_mem dx (List.mem_cons_of_mem dgamma List.mem_cons_self)
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
    · subst tid
      exact hgrad
    · rcases List.mem_cons.mp htid with heq | htid
      · subst tid
        exact hinput
      · rcases List.mem_cons.mp htid with heq | htid
        · subst tid
          exact hgamma
        · have heq : tid = beta := List.mem_singleton.mp htid
          subst tid
          exact hbeta
  · intro a b hstep
    have hselected : stepWithInputs g (scope sourceNode) (peer sourceNode)
        a sourceNode none = some (applyNode g a sourceNode) := by
      rw [hscope, hnode]
      rw [stepWithInputs_ordinary _ _ _ _ _
        (by change "OpName.BW_layernorm" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.BW_layernorm" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_bw_layernorm_db_out g a rank grad input gamma beta dx dgamma dbeta hdx_dbeta hdgamma_dbeta
  · intro a b hab
    rw [hab grad List.mem_cons_self,
      hab input (List.mem_cons_of_mem grad List.mem_cons_self),
      hab gamma (List.mem_cons_of_mem grad (List.mem_cons_of_mem input List.mem_cons_self)),
      hab beta (List.mem_cons_of_mem grad
        (List.mem_cons_of_mem input (List.mem_cons_of_mem gamma List.mem_cons_self)))]
  · exact hrun

#print axioms bw_layernorm_dx_value_of_split
#print axioms bw_layernorm_dgamma_value_of_split
#print axioms bw_layernorm_dbeta_value_of_split
end
end TrainVerify.Denote.SourceBWLayernormRead
