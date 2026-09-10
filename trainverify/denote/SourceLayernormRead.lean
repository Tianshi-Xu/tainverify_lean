import denote.SourceValueRead

/-!
Read an ordinary source FW_layernorm in the SAME final Store returned by the
original successful runWithInputs. The exact source node has three input ports,
one output, empty params, and an explicit global request. The original request
split retains the complete checked evaluator and source order.

Nonwrites for input, gamma, and beta cover both the selected node and its entire
suffix. Schedule output uniqueness supplies output nonoverwrite. This theorem
uses the existing Denote default layernorm semantics; authentication of raw
source kwargs and their supported shapes is a separate caller-side obligation,
not an additional value or shape hypothesis of this library theorem.
-/
namespace TrainVerify.Denote.SourceLayernormRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The original successful run determines the final layernorm value. The
ordinary success law and read extensionality are discharged internally. -/
theorem layernorm_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (sourceNode : NodeDecl)
    (rank : Nat) (input gamma beta output : Tid) (s t : Store)
    (hnode : sourceNode =
      { rank := rank, op := "OpName.FW_layernorm", ins := [input, gamma, beta],
        outs := [output], params := [] })
    (hsplit : requests = before ++ (sourceNode, none) :: after)
    (hscope : scope sourceNode = .global)
    (hinput : ∀ row ∈ (sourceNode, none) :: after, input ∉ row.1.outs)
    (hgamma : ∀ row ∈ (sourceNode, none) :: after, gamma ∉ row.1.outs)
    (hbeta : ∀ row ∈ (sourceNode, none) :: after, beta ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t output = fw_layernorm (t input) (t gamma) (t beta) := by
  apply SourceValueRead.node_value_of_split g scope peer nodes requests before after
    sourceNode output [input, gamma, beta]
    (fun a => fw_layernorm (a input) (a gamma) (a beta)) s t hsplit
  · rw [hnode]
    exact List.mem_cons_self
  · intro tid htid
    rcases List.mem_cons.mp htid with heq | htid
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
        (by change "OpName.FW_layernorm" ≠ "OpName.DATALOADER"; decide)]
      exact step_global _ _ _ _
        (by change ordinary "OpName.FW_layernorm" = true; decide)
    have hb : applyNode g a sourceNode = b :=
      Option.some.inj (hselected.symm.trans hstep)
    rw [← hb, hnode]
    exact applyNode_fw_layernorm_out g a rank input gamma beta output []
  · intro a b hab
    rw [hab input List.mem_cons_self,
      hab gamma (List.mem_cons_of_mem input List.mem_cons_self),
      hab beta (List.mem_cons_of_mem input (List.mem_cons_of_mem gamma List.mem_cons_self))]
  · exact hrun

#print axioms layernorm_value_of_split
end
end TrainVerify.Denote.SourceLayernormRead
