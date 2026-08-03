/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.MultirefGeneral
import denote.DenoteDistributedFaithful

/-!
# Explicit graph certificates for faithful `FW_multiref`

A certificate records every graph fact used to reduce one fan-out output.  In
particular, it does not hide the faithful evaluator's collective exclusions or
the prefix/suffix read/write conditions behind a tactic.  `FW_multiref` is
shape- and value-preserving, so no tensor-shape premise is required: the result
is an equality to the input tensor itself.
-/

namespace TrainVerify.Denote

/-- Checkable graph evidence for one output of a faithful multiref node.

The three `not*Collective` fields are deliberately explicit.  They document
why this node takes the conservative (local) branch of the faithful evaluator.
The four suffix fields are the exact side conditions needed by
`denoteGraphDistributedFaithful_reduce1`.
-/
structure FaithfulMultirefCertificate (g : GraphDecl) where
  index : Nat
  rank : Nat
  input : Tid
  outputs : List Tid
  arity : Nat
  output : Tid
  inBounds : index < g.nodes.length
  nodeAt : g.nodes[index]'inBounds =
    { rank := rank, op := "OpName.FW_multiref", ins := [input],
      outs := outputs, params := [arity] }
  arityMatches : outputs.length = arity
  outputMember : output ∈ outputs
  notShuffleCollective : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_shuffle"
  notUnshuffleCollective : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_unshuffle"
  notAttentionCollective : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag"
  suffixOutputsNonempty : ∀ n ∈ g.nodes.drop (index + 1), n.outs ≠ []
  outputNotWrittenAfter : ∀ n ∈ g.nodes.drop (index + 1), output ∉ n.outs
  prefixReadOutputsNonempty : ∀ n ∈ g.nodes.drop index, n.outs ≠ []
  inputNotWrittenFromNode : ∀ n ∈ g.nodes.drop index, input ∉ n.outs

/-- A valid certificate reduces its selected output to the multiref input.
There is no shape side condition because the local `FW_multiref` denotation is
exactly the identity, rather than merely shape-equivalent. -/
theorem denoteGraphDistributedFaithful_multiref
    (g : GraphDecl) (init : Store) (c : FaithfulMultirefCertificate g) :
    denoteGraphDistributedFaithful g init c.output =
      denoteGraphDistributedFaithful g init c.input := by
  refine denoteGraphDistributedFaithful_reduce1 g init c.index
    { rank := c.rank, op := "OpName.FW_multiref", ins := [c.input],
      outs := c.outputs, params := [c.arity] }
    c.input c.output (fun x => x) c.inBounds c.nodeAt ?_
    c.suffixOutputsNonempty c.outputNotWrittenAfter
    c.prefixReadOutputsNonempty c.inputNotWrittenFromNode
  intro s
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    c.notShuffleCollective c.notUnshuffleCollective c.notAttentionCollective]
  exact applyNode_fw_multiref_at g s c.rank c.input c.outputs c.arity
    c.arityMatches c.output c.outputMember

end TrainVerify.Denote
