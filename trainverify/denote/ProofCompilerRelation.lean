import denote.Denote

namespace TrainVerify.Denote.ProofCompiler

open TrainVerify.Denote

/-- Closed value-level relation subset accepted by the first kernel-checking slice.

The Python IR has additional variants. They are deliberately not represented here
until their faithful value semantics and side conditions are specified; the emitter
must reject them rather than manufacture a theorem. -/
inductive Relation where
  | equal
  | replicated
  | contiguousShard (dim parts : Nat)
  deriving Repr, DecidableEq

/-- The mathematical meaning of an SM/PM tensor relation.

Unlike the legacy `LineageGoal.replicated` reconstruction, `replicated` checks every
rank-local value and the complete rank count. -/
def Holds (numRanks : Nat) (relation : Relation) (sm : Tensor) (pm : List Tensor) : Prop :=
  match relation with
  | .equal => pm = [sm]
  | .replicated =>
      pm.length = numRanks ∧ ∀ tensor ∈ pm, tensor = sm
  | .contiguousShard dim parts =>
      pm.length = parts ∧
      sm = allGatherPrimDimN dim parts 0 pm

/-- One already-related input to a semantic relation rule. -/
structure RelatedInput where
  sm : Tensor
  pm : List Tensor

/-- Every input relation named by a rule is backed by a value-level proof. -/
def PremisesHold (numRanks : Nat) (expected : List Relation)
    (inputs : List RelatedInput) : Prop :=
  List.Forall₂ (fun relation input =>
    Holds numRanks relation input.sm input.pm) expected inputs

/-- Kernel-facing type of a relation theorem.

`semantics` is fixed by the theorem constant registered for an operator. Generated
certificates must prove that predicate from the actual graph denotations before the
rule can produce an output relation. -/
def RuleHolds (inputRelations : List Relation) (outputRelation : Relation)
    (semantics : List RelatedInput → Tensor → List Tensor → Prop) : Prop :=
  ∀ numRanks inputs smOutput pmOutput,
    PremisesHold numRanks inputRelations inputs →
    semantics inputs smOutput pmOutput →
    Holds numRanks outputRelation smOutput pmOutput

/-- Actual output semantics of applying the same unary tensor function to an SM
value and every PM value. -/
def UnaryMapSemantics (f : Tensor → Tensor)
    (inputs : List RelatedInput) (smOutput : Tensor) (pmOutput : List Tensor) : Prop :=
  ∃ input, inputs = [input] ∧
    smOutput = f input.sm ∧
    pmOutput = input.pm.map f

/-- Any unary function preserves exact equality. -/
theorem unaryMap_equal (f : Tensor → Tensor) :
    RuleHolds [.equal] .equal (UnaryMapSemantics f) := by
  intro numRanks inputs smOutput pmOutput hpremises hsemantics
  rcases hsemantics with ⟨input, rfl, rfl, rfl⟩
  have hinput : Holds numRanks .equal input.sm input.pm :=
    by simpa [PremisesHold] using hpremises
  change input.pm.map f = [f input.sm]
  rw [hinput]
  rfl

/-- Any unary function applied independently on every rank preserves replication. -/
theorem unaryMap_replicated (f : Tensor → Tensor) :
    RuleHolds [.replicated] .replicated (UnaryMapSemantics f) := by
  intro numRanks inputs smOutput pmOutput hpremises hsemantics
  rcases hsemantics with ⟨input, rfl, rfl, rfl⟩
  have hinput : Holds numRanks .replicated input.sm input.pm :=
    by simpa [PremisesHold] using hpremises
  constructor
  · simpa [Holds] using hinput.1
  · intro tensor htensor
    simp only [List.mem_map] at htensor
    rcases htensor with ⟨source, hsource, rfl⟩
    rw [hinput.2 source hsource]

/-- Semantic-library theorem for the faithful `FW_contiguous = tensorId` denotation. -/
theorem fw_contiguous_equal :
    RuleHolds [.equal] .equal (UnaryMapSemantics fw_contiguous) :=
  unaryMap_equal fw_contiguous

/-- Semantic-library theorem for applying `FW_contiguous` to replicated values. -/
theorem fw_contiguous_replicated :
    RuleHolds [.replicated] .replicated (UnaryMapSemantics fw_contiguous) :=
  unaryMap_replicated fw_contiguous

/-- A certificate node whose relation claim is already accepted by the kernel. -/
structure CertifiedRelation (numRanks : Nat) where
  relation : Relation
  sm : Tensor
  pm : List Tensor
  holds : Holds numRanks relation sm pm

def CertifiedRelation.toRelatedInput {numRanks : Nat}
    (certificate : CertifiedRelation numRanks) : RelatedInput where
  sm := certificate.sm
  pm := certificate.pm

theorem certifiedPremisesHold {numRanks : Nat}
    (premises : List (CertifiedRelation numRanks)) :
    PremisesHold numRanks (premises.map (·.relation))
      (premises.map (·.toRelatedInput)) := by
  unfold PremisesHold
  induction premises with
  | nil => exact .nil
  | cons certificate rest ih =>
      exact .cons certificate.holds ih

/-- Compose one certificate DAG rule node.

The theorem constant `rule`, exact relation vector, and actual semantic reduction
proof are all arguments checked by Lean. A forged theorem name or mismatched
premise/output relation therefore fails elaboration. -/
def applyRule {numRanks : Nat} {inputRelations : List Relation}
    {outputRelation : Relation}
    {semantics : List RelatedInput → Tensor → List Tensor → Prop}
    (rule : RuleHolds inputRelations outputRelation semantics)
    (premises : List (CertifiedRelation numRanks))
    (hrelations : premises.map (·.relation) = inputRelations)
    (smOutput : Tensor) (pmOutput : List Tensor)
    (hsemantics : semantics (premises.map (·.toRelatedInput)) smOutput pmOutput) :
    CertifiedRelation numRanks where
  relation := outputRelation
  sm := smOutput
  pm := pmOutput
  holds := by
    apply rule numRanks (premises.map (·.toRelatedInput)) smOutput pmOutput
    · rw [← hrelations]
      exact certifiedPremisesHold premises
    · exact hsemantics

end TrainVerify.Denote.ProofCompiler
