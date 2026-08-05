import denote.ProofCompilerRelation

namespace TrainVerify.Denote.ProofCompiler.Tests

open TrainVerify.Denote

variable (sm a b : Tensor)

example : Holds 1 .equal sm [sm] := by
  rfl

example (h : Holds 2 .replicated sm [a, b]) : a = sm ∧ b = sm := by
  exact ⟨h.2 a (by simp), h.2 b (by simp)⟩

example : ¬ Holds 2 .replicated sm [sm] := by
  simp [Holds]

example (dim : Nat) :
    Holds 2 (.contiguousShard dim 2) sm [a, b] ↔
      sm = allGatherPrimDimN dim 2 0 [a, b] := by
  simp [Holds]

example (dim : Nat) :
    Holds 2 (.contiguousShard dim 1) sm [a] ↔
      sm = allGatherPrimDimN dim 1 0 [a] := by
  simp [Holds]

/-- These are semantic rule theorems: the output tensors are fixed by
    `UnaryMapSemantics`, not selected by a symbolic rule name. -/
example (f : Tensor → Tensor) :
    RuleHolds [.equal] .equal (UnaryMapSemantics f) :=
  unaryMap_equal f

example (f : Tensor → Tensor) :
    RuleHolds [.replicated] .replicated (UnaryMapSemantics f) :=
  unaryMap_replicated f

def equalSeed (value : Tensor) : CertifiedRelation 1 where
  relation := .equal
  sm := value
  pm := [value]
  holds := rfl

def applyEqualMap (f : Tensor → Tensor) (value : Tensor) : CertifiedRelation 1 :=
  applyRule (unaryMap_equal f) [equalSeed value] rfl (f value) [f value] (by
    refine ⟨(equalSeed value).toRelatedInput, ?_, rfl, ?_⟩
    · rfl
    · rfl)

example (f : Tensor → Tensor) (value : Tensor) :
    Holds 1 .equal (f value) [f value] :=
  (applyEqualMap f value).holds

def replicatedSeed2 (value : Tensor) : CertifiedRelation 2 where
  relation := .replicated
  sm := value
  pm := [value, value]
  holds := by simp [Holds]

def applyReplicatedMap2 (f : Tensor → Tensor) (value : Tensor) : CertifiedRelation 2 :=
  applyRule (unaryMap_replicated f) [replicatedSeed2 value] rfl
    (f value) [f value, f value] (by
      refine ⟨(replicatedSeed2 value).toRelatedInput, ?_, rfl, ?_⟩
      · rfl
      · rfl)

example (f : Tensor → Tensor) (value : Tensor) :
    Holds 2 .replicated (f value) [f value, f value] :=
  (applyReplicatedMap2 f value).holds

def unseenSmGraph : GraphDecl where
  numRanks := 1
  nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [101], outs := [102] }]

def unseenPmGraph : GraphDecl where
  numRanks := 1
  nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [201], outs := [202] }]

example (init : Store) :
    denoteGraph unseenSmGraph init 102 = fw_contiguous (init 101) := by
  rfl

example (init : Store) :
    denoteGraph unseenPmGraph init 202 = fw_contiguous (init 201) := by
  rfl

theorem unseenOneNodeCertificate (initSM initPM : Store)
    (seed : Holds 1 .equal (initSM 101) [initPM 201]) :
    Holds 1 .equal
      (denoteGraph unseenSmGraph initSM 102)
      [denoteGraph unseenPmGraph initPM 202] := by
  let certifiedSeed : CertifiedRelation 1 :=
    { relation := .equal, sm := initSM 101, pm := [initPM 201], holds := seed }
  have semanticStep : UnaryMapSemantics fw_contiguous
      [certifiedSeed.toRelatedInput]
      (denoteGraph unseenSmGraph initSM 102)
      [denoteGraph unseenPmGraph initPM 202] := by
    refine ⟨certifiedSeed.toRelatedInput, rfl, ?_, ?_⟩
    · rfl
    · rfl
  exact (applyRule fw_contiguous_equal [certifiedSeed] rfl
    (denoteGraph unseenSmGraph initSM 102)
    [denoteGraph unseenPmGraph initPM 202] semanticStep).holds

#print axioms unaryMap_equal
#print axioms unaryMap_replicated
#print axioms unseenOneNodeCertificate

end TrainVerify.Denote.ProofCompiler.Tests
