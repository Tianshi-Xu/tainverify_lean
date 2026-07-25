import denote.Denote

namespace TrainVerify.Denote

/-- Tids known to denote the same external input value, with immutable provenance. -/
structure InputValueClass where
  source : String
  tids : List Tid
  deriving Repr, DecidableEq

/-- An initial store respects one generated input value-equivalence class. -/
def InputValueClass.Holds (c : InputValueClass) (store : Store) : Prop :=
  ∀ tid ∈ c.tids, store tid = store (c.tids.headD 0)

/-- Two tids in a respected class denote equal values.

No nonemptiness hypothesis is needed: the two membership hypotheses already witness
that the class is nonempty. -/
theorem InputValueClass.Holds.eq_of_mem {c : InputValueClass} {store : Store}
    (h : c.Holds store) {a b : Tid} (ha : a ∈ c.tids) (hb : b ∈ c.tids) :
    store a = store b := by
  exact (h a ha).trans (h b hb).symm

/-- Every generated input value-equivalence class is respected by the store. -/
def InputValueClassesHold (classes : List InputValueClass) (store : Store) : Prop :=
  ∀ c ∈ classes, c.Holds store

/-- Select a generated class and two of its tids to obtain their value equality. -/
theorem InputValueClassesHold.eq_of_mem {classes : List InputValueClass} {store : Store}
    (h : InputValueClassesHold classes store) {c : InputValueClass}
    (hc : c ∈ classes) {a b : Tid} (ha : a ∈ c.tids) (hb : b ∈ c.tids) :
    store a = store b := by
  exact (h c hc).eq_of_mem ha hb

/-- A constant store satisfies every input value class, so the generated contract is
always satisfiable independently of whether any class happens to be empty. -/
theorem inputValueClassesHold_const (classes : List InputValueClass) (value : Tensor) :
    InputValueClassesHold classes (fun _ => value) := by
  intro c hc tid htid
  rfl

end TrainVerify.Denote
