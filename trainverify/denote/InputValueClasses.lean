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

/-- Every generated input value-equivalence class is respected by the store. -/
def InputValueClassesHold (classes : List InputValueClass) (store : Store) : Prop :=
  ∀ c ∈ classes, c.Holds store

end TrainVerify.Denote
