import denote.SourceInitialParameters

namespace TrainVerify.Denote.SourceInitialParameterSpecs
open RelationCompiler
noncomputable section
set_option maxHeartbeats 500000

/-- Source-derived shape/layout data; no observed values or proof tokens. -/
inductive Spec where
  | sharded (tid : Tid) (tids : List Tid) (dim : Nat) (full shard : Shape)
  | replicated (tid : Tid) (tids : List Tid) (shape : Shape)
  deriving DecidableEq

/-- Exactly the original explicit shape/slice or copy premises. -/
def Spec.values (spec : Spec) (s p : Store) : Prop :=
  match spec with
  | .sharded tid tids dim full _ =>
      (s tid).shape = full ∧ tids.map p = List.ofFn (fun r : Fin tids.length =>
        chunkPrimDimN dim tids.length r.val (s tid))
  | .replicated tid tids shape =>
      (s tid).shape = shape ∧ ∀ t ∈ tids, p t = s tid

def Spec.fact : Spec → RelationFact
  | .sharded tid tids dim full shard => .sharded tid tids dim full shard
  | .replicated tid tids shape => .replicated tid tids shape

def Spec.valid : Spec → Prop
  | .sharded _ tids dim full shard =>
      0 < tids.length ∧ dim < shard.length ∧
      full = shard.set dim (shard.getD dim 0 * tids.length)
  | .replicated _ tids _ => tids ≠ []

instance (spec : Spec) : Decidable spec.valid := by
  cases spec <;> unfold Spec.valid <;> infer_instance

/-- A right-associated conjunction without an extra trailing True. Its reduction
is definitionally the original explicitly generated conjunction, in order. -/
def All {α : Type} (pred : α → Prop) : List α → Prop
  | [] => True
  | [x] => pred x
  | x :: y :: xs => pred x ∧ All pred (y :: xs)

instance {α : Type} (pred : α → Prop) [DecidablePred pred] (xs : List α) :
    Decidable (All pred xs) := by
  induction xs with
  | nil => exact isTrue True.intro
  | cons x xs ih =>
      cases xs with
      | nil => exact inferInstanceAs (Decidable (pred x))
      | cons y ys => exact @instDecidableAnd (pred x) (All pred (y :: ys)) _ ih

theorem Spec.of_values (spec : Spec) (s p : Store)
    (hv : spec.valid) (h : spec.values s p) : spec.fact.Holds s p := by
  cases spec with
  | sharded tid tids dim full shard =>
      exact SourceInitialParameters.sharded_of_exact_slices s p tid tids dim tids.length
        full shard hv.1 hv.2.1 h.1 hv.2.2 h.2
  | replicated tid tids shape =>
      exact SourceInitialParameters.replicated_of_exact_values s p tid tids shape hv h.1 h.2

theorem all_of_values (specs : List Spec) (s p : Store)
    (hv : All Spec.valid specs) (h : All (fun spec => spec.values s p) specs) :
    All (fun spec => spec.fact.Holds s p) specs := by
  induction specs with
  | nil => exact True.intro
  | cons x xs ih =>
      cases xs with
      | nil => exact x.of_values s p hv h
      | cons y ys => exact ⟨x.of_values s p hv.1 h.1, ih hv.2 h.2⟩

#print axioms Spec.of_values
#print axioms all_of_values
end
end TrainVerify.Denote.SourceInitialParameterSpecs
