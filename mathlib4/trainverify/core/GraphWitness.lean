import trainverify.core.ExecPlan
import trainverify.core.Lemmas

open Std

namespace TrainVerify

universe u

variable {α : Type u}

/-- Execution-plan state tracks a concrete plan together with its initial store. -/
structure ExecPlanState (α : Type u) where
  plan : List ExecPlanEntry
  init : Store α := {}
  deriving Repr

namespace ExecPlanState

variable [Semiring α]

/-- Store produced after running the first `fuel` entries under runtime `rt`. -/
def prefixStore (state : ExecPlanState α) (rt : Runtime α)
    (fuel : Nat) : Store α :=
  execPlanPrefix rt state.plan state.init fuel

@[simp]
lemma prefixStore_zero (state : ExecPlanState α) (rt : Runtime α) :
    state.prefixStore rt 0 = state.init := by
  simp [prefixStore, execPlanPrefix]

/-- Store produced by replaying the plan fully under runtime `rt`. -/
def finalStore (state : ExecPlanState α) (rt : Runtime α) : Store α :=
  execPlanFinal rt state.plan state.init

@[simp]
lemma finalStore_eq_prefix (state : ExecPlanState α) (rt : Runtime α) :
    state.finalStore rt = state.prefixStore rt state.plan.length := by
  simp [finalStore, prefixStore, execPlanFinal]

/-- Trace of prefix stores recorded during execution under `rt`. -/
def trace (state : ExecPlanState α) (rt : Runtime α) : List (Store α) :=
  execPlanTrace rt state.plan state.init

/-- Fetch the execution-plan entry at index `idx`. -/
def entry (state : ExecPlanState α) (idx : Fin state.plan.length) : ExecPlanEntry :=
  state.plan.get idx

/-- Node scheduled at index `idx`. -/
def nodeAt (state : ExecPlanState α) (idx : Fin state.plan.length) : Node :=
  (state.entry idx).node

/-- Store directly before executing the entry at index `idx`. -/
def storeBefore (state : ExecPlanState α) (rt : Runtime α)
    (idx : Fin state.plan.length) : Store α :=
  state.prefixStore rt idx.val

/-- Store directly after executing the entry at index `idx`. -/
def storeAfter (state : ExecPlanState α) (rt : Runtime α)
    (idx : Fin state.plan.length) : Store α :=
  state.prefixStore rt (idx.val + 1)

@[simp]
lemma storeAfter_eq_runNode (state : ExecPlanState α) (rt : Runtime α)
    (idx : Fin state.plan.length) :
    state.storeAfter rt idx =
      rt.runNode (state.nodeAt idx) (state.storeBefore rt idx) := by
  classical
  have := _root_.TrainVerify.execPlanPrefix_succ_get (rt := rt) (plan := state.plan)
    (st := state.init) (idx := idx.val) (hidx := idx.is_lt)
  simpa [storeAfter, storeBefore, prefixStore, nodeAt, entry]
    using this

end ExecPlanState

section

variable [Semiring α]

/-- Witness that every plan entry makes progress under the standard runtime. -/
def GraphExecWitness (env : Env α)
    (shapes : ShapeMap) (inits : InitMap)
    (state : ExecPlanState α) : Prop :=
  ∀ idx : Fin state.plan.length,
    NodeProgress env shapes inits (state.nodeAt idx)
      (state.storeBefore (Runtime.mkStandard env shapes inits) idx)

/-- Witness that two execution plans agree on all shared tensors at termination. -/
structure GraphEquivWitness (env : Env α)
  (sharedTids : List Nat)
  (smShapes : ShapeMap) (smInits : InitMap)
  (pmShapes : ShapeMap) (pmInits : InitMap)
  (smState pmState : ExecPlanState α) : Prop where
  smWitness : GraphExecWitness env smShapes smInits smState
  pmWitness : GraphExecWitness env pmShapes pmInits pmState
  sharedFinal :
    ∀ tid, List.Mem tid sharedTids →
      (smState.finalStore (Runtime.mkStandard env smShapes smInits)).getD tid [] =
      (pmState.finalStore (Runtime.mkStandard env pmShapes pmInits)).getD tid []

end

namespace GraphEquivWitness

variable [Semiring α]

lemma sharedTensor_eq {env : Env α} {shared : List Nat}
  {smShapes : ShapeMap} {smInits : InitMap}
  {pmShapes : ShapeMap} {pmInits : InitMap}
  {smState pmState : ExecPlanState α}
  (w : GraphEquivWitness (env := env) (sharedTids := shared)
      (smShapes := smShapes) (smInits := smInits)
      (pmShapes := pmShapes) (pmInits := pmInits)
      smState pmState)
    {tid : Nat} (h : List.Mem tid shared) :
    (smState.finalStore (Runtime.mkStandard env smShapes smInits)).getD tid [] =
    (pmState.finalStore (Runtime.mkStandard env pmShapes pmInits)).getD tid [] :=
  w.sharedFinal tid h

end GraphEquivWitness

end TrainVerify
