import trainverify.core.GraphSpec
import trainverify.core.GraphWitness

open Std

namespace TrainVerify
namespace GraphWitnessPipeline

universe u

variable {α : Type u}

/-- Build an execution-plan state from a plan and optional initial store. -/
def mkState (plan : List ExecPlanEntry) (init : Store α := {}) : ExecPlanState α :=
  { plan, init }

@[simp]
lemma mkState_plan (plan : List ExecPlanEntry) (init : Store α := {}) :
    (mkState (α := α) plan init).plan = plan := rfl

@[simp]
lemma mkState_init (plan : List ExecPlanEntry) (init : Store α := {}) :
    (mkState (α := α) plan init).init = init := rfl

/-- Package an execution-plan state together with its progress witness. -/
structure ExecPlanWitness (env : Env α) [Semiring α]
    (shapes : ShapeMap) (inits : InitMap) where
  state : ExecPlanState α
  witness : GraphExecWitness env shapes inits state

namespace ExecPlanWitness

variable [Semiring α] {env : Env α}
variable {shapes : ShapeMap} {inits : InitMap}

/-- Convenience constructor turning a plan plus per-node progress proof into a witness package. -/
def ofPlan (plan : List ExecPlanEntry) (init : Store α := {})
    (h : GraphExecWitness env shapes inits (mkState (α := α) plan init)) :
    ExecPlanWitness env shapes inits where
  state := mkState (α := α) plan init
  witness := h

@[simp]
lemma state_plan (pkg : ExecPlanWitness env shapes inits) :
    pkg.state.plan = pkg.state.plan := rfl

@[simp]
lemma witness_apply (pkg : ExecPlanWitness env shapes inits) :
    pkg.witness = pkg.witness := rfl

end ExecPlanWitness

/-- Bundle the SM and PM execution witnesses. -/
structure WitnessPair (env : Env α) [Semiring α]
    (smShapes : ShapeMap) (smInits : InitMap)
    (pmShapes : ShapeMap) (pmInits : InitMap) where
  sm : ExecPlanWitness env smShapes smInits
  pm : ExecPlanWitness env pmShapes pmInits

namespace WitnessPair

variable [Semiring α] {env : Env α}
variable {smShapes : ShapeMap} {smInits : InitMap}
variable {pmShapes : ShapeMap} {pmInits : InitMap}

/-- Build a graph-equivalence witness once shared tensor equality is supplied. -/
def toEquiv (sharedTids : List Nat)
    (pair : WitnessPair env smShapes smInits pmShapes pmInits)
    (h : ∀ tid, tid ∈ sharedTids →
      (pair.sm.state.finalStore (Runtime.mkStandard env smShapes smInits)).getD tid [] =
      (pair.pm.state.finalStore (Runtime.mkStandard env pmShapes pmInits)).getD tid []) :
    GraphEquivWitness env sharedTids smShapes smInits pmShapes pmInits
      pair.sm.state pair.pm.state where
  smWitness := pair.sm.witness
  pmWitness := pair.pm.witness
  sharedFinal := h

/-- Deduce observable equality from shared tensor equality plus witness pair. -/
lemma outputsAgree (pair : WitnessPair env smShapes smInits pmShapes pmInits)
    (sharedTids : List Nat) (obsTid : Nat)
    (hshared : ∀ tid, tid ∈ sharedTids →
      (pair.sm.state.finalStore (Runtime.mkStandard env smShapes smInits)).getD tid [] =
      (pair.pm.state.finalStore (Runtime.mkStandard env pmShapes pmInits)).getD tid [])
    (hObs : obsTid ∈ sharedTids)
    {smOut pmOut : Mat α}
    (hSm : (pair.sm.state.finalStore (Runtime.mkStandard env smShapes smInits)).getD obsTid [] = smOut)
    (hPm : (pair.pm.state.finalStore (Runtime.mkStandard env pmShapes pmInits)).getD obsTid [] = pmOut) :
    smOut = pmOut := by
  have hEquiv := pair.toEquiv sharedTids hshared
  have hstores := GraphEquivWitness.sharedTensor_eq
    (env := env) (shared := sharedTids)
    (smShapes := smShapes) (smInits := smInits)
    (pmShapes := pmShapes) (pmInits := pmInits)
    (smState := pair.sm.state) (pmState := pair.pm.state)
    hEquiv hObs
  calc
    smOut = (pair.sm.state.finalStore (Runtime.mkStandard env smShapes smInits)).getD obsTid [] :=
      by simpa using hSm.symm
    _ = (pair.pm.state.finalStore (Runtime.mkStandard env pmShapes pmInits)).getD obsTid [] :=
      hstores
    _ = pmOut := by simpa using hPm

end WitnessPair

end GraphWitnessPipeline
end TrainVerify
