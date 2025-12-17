import trainverify.core.GraphSpec

open Std

namespace TrainVerify

universe u

variable {α : Type u}

namespace ExecPlanEntry

/-- Run a single execution-plan entry using the provided runtime. -/
@[simp]
def runWith [Semiring α] (entry : ExecPlanEntry) (rt : Runtime α)
    (st : Store α) : Store α :=
  rt.runNode entry.node st

end ExecPlanEntry

/-- Fold a runtime across a list of execution-plan entries. -/
def runExecPlan [Semiring α] (rt : Runtime α)
    (plan : List ExecPlanEntry) (st : Store α) : Store α :=
  plan.foldl (fun acc entry => ExecPlanEntry.runWith entry rt acc) st

/-- Store after executing the first `fuel` entries of `plan`. -/
def execPlanPrefix [Semiring α] (rt : Runtime α)
    (plan : List ExecPlanEntry) (st : Store α) : Nat → Store α
  | 0 => st
  | Nat.succ fuel =>
      match plan with
      | [] => st
      | entry :: rest =>
          let st' := ExecPlanEntry.runWith entry rt st
          execPlanPrefix rt rest st' fuel

@[simp]
theorem execPlanPrefix_zero [Semiring α]
    (rt : Runtime α) (plan : List ExecPlanEntry) (st : Store α) :
    execPlanPrefix rt plan st 0 = st := by
  cases plan <;> rfl

@[simp]
theorem execPlanPrefix_nil_succ [Semiring α]
    (rt : Runtime α) (st : Store α) (fuel : Nat) :
    execPlanPrefix rt [] st (Nat.succ fuel) = st := by
  cases fuel <;> rfl

@[simp]
theorem execPlanPrefix_cons_succ [Semiring α]
    (rt : Runtime α) (entry : ExecPlanEntry) (plan : List ExecPlanEntry)
    (st : Store α) (fuel : Nat) :
    execPlanPrefix rt (entry :: plan) st (fuel + 1) =
      execPlanPrefix rt plan (ExecPlanEntry.runWith entry rt st) fuel := by
  cases fuel <;> rfl

@[simp]
theorem execPlanPrefix_length_zero [Semiring α]
    (rt : Runtime α) (st : Store α) :
    execPlanPrefix rt [] st 0 = st := rfl

/-- Running the full execution plan matches taking its prefix of length `plan.length`. -/
lemma runExecPlan_eq_prefix [Semiring α]
    (rt : Runtime α) (plan : List ExecPlanEntry) (st : Store α) :
    runExecPlan rt plan st = execPlanPrefix rt plan st plan.length := by
  induction plan generalizing st with
  | nil => simp [runExecPlan, execPlanPrefix]
  | cons entry rest ih =>
    simpa [runExecPlan, execPlanPrefix, ExecPlanEntry.runWith, Nat.succ_eq_add_one]
      using ih (ExecPlanEntry.runWith entry rt st)

/-- Store after executing all entries in the plan. -/
def execPlanFinal [Semiring α] (rt : Runtime α)
    (plan : List ExecPlanEntry) (st : Store α) : Store α :=
  execPlanPrefix rt plan st plan.length

@[simp]
theorem execPlanFinal_def [Semiring α]
    (rt : Runtime α) (plan : List ExecPlanEntry) (st : Store α) :
    execPlanFinal rt plan st = runExecPlan rt plan st :=
  (runExecPlan_eq_prefix rt plan st).symm

/-- Snapshot the store before each plan entry executes. -/
def execPlanTrace [Semiring α]
    (rt : Runtime α) : List ExecPlanEntry → Store α → List (Store α)
  | [], st => [st]
  | entry :: rest, st =>
      let st' := ExecPlanEntry.runWith entry rt st
      st :: execPlanTrace rt rest st'

@[simp]
lemma execPlanTrace_length [Semiring α]
    (rt : Runtime α) (plan : List ExecPlanEntry) (st : Store α) :
    (execPlanTrace rt plan st).length = plan.length + 1 := by
  induction plan generalizing st with
  | nil => simp [execPlanTrace]
  | cons entry rest ih =>
      simp [execPlanTrace, ih, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

@[simp]
lemma execPlanTrace_head [Semiring α]
    (rt : Runtime α) (plan : List ExecPlanEntry) (st : Store α) :
    (execPlanTrace rt plan st).head! = st := by
  cases plan <;> simp [execPlanTrace]

/-- One-step expansion of `execPlanPrefix`: running the `(idx)`-th entry advances
the store by `ExecPlanEntry.runWith` of that entry. -/
lemma execPlanPrefix_succ_get [Semiring α]
    (rt : Runtime α) (plan : List ExecPlanEntry) (st : Store α)
    (idx : Nat) (hidx : idx < plan.length) :
    execPlanPrefix rt plan st (idx + 1) =
      ExecPlanEntry.runWith (plan.get ⟨idx, hidx⟩) rt
        (execPlanPrefix rt plan st idx) := by
    classical
    revert st idx
    induction plan with
  | nil =>
      intro st idx hidx
      cases hidx
  | cons entry rest ih =>
      intro st idx hidx
      cases idx with
      | zero =>
          simp [execPlanPrefix]
      | succ idx =>
          have hrest : idx < rest.length := by
            have : Nat.succ idx < Nat.succ rest.length := by
              simpa [List.length_cons] using hidx
            exact Nat.succ_lt_succ_iff.mp this
          have ih' := ih (st := ExecPlanEntry.runWith entry rt st) (idx := idx) hrest
          have hprefix_succ :
              execPlanPrefix rt (entry :: rest) st (Nat.succ idx + 1) =
                execPlanPrefix rt rest (ExecPlanEntry.runWith entry rt st) (idx + 1) := by
            simp [execPlanPrefix, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc]
          have hprefix :
              execPlanPrefix rt (entry :: rest) st (Nat.succ idx) =
                execPlanPrefix rt rest (ExecPlanEntry.runWith entry rt st) idx := by
            simp [execPlanPrefix, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc]
          have hcalc :
              execPlanPrefix rt (entry :: rest) st (Nat.succ idx + 1) =
                ExecPlanEntry.runWith (rest.get ⟨idx, hrest⟩) rt
                  (execPlanPrefix rt (entry :: rest) st (Nat.succ idx)) := by
            simpa [hprefix_succ, hprefix] using ih'
          have hget :
              (entry :: rest).get ⟨Nat.succ idx, hidx⟩ =
                rest.get ⟨idx, hrest⟩ := by
            simpa [List.get, Nat.succ_eq_add_one] using
              List.get_cons_succ (xs := rest) (x := entry)
                ⟨idx, hrest⟩
          simpa [Nat.succ_eq_add_one, hget] using hcalc

end TrainVerify
