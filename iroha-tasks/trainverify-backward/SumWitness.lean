import denote.SourceBWSumRead

/-!
Single-node satisfiable caller for the ordinary source BW_sum read. The original
checked run succeeds on an explicit seed of 3 and a nonsymmetric [2,3,5] primal.
The caller uses the new split theorem, not an assumed output/shape equation.
Every in-bounds output value is 3, with no normalization by the primal size.

The parent checks this caller serially with its helper and audits every theorem.
No native_decide is used; source/runtime seed authentication is a separate gate.
-/
namespace TrainVerify.Denote.SourceBWSumReadWitness
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

def selected : NodeDecl :=
  { rank := 0, op := "OpName.BW_sum", ins := [10, 20], outs := [50], params := [] }
def nodes : List NodeDecl := [selected]
def requests : List InputRequest := [(selected, none)]
def scope : NodeDecl → GroupScopedEval.Request := fun _ => .global
def peer : NodeDecl → Nat → Tid := fun _ _ => 0
def finalStore (g : GraphDecl) (s : Store) : Store := applyNode g s selected

theorem schedule_valid : InputSchedule nodes requests := by decide

theorem run_success (g : GraphDecl) (s : Store) :
    runWithInputs g scope peer nodes (some requests) (some s) = some (finalStore g s) := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some (finalStore g s)
  rw [if_pos schedule_valid]
  change stepWithInputs g (scope selected) (peer selected) s selected none = _
  rw [stepWithInputs_ordinary g (scope selected) (peer selected) s selected (by decide)]
  exact step_global g (peer selected) s selected (by decide)

-- The only dynamic premise is the original successful checked run.
theorem caller_read (g : GraphDecl) (s t : Store)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t 50 = bw_sum (t 10) (t 20) := by
  exact SourceBWSumRead.bw_sum_value_of_split g scope peer nodes requests
    [] [] selected 0 10 20 50 s t rfl rfl rfl (by decide) (by decide) hrun

theorem sum_read (g : GraphDecl) (s : Store) :
    (finalStore g s) 50 = bw_sum ((finalStore g s) 10) ((finalStore g s) 20) :=
  caller_read g s (finalStore g s) (run_success g s)

def seed : Tensor := { shape := [1], val := fun _ => 3 }
def primal : Tensor := { shape := [2, 3, 5], val := fun _ => 2 }
def initial : Store := fun tid =>
  if tid = 10 then seed else if tid = 20 then primal else zeroTensor []

theorem initial_seed_value : valAt (initial 10) 0 = 3 := by
  rw [valAt_of_lt (initial 10) 0 (by decide)]
  rfl

theorem seed_preserved (g : GraphDecl) : (finalStore g initial) 10 = seed := by
  change applyNode g initial selected 10 = seed
  rw [applyNode_eq_of_not_mem_outs g initial selected 10 (by decide)]
  rfl

theorem primal_preserved (g : GraphDecl) : (finalStore g initial) 20 = primal := by
  change applyNode g initial selected 20 = primal
  rw [applyNode_eq_of_not_mem_outs g initial selected 20 (by decide)]
  rfl

theorem output_shape (g : GraphDecl) : ((finalStore g initial) 50).shape = [2, 3, 5] := by
  rw [sum_read g initial, bw_sum_shape, primal_preserved g]
  rfl

theorem output_value (g : GraphDecl) (idx : Nat) (hidx : idx < prodShape [2, 3, 5]) :
    valAt ((finalStore g initial) 50) idx = 3 := by
  rw [sum_read g initial, seed_preserved g, primal_preserved g]
  rw [bw_sum_valAt_of_lt seed primal idx hidx]
  exact initial_seed_value

/-- All caller conditions are satisfiable with a non-unit seed, and the original
run's actual final output has the concrete shape and all in-bounds values. -/
theorem caller_nonvacuous (g : GraphDecl) :
    ∃ s t : Store,
      (s 10).shape = [1] ∧ (s 20).shape = [2, 3, 5] ∧
      valAt (s 10) 0 = 3 ∧ valAt (s 20) 0 = 2 ∧
      runWithInputs g scope peer nodes (some requests) (some s) = some t ∧
      valAt (t 10) 0 = 3 ∧
      t 50 = bw_sum (t 10) (t 20) ∧
      (t 50).shape = [2, 3, 5] ∧
      (∀ idx : Nat, idx < prodShape [2, 3, 5] → valAt (t 50) idx = 3) := by
  refine ⟨initial, finalStore g initial, rfl, rfl, initial_seed_value, ?_,
    run_success g initial, ?_, sum_read g initial, output_shape g, output_value g⟩
  · rw [valAt_of_lt (initial 20) 0 (by decide)]
    rfl
  · rw [seed_preserved g]
    exact initial_seed_value

#print axioms schedule_valid
#print axioms run_success
#print axioms caller_read
#print axioms sum_read
#print axioms initial_seed_value
#print axioms seed_preserved
#print axioms primal_preserved
#print axioms output_shape
#print axioms output_value
#print axioms caller_nonvacuous
end
end TrainVerify.Denote.SourceBWSumReadWitness
