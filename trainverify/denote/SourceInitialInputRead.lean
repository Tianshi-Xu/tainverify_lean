import denote.SourceInitialInputs
import Mathlib.Data.List.Nodup

/-!
Uncompiled candidate: final checked-input reads in the original successful
`runWithInputs` Store. No alternate evaluator, Store, or nonoverwrite premise.
The exact request split preserves the loader occurrence and execution order.
-/
namespace TrainVerify.Denote.SourceInitialInputRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- The original schedule's globally unique output TIDs exclude every later
writer of a selected row's output. This helper also accepts the generator's
existing `smInputSchedule_valid` / `pmInputSchedule_valid` certificates. -/
theorem inputSchedule_not_written_after
    (nodes : List NodeDecl) (requests before after : List InputRequest)
    (selected : InputRequest) (tid : Tid)
    (hschedule : InputSchedule nodes requests)
    (hsplit : requests = before ++ selected :: after)
    (hout : tid ∈ selected.1.outs) :
    ∀ row ∈ after, tid ∉ row.1.outs := by
  have huniq := hschedule.2
  rw [← hschedule.1, hsplit] at huniq
  simp only [List.map_append, List.map_cons, List.flatMap_append,
    List.flatMap_cons] at huniq
  have htail : (selected.1.outs ++
      (after.map Prod.fst).flatMap NodeDecl.outs).Nodup :=
    List.Nodup.of_append_right huniq
  have hdis := List.disjoint_of_nodup_append htail
  intro row hrow hwritten
  exact (List.disjoint_left.mp hdis) hout
    (List.mem_flatMap.mpr
      ⟨row.1, List.mem_map.mpr ⟨row, hrow, rfl⟩, hwritten⟩)

/-- Read one feed port in the SAME final Store returned by the original checked
run. Success supplies `InputSchedule`; its Nodup field supplies nonoverwrite.
Call once per loader port, retaining the exact source request list and endpoint
Store used by `SourceInitialInputs.initial_relations_two`. -/
theorem input_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl) (feed : PortFeed)
    (s t : Store) (tid : Tid) (value : Tensor)
    (hsplit : requests = before ++ (n, some feed) :: after)
    (hscope : scope n = .group none) (hc : InputContract n feed)
    (hmem : (tid, value) ∈ feed)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t tid = value := by
  have hschedule : InputSchedule nodes requests := by
    have hcheck := hrun
    change (if InputSchedule nodes requests then
      runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
        requests (some s) else none) = some t at hcheck
    split at hcheck
    · assumption
    · contradiction
  have hout : tid ∈ n.outs := by
    rw [← hc.2.2.2.2.2]
    exact List.mem_map.mpr ⟨(tid, value), hmem, rfl⟩
  exact SourceInitialInputs.input_value_after g scope peer nodes requests before after
    n feed s t tid value hsplit hscope hc hmem
    (inputSchedule_not_written_after nodes requests before after (n, some feed)
      tid hschedule hsplit hout) hrun

#print axioms inputSchedule_not_written_after
#print axioms input_value_of_split
end
end TrainVerify.Denote.SourceInitialInputRead
