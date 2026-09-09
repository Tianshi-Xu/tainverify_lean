import denote.SourceInitialInputRead

/-!
Generic value transport to the SAME final Store of the original successful
`runWithInputs`. The exact request split retains the complete source evaluator
and request order. Schedule output uniqueness supplies output nonoverwrite;
explicit read-ID nonwrites cover both the selected node and its entire suffix.

The universal `hstep` and `hext` laws are library parameters to instantiate with
closed operator lemmas, not additional value hypotheses for actual entry callers.
No operator-specific semantics or alternate evaluator is introduced here.
-/
namespace TrainVerify.Denote.SourceValueRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Transport a successful selected node's value equation to the original final
Store. Step success is extracted from the run, rather than assumed separately. -/
theorem node_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (out : Tid) (readIDs : List Tid) (eval : Store → Tensor) (s t : Store)
    (hsplit : requests = before ++ (n, none) :: after)
    (hout : out ∈ n.outs)
    (hreads : ∀ tid ∈ readIDs, ∀ row ∈ (n, none) :: after, tid ∉ row.1.outs)
    (hstep : ∀ a b : Store,
      stepWithInputs g (scope n) (peer n) a n none = some b → b out = eval a)
    (hext : ∀ a b : Store, (∀ tid ∈ readIDs, a tid = b tid) → eval a = eval b)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t out = eval t := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some t at hrun
  split at hrun
  · rename_i hschedule
    have hfresh : ∀ row ∈ after, out ∉ row.1.outs :=
      SourceInitialInputRead.inputSchedule_not_written_after nodes requests before after
        (n, none) out hschedule hsplit hout
    rw [hsplit, SourceScopedPrefix.runUsing_append] at hrun
    cases hb : runUsing
        (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
        before (some s) with
    | none =>
      rw [hb, runUsing_none] at hrun
      contradiction
    | some middle =>
      rw [hb] at hrun
      -- Read liveness spans the selected step too, not only the strict suffix.
      have hreadsFinal : ∀ tid ∈ readIDs, middle tid = t tid := by
        intro tid htid
        exact (SourceScopedPrefix.frame g scope peer ((n, none) :: after) middle t
          tid (hreads tid htid) hrun).symm
      change runUsing
        (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
        after (stepWithInputs g (scope n) (peer n) middle n none) = some t at hrun
      cases hselected : stepWithInputs g (scope n) (peer n) middle n none with
      | none =>
        rw [hselected, runUsing_none] at hrun
        contradiction
      | some stepped =>
        rw [hselected] at hrun
        calc
          t out = stepped out :=
            SourceScopedPrefix.frame g scope peer after stepped t out hfresh hrun
          _ = eval middle := hstep middle stepped hselected
          _ = eval t := hext middle t hreadsFinal
  · contradiction

#print axioms node_value_of_split
end
end TrainVerify.Denote.SourceValueRead
