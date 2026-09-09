import denote.SourceInitialParameterSpecs
import denote.SourceScopedPrefix

namespace TrainVerify.Denote.SourceParameterFrame
open SourceInitialParameterSpecs SourceScopedEval
set_option maxHeartbeats 500000

/-- The source parameter key, independent of all tensor values. -/
def smTid : Spec → Tid
  | .sharded tid _ _ _ _ => tid
  | .replicated tid _ _ => tid

/-- Every PM shard/copy key, in the original metadata order. -/
def pmTids : Spec → List Tid
  | .sharded _ tids _ _ _ => tids
  | .replicated _ tids _ => tids

/-- Pure finite metadata: neither original request stream writes this spec's
SM key or any of its PM keys. In particular, output uniqueness alone is not
this condition. Callers can kernel-decide it on their actual flattened outs. -/
def SpecUnwritten (spec : Spec) (smWritten pmWritten : List Tid) : Prop :=
  smTid spec ∉ smWritten ∧ ∀ tid ∈ pmTids spec, tid ∉ pmWritten

instance (spec : Spec) (smWritten pmWritten : List Tid) :
    Decidable (SpecUnwritten spec smWritten pmWritten) := by
  unfold SpecUnwritten
  infer_instance

/-- Turn flattened output metadata into the exact per-request frame premise. -/
theorem not_written_rows (requests : List InputRequest) (tid : Tid)
    (h : tid ∉ requests.flatMap (fun row => row.1.outs)) :
    ∀ row ∈ requests, tid ∉ row.1.outs := by
  intro row hr ht
  exact h (List.mem_flatMap.mpr ⟨row, hr, ht⟩)

/-- Frame the same successful checked run, including input-port writes. The
schedule check is discharged by that run's success, not assumed separately. -/
theorem runWithInputs_frame (g : GraphDecl)
    (scope : NodeDecl → GroupScopedEval.Request) (peer : NodeDecl → Nat → Tid)
    (nodes : List NodeDecl) (requests : List InputRequest) (s t : Store) (tid : Tid)
    (ht : tid ∉ requests.flatMap (fun row => row.1.outs))
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t tid = s tid := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some t at hrun
  split at hrun
  · exact SourceScopedPrefix.frame g scope peer requests s t tid
      (not_written_rows requests tid ht) hrun
  · contradiction

/-- Tensor equality at precisely the parameter keys preserves the entire
original value contract: SM shape, ordered chunk map, or every replicated copy.
This helper's equalities are derived from successful runs in the public theorem. -/
theorem values_frame (spec : Spec) (s p s' p' : Store)
    (hs : s' (smTid spec) = s (smTid spec))
    (hp : ∀ tid ∈ pmTids spec, p' tid = p tid)
    (h : spec.values s p) : spec.values s' p' := by
  cases spec with
  | sharded tid tids dim full shard =>
      change s' tid = s tid at hs
      change ∀ t ∈ tids, p' t = p t at hp
      change (s' tid).shape = full ∧
        tids.map p' = List.ofFn (fun r : Fin tids.length =>
          chunkPrimDimN dim tids.length r.val (s' tid))
      refine ⟨(congrArg Tensor.shape hs).trans h.1, ?_⟩
      have hm : tids.map p' = tids.map p := List.map_congr_left hp
      rw [hm, hs]
      exact h.2
  | replicated tid tids shape =>
      change s' tid = s tid at hs
      change ∀ t ∈ tids, p' t = p t at hp
      change (s' tid).shape = shape ∧ ∀ t ∈ tids, p' t = s' tid
      refine ⟨(congrArg Tensor.shape hs).trans h.1, ?_⟩
      intro t ht
      exact (hp t ht).trans ((h.2 t ht).trans hs.symm)

/-- Specialize the shared unwritten-key frame to one metadata entry. -/
theorem values_frame_of_unwritten (spec : Spec) (smWritten pmWritten : List Tid)
    (s p s' p' : Store)
    (hsm : ∀ tid, tid ∉ smWritten → s' tid = s tid)
    (hpm : ∀ tid, tid ∉ pmWritten → p' tid = p tid)
    (hu : SpecUnwritten spec smWritten pmWritten)
    (h : spec.values s p) : spec.values s' p' :=
  values_frame spec s p s' p' (hsm _ hu.1)
    (fun tid ht => hpm tid (hu.2 tid ht)) h

/-- Preserve the exact right-associated `All`, including its singleton case
with no trailing True. The two execution-frame proofs are shared by all specs. -/
theorem all_values_frame (specs : List Spec) (smWritten pmWritten : List Tid)
    (s p s' p' : Store)
    (hsm : ∀ tid, tid ∉ smWritten → s' tid = s tid)
    (hpm : ∀ tid, tid ∉ pmWritten → p' tid = p tid)
    (hu : All (fun spec => SpecUnwritten spec smWritten pmWritten) specs)
    (h : All (fun spec => spec.values s p) specs) :
    All (fun spec => spec.values s' p') specs := by
  induction specs with
  | nil => exact True.intro
  | cons x xs ih =>
      cases xs with
      | nil => exact values_frame_of_unwritten x smWritten pmWritten s p s' p' hsm hpm hu h
      | cons y ys =>
          exact ⟨values_frame_of_unwritten x smWritten pmWritten s p s' p' hsm hpm hu.1 h.1,
            ih hu.2 h.2⟩

/-- Complete initial-parameter values hold at the SAME final stores returned
by the two original successful checked request streams. Only structural
nonwrites are additional premises; no final value/relation is assumed.

Parent instantiation (all names below stand for the parent's existing objects):
```
have hu : All (fun spec => SpecUnwritten spec
    (smRequests.flatMap (fun row => row.1.outs))
    (pmRequests.flatMap (fun row => row.1.outs))) parameterSpecs := by decide
exact all_values_runWithInputs parameterSpecs smGraph pmGraph smScope pmScope
  smPeer pmPeer smNodes pmNodes smRequests pmRequests
  initSM initPM finalSM finalPM hu hsmRun hpmRun hInitialValues
```
No validity premise is needed to preserve values. To obtain final relations,
apply `SourceInitialParameterSpecs.all_of_values` to the unchanged spec-validity
metadata and this theorem's conclusion. -/
theorem all_values_runWithInputs (specs : List Spec) (smGraph pmGraph : GraphDecl)
    (smScope pmScope : NodeDecl → GroupScopedEval.Request)
    (smPeer pmPeer : NodeDecl → Nat → Tid) (smNodes pmNodes : List NodeDecl)
    (smRequests pmRequests : List InputRequest) (initSM initPM finalSM finalPM : Store)
    (hu : All (fun spec => SpecUnwritten spec
      (smRequests.flatMap (fun row => row.1.outs))
      (pmRequests.flatMap (fun row => row.1.outs))) specs)
    (hsmRun : runWithInputs smGraph smScope smPeer smNodes
      (some smRequests) (some initSM) = some finalSM)
    (hpmRun : runWithInputs pmGraph pmScope pmPeer pmNodes
      (some pmRequests) (some initPM) = some finalPM)
    (hInitialValues : All (fun spec => spec.values initSM initPM) specs) :
    All (fun spec => spec.values finalSM finalPM) specs := by
  apply all_values_frame specs
    (smRequests.flatMap (fun row => row.1.outs))
    (pmRequests.flatMap (fun row => row.1.outs)) initSM initPM finalSM finalPM
    _ _ hu hInitialValues
  · intro tid ht
    exact runWithInputs_frame smGraph smScope smPeer smNodes smRequests
      initSM finalSM tid ht hsmRun
  · intro tid ht
    exact runWithInputs_frame pmGraph pmScope pmPeer pmNodes pmRequests
      initPM finalPM tid ht hpmRun

#print axioms runWithInputs_frame
#print axioms values_frame
#print axioms all_values_frame
#print axioms all_values_runWithInputs
end TrainVerify.Denote.SourceParameterFrame
