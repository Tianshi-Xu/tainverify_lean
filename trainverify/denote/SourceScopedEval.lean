import denote.AllToAllSourceFaithful

namespace TrainVerify.Denote.SourceScopedEval
set_option maxHeartbeats 500000
noncomputable section

/-- Explicit global requests never accept collectives or WRED. -/
def ordinary (op : String) : Bool :=
  !GroupScopedEval.supported op && op != "OpName.WRED" && op != "OpName.CROSS_DP_WRED"

/-- Single-output SUM domain; the legacy K-output shape inference is not used. -/
def WredContract (rs : List Nat) (peer : Nat → Tid) (s : Store) (n : NodeDecl) : Prop :=
  n.op = "OpName.CROSS_DP_WRED" ∧ n.params = [] ∧ n.outs.length = 1 ∧
  n.ins = rs.map peer ∧ n.ins ≠ [] ∧
  ∀ tid ∈ n.ins, (s tid).shape = (s (n.ins.headD 0)).shape

noncomputable instance (rs : List Nat) (peer : Nat → Tid) (s : Store) (n : NodeDecl) :
    Decidable (WredContract rs peer s n) := Classical.propDecidable _

def wredStep (g : GraphDecl) (ranks : Option (List Nat)) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) : Option Store :=
  match ranks with
  | none => none
  | some rs => if GroupScopedEval.WellFormed g.numRanks n.rank rs ∧ WredContract rs peer s n
      then some (applyNode g s n) else none

/-- One world-store dispatcher with explicitly checked source collectives. -/
def step (g : GraphDecl) (request : GroupScopedEval.Request) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) : Option Store :=
  match request with
  | .global => if ordinary n.op then some (applyNode g s n) else none
  | .group rs => if n.op = "OpName.AllToAllPrim" then
      (AllToAllSourceFaithful.step g rs peer s n).toOption
    else if n.op = "OpName.CROSS_DP_WRED" then wredStep g rs peer s n
    else GroupScopedEval.step g (.group rs) s n

theorem step_allToAll (g : GraphDecl) (rs : Option (List Nat)) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (h : n.op = "OpName.AllToAllPrim") :
    step g (.group rs) peer s n = (AllToAllSourceFaithful.step g rs peer s n).toOption := by
  simp only [step, h, ↓reduceIte]

theorem step_group (g : GraphDecl) (rs : Option (List Nat)) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (h : n.op ≠ "OpName.AllToAllPrim")
    (hw : n.op ≠ "OpName.CROSS_DP_WRED") :
    step g (.group rs) peer s n = GroupScopedEval.step g (.group rs) s n := by
  simp only [step, h, hw, ↓reduceIte]

theorem step_wred (g : GraphDecl) (rs : Option (List Nat)) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (h : n.op = "OpName.CROSS_DP_WRED") :
    step g (.group rs) peer s n = wredStep g rs peer s n := by
  simp only [step, h, show "OpName.CROSS_DP_WRED" ≠ "OpName.AllToAllPrim" by decide, ↓reduceIte]

theorem wred_output (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s : Store) (rank : Nat) (ins : List Tid) (out : Tid)
    (hw : GroupScopedEval.WellFormed g.numRanks rank rs)
    (hc : WredContract rs peer s {rank := rank, op := "OpName.CROSS_DP_WRED", ins := ins, outs := [out]}) :
    ∃ s', step g (.group (some rs)) peer s
      {rank := rank, op := "OpName.CROSS_DP_WRED", ins := ins, outs := [out]} = some s' ∧
      s' out = cross_dp_wred (ins.map s) ∧
      (∀ tid, tid ∉ ([out] : List Tid) → s' tid = s tid) := by
  refine ⟨applyNode g s _, ?_, applyNode_cross_dp_wred_out g s rank ins out, ?_⟩
  · rw [step_wred _ _ _ _ _ rfl]
    exact if_pos ⟨hw, hc⟩
  · intro tid ht
    exact applyNode_skip g s _ tid ht

theorem step_global (g : GraphDecl) (peer : Nat → Tid) (s : Store) (n : NodeDecl)
    (h : ordinary n.op = true) : step g .global peer s n = some (applyNode g s n) := by
  simp only [step, h, ↓reduceIte]

/-- Shared single-pass engine for legacy nodes and explicit input requests. -/
def runUsing {α : Type} (advance : α → Store → Option Store)
    (nodes : List α) (init : Option Store) : Option Store :=
  nodes.foldl (fun state n => state.bind (advance n)) init

/-- The complete graph node list is evaluated once, in original order. -/
def run (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl) (init : Option Store) : Option Store :=
  runUsing (fun n s => step g (scope n) (peer n) s n) nodes init

def denote (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (s : Store) : Option Store :=
  run g scope peer g.nodes (some s)

theorem run_cons (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (n : NodeDecl) (ns : List NodeDecl) (s : Store) :
    run g scope peer (n :: ns) (some s) = run g scope peer ns (step g (scope n) (peer n) s n) := rfl

theorem run_none (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (ns : List NodeDecl) : run g scope peer ns none = none := by
  induction ns with
  | nil => rfl
  | cons n ns ih => exact ih

theorem step_skip (g : GraphDecl) (request : GroupScopedEval.Request) (peer : Nat → Tid)
    (s s' : Store) (n : NodeDecl) (tid : Tid) (h : tid ∉ n.outs)
    (hs : step g request peer s n = some s') : s' tid = s tid := by
  cases request with
  | global =>
    simp only [step] at hs
    split at hs
    · cases Option.some.inj hs; exact applyNode_skip g s n tid h
    · contradiction
  | group rs =>
    by_cases hop : n.op = "OpName.AllToAllPrim"
    · rw [step_allToAll _ _ _ _ _ hop] at hs
      unfold AllToAllSourceFaithful.step at hs
      split at hs
      · contradiction
      · split at hs
        · contradiction
        · split at hs
          · split at hs
            · cases Option.some.inj hs
              exact AllToAllSourceFaithful.localStep_skip _ _ _ _ _ _ h
            · contradiction
          · contradiction
    · by_cases hw : n.op = "OpName.CROSS_DP_WRED"
      · rw [step_wred _ _ _ _ _ hw] at hs
        unfold wredStep at hs
        split at hs
        · contradiction
        · split at hs
          · cases Option.some.inj hs; exact applyNode_skip g s n tid h
          · contradiction
      · rw [step_group _ _ _ _ _ hop hw] at hs
        exact GroupScopedEval.step_skip g (.group rs) s s' n tid h hs

theorem run_skip (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl) (s s' : Store) (tid : Tid)
    (h : ∀ n ∈ nodes, tid ∉ n.outs) (hs : run g scope peer nodes (some s) = some s') :
    s' tid = s tid := by
  induction nodes generalizing s with
  | nil => cases Option.some.inj hs; rfl
  | cons n ns ih =>
    rw [run_cons] at hs
    cases he : step g (scope n) (peer n) s n with
    | none => rw [he, run_none] at hs; contradiction
    | some t =>
      rw [he] at hs
      exact (ih t (fun m hm => h m (List.mem_cons_of_mem n hm)) hs).trans
        (step_skip g (scope n) (peer n) s t n tid (h n List.mem_cons_self) he)

theorem run_global (g : GraphDecl) (peer : NodeDecl → Nat → Tid)
    (nodes : List NodeDecl) (s : Store) (h : ∀ n ∈ nodes, ordinary n.op = true) :
    run g (fun _ => .global) peer nodes (some s) = some (nodes.foldl (applyNode g) s) := by
  induction nodes generalizing s with
  | nil => rfl
  | cons n ns ih =>
    rw [run_cons, step_global _ _ _ _ (h n List.mem_cons_self)]
    exact ih _ (fun m hm => h m (List.mem_cons_of_mem n hm))


/-- Ordered mathematical tensors, not a shape/dtype or runtime-observation encoding. -/
abbrev PortFeed := List (Tid × Tensor)

/-- Every scheduled node has an explicit slot; its full declaration is checked. -/
abbrev InputRequest := NodeDecl × Option PortFeed

def InputContract (n : NodeDecl) (feed : PortFeed) : Prop :=
  n.op = "OpName.DATALOADER" ∧ n.ins = [] ∧ n.params = [] ∧
  n.outs ≠ [] ∧ n.outs.Nodup ∧ feed.map Prod.fst = n.outs

instance (n : NodeDecl) (feed : PortFeed) : Decidable (InputContract n feed) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- All supplied ports are written, with no fallback or truncating zip. -/
def checkedInputStep (s : Store) (n : NodeDecl) (feed : PortFeed) : Option Store :=
  if InputContract n feed then some (storeSet s feed) else none

theorem checkedInputStep_valid (s : Store) (n : NodeDecl) (feed : PortFeed)
    (h : InputContract n feed) : checkedInputStep s n feed = some (storeSet s feed) :=
  if_pos h

theorem checkedInputStep_invalid (s : Store) (n : NodeDecl) (feed : PortFeed)
    (h : ¬ InputContract n feed) : checkedInputStep s n feed = none := if_neg h

theorem storeSet_feed_value (s : Store) (feed : PortFeed) (tid : Tid) (v : Tensor)
    (hu : (feed.map Prod.fst).Nodup) (hm : (tid, v) ∈ feed) :
    storeSet s feed tid = v := by
  induction feed with
  | nil => cases hm
  | cons p ps ih =>
    rcases p with ⟨k, x⟩
    have hn := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hm with he | ht
    · cases he
      simp only [storeSet, List.find?, decide_true]
    · have hk : k ≠ tid := by
        intro he
        apply hn.1
        rw [he]
        exact List.mem_map.mpr ⟨(tid, v), ht, rfl⟩
      simpa only [storeSet, List.find?, hk, decide_false, ↓reduceIte] using ih hn.2 ht

theorem checkedInputStep_value (s s' : Store) (n : NodeDecl) (feed : PortFeed)
    (tid : Tid) (v : Tensor) (hm : (tid, v) ∈ feed)
    (hs : checkedInputStep s n feed = some s') : s' tid = v := by
  unfold checkedInputStep at hs
  split at hs
  · rename_i h
    cases Option.some.inj hs
    apply storeSet_feed_value s feed tid v _ hm
    rw [h.2.2.2.2.2]
    exact h.2.2.2.2.1
  · contradiction

theorem checkedInputStep_skip (s s' : Store) (n : NodeDecl) (feed : PortFeed)
    (tid : Tid) (ht : tid ∉ n.outs)
    (hs : checkedInputStep s n feed = some s') : s' tid = s tid := by
  unfold checkedInputStep at hs
  split at hs
  · rename_i h
    cases Option.some.inj hs
    apply storeSet_eq_of_not_mem_fst
    rw [h.2.2.2.2.2]
    exact ht
  · contradiction

/-- In explicit mode a loader requires a payload; other operations forbid one.
The loader request stays the source renderer's blocked `.group none` request. -/
def stepWithInputs (g : GraphDecl) (request : GroupScopedEval.Request) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (feed : Option PortFeed) : Option Store :=
  match feed with
  | some ports => if request = .group none then checkedInputStep s n ports else none
  | none => if n.op = "OpName.DATALOADER" then none else step g request peer s n

theorem stepWithInputs_missing (g : GraphDecl) (request : GroupScopedEval.Request)
    (peer : Nat → Tid) (s : Store) (n : NodeDecl) (h : n.op = "OpName.DATALOADER") :
    stepWithInputs g request peer s n none = none := if_pos h

theorem stepWithInputs_ordinary (g : GraphDecl) (request : GroupScopedEval.Request)
    (peer : Nat → Tid) (s : Store) (n : NodeDecl) (h : n.op ≠ "OpName.DATALOADER") :
    stepWithInputs g request peer s n none = step g request peer s n := if_neg h

theorem stepWithInputs_unknown (g : GraphDecl) (peer : Nat → Tid) (s : Store)
    (n : NodeDecl) (feed : Option PortFeed)
    (h : n.op ≠ "OpName.DATALOADER") (ha : n.op ≠ "OpName.AllToAllPrim")
    (hw : n.op ≠ "OpName.CROSS_DP_WRED") :
    stepWithInputs g (.group none) peer s n feed = none := by
  cases feed with
  | none => rw [stepWithInputs_ordinary _ _ _ _ _ h, step_group _ _ _ _ _ ha hw]; rfl
  | some ports =>
    change (if (GroupScopedEval.Request.group none) = .group none then checkedInputStep s n ports else none) = none
    rw [if_pos rfl]
    exact checkedInputStep_invalid _ _ _ (fun hc => h hc.1)

theorem stepWithInputs_skip (g : GraphDecl) (request : GroupScopedEval.Request)
    (peer : Nat → Tid) (s s' : Store) (n : NodeDecl) (feed : Option PortFeed)
    (tid : Tid) (ht : tid ∉ n.outs)
    (hs : stepWithInputs g request peer s n feed = some s') : s' tid = s tid := by
  cases feed with
  | none =>
    simp only [stepWithInputs] at hs
    split at hs
    · contradiction
    · exact step_skip g request peer s s' n tid ht hs
  | some ports =>
    simp only [stepWithInputs] at hs
    split at hs
    · exact checkedInputStep_skip s s' n ports tid ht hs
    · contradiction

/-- Full ordered schedule equality prevents missing, reordered or unused requests.
Unique graph-written keys make input outputs fresh relative to every other writer. -/
def InputSchedule (nodes : List NodeDecl) (requests : List InputRequest) : Prop :=
  requests.map Prod.fst = nodes ∧ (nodes.flatMap NodeDecl.outs).Nodup

instance (nodes : List NodeDecl) (requests : List InputRequest) :
    Decidable (InputSchedule nodes requests) := inferInstanceAs (Decidable (_ ∧ _))

/-- `none` is exactly the legacy mode; `some []` is a checked empty schedule,
not a request to invent missing data. No second graph or store is introduced. -/
def runWithInputs (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (inputs : Option (List InputRequest)) (init : Option Store) : Option Store :=
  match inputs with
  | none => run g scope peer nodes init
  | some requests => if InputSchedule nodes requests then
      runUsing (fun row s => stepWithInputs g (scope row.1) (peer row.1) s row.1 row.2) requests init
    else none

def denoteWithInputs (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (inputs : Option (List InputRequest)) (s : Store) : Option Store :=
  runWithInputs g scope peer g.nodes inputs (some s)

theorem runWithInputs_noFeed (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl) (init : Option Store) :
    runWithInputs g scope peer nodes none init = run g scope peer nodes init := rfl

theorem denoteWithInputs_noFeed (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (s : Store) :
    denoteWithInputs g scope peer none s = denote g scope peer s := rfl

theorem runUsing_none {α : Type} (advance : α → Store → Option Store) (nodes : List α) :
    runUsing advance nodes none = none := by
  induction nodes with
  | nil => rfl
  | cons n ns ih => exact ih

theorem runUsing_failed {α : Type} (advance : α → Store → Option Store)
    (n : α) (ns : List α) (s : Store) (h : advance n s = none) :
    runUsing advance (n :: ns) (some s) = none := by
  change runUsing advance ns (advance n s) = none
  rw [h, runUsing_none]

theorem runUsing_frame {α : Type} (advance : α → Store → Option Store) (nodes : List α)
    (s s' : Store) (tid : Tid)
    (hf : ∀ n ∈ nodes, ∀ a b, advance n a = some b → b tid = a tid)
    (hs : runUsing advance nodes (some s) = some s') : s' tid = s tid := by
  induction nodes generalizing s with
  | nil => cases Option.some.inj hs; rfl
  | cons n ns ih =>
    change runUsing advance ns (advance n s) = some s' at hs
    cases he : advance n s with
    | none => rw [he, runUsing_none] at hs; contradiction
    | some t =>
      rw [he] at hs
      exact (ih t (fun m hm => hf m (List.mem_cons_of_mem n hm)) hs).trans
        (hf n List.mem_cons_self s t he)

theorem runWithInputs_none (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl) (inputs : Option (List InputRequest)) :
    runWithInputs g scope peer nodes inputs none = none := by
  cases inputs with
  | none => exact run_none g scope peer nodes
  | some requests =>
    simp only [runWithInputs]
    split
    · exact runUsing_none _ _
    · rfl

theorem runWithInputs_skip (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl) (inputs : Option (List InputRequest))
    (s s' : Store) (tid : Tid) (ht : ∀ n ∈ nodes, tid ∉ n.outs)
    (hs : runWithInputs g scope peer nodes inputs (some s) = some s') : s' tid = s tid := by
  cases inputs with
  | none => exact run_skip g scope peer nodes s s' tid ht hs
  | some requests =>
    simp only [runWithInputs] at hs
    split at hs
    · rename_i hc
      apply runUsing_frame _ requests s s' tid _ hs
      intro row hr a b hb
      apply stepWithInputs_skip g (scope row.1) (peer row.1) a b row.1 row.2 tid _ hb
      apply ht row.1
      rw [← hc.1]
      exact List.mem_map.mpr ⟨row, hr, rfl⟩
    · contradiction

#print axioms checkedInputStep_valid
#print axioms checkedInputStep_invalid
#print axioms storeSet_feed_value
#print axioms checkedInputStep_value
#print axioms checkedInputStep_skip
#print axioms stepWithInputs_missing
#print axioms stepWithInputs_ordinary
#print axioms stepWithInputs_unknown
#print axioms stepWithInputs_skip
#print axioms runWithInputs_noFeed
#print axioms denoteWithInputs_noFeed
#print axioms runUsing_none
#print axioms runUsing_failed
#print axioms runUsing_frame
#print axioms runWithInputs_none
#print axioms runWithInputs_skip

#print axioms run_cons
#print axioms run_none
#print axioms step_skip
#print axioms run_skip
#print axioms run_global

#print axioms step_allToAll
#print axioms step_group
#print axioms step_global
#print axioms step_wred
#print axioms wred_output
end
end TrainVerify.Denote.SourceScopedEval
