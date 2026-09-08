import denote.AllToAllSourceFaithful

namespace TrainVerify.Denote.SourceScopedEval
set_option maxHeartbeats 500000
noncomputable section

/-- Explicit global requests never accept collectives or unimplemented WRED. -/
def ordinary (op : String) : Bool :=
  !GroupScopedEval.supported op && op != "OpName.WRED" && op != "OpName.CROSS_DP_WRED"

/-- One world-store dispatcher. Only AllToAll changes denotation. -/
def step (g : GraphDecl) (request : GroupScopedEval.Request) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) : Option Store :=
  match request with
  | .global => if ordinary n.op then some (applyNode g s n) else none
  | .group rs => if n.op = "OpName.AllToAllPrim" then
      (AllToAllSourceFaithful.step g rs peer s n).toOption
    else GroupScopedEval.step g (.group rs) s n

theorem step_allToAll (g : GraphDecl) (rs : Option (List Nat)) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (h : n.op = "OpName.AllToAllPrim") :
    step g (.group rs) peer s n = (AllToAllSourceFaithful.step g rs peer s n).toOption := by
  simp only [step, h, ↓reduceIte]

theorem step_group (g : GraphDecl) (rs : Option (List Nat)) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (h : n.op ≠ "OpName.AllToAllPrim") :
    step g (.group rs) peer s n = GroupScopedEval.step g (.group rs) s n := by
  simp only [step, h, ↓reduceIte]

theorem step_global (g : GraphDecl) (peer : Nat → Tid) (s : Store) (n : NodeDecl)
    (h : ordinary n.op = true) : step g .global peer s n = some (applyNode g s n) := by
  simp only [step, h, ↓reduceIte]

/-- The complete graph node list is evaluated once, in original order. -/
def run (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl) (init : Option Store) : Option Store :=
  nodes.foldl (fun state n => state.bind (fun s => step g (scope n) (peer n) s n)) init

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
    · rw [step_group _ _ _ _ _ hop] at hs
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

#print axioms run_cons
#print axioms run_none
#print axioms step_skip
#print axioms run_skip
#print axioms run_global

#print axioms step_allToAll
#print axioms step_group
#print axioms step_global
end
end TrainVerify.Denote.SourceScopedEval
