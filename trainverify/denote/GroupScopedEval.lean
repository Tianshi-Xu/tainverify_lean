import denote.Denote

namespace TrainVerify.Denote.GroupScopedEval
set_option maxHeartbeats 500000
noncomputable section

/-- Ordered primitive membership, not GraphDecl.replicaGroups. -/
def WellFormed (world rank : Nat) (ranks : List Nat) : Prop :=
  ranks ≠ [] ∧ ranks.Nodup ∧ (∀ r ∈ ranks, r < world) ∧ rank ∈ ranks

instance (world rank : Nat) (ranks : List Nat) : Decidable (WellFormed world rank ranks) :=
  inferInstanceAs (Decidable (ranks ≠ [] ∧ ranks.Nodup ∧ (∀ r ∈ ranks, r < world) ∧ rank ∈ ranks))

/-- An absent required group is different from an explicitly global step. -/
inductive Request where
  | global
  | group (ranks : Option (List Nat))
  deriving DecidableEq

def resolve (world rank : Nat) (ranks : Option (List Nat)) : Option (List Nat × Nat) :=
  match ranks with
  | none => none
  | some rs => if WellFormed world rank rs then some (rs, rs.idxOf rank) else none

theorem resolve_valid (world rank : Nat) (rs : List Nat) (h : WellFormed world rank rs) :
    resolve world rank (some rs) = some (rs, rs.idxOf rank) := by
  exact if_pos h

theorem resolve_invalid (world rank : Nat) (rs : List Nat) (h : ¬ WellFormed world rank rs) :
    resolve world rank (some rs) = none := by
  exact if_neg h

theorem localIndex_lt (world rank : Nat) (rs : List Nat) (h : WellFormed world rank rs) :
    rs.idxOf rank < rs.length := List.idxOf_lt_length_of_mem h.2.2.2

/-- Only the existing five primitive evalOp boundaries are scoped. -/
def supported (op : String) : Bool :=
  op == "OpName.ChunkPrim" || op == "OpName.AllGatherPrim" ||
  op == "OpName.AllToAllPrim" || op == "OpName.ReduceScatterPrim" || op == "OpName.AllReducePrim"

/-- Same node, inputs, output keys and store; only evalOp's two rank arguments change. -/
def localStep (rs : List Nat) (s : Store) (n : NodeDecl) : Store :=
  storeSet s (n.outs.zip (evalOp rs.length (rs.idxOf n.rank) n.op n.params (n.ins.map s)))

def step (g : GraphDecl) (request : Request) (s : Store) (n : NodeDecl) : Option Store :=
  match request with
  | .global => some (applyNode g s n)
  | .group ranks =>
    match resolve g.numRanks n.rank ranks with
    | none => none
    | some (rs, _) => if supported n.op then some (localStep rs s n) else none

theorem step_global (g : GraphDecl) (s : Store) (n : NodeDecl) :
    step g .global s n = some (applyNode g s n) := rfl

theorem step_scoped (g : GraphDecl) (s : Store) (n : NodeDecl) (rs : List Nat)
    (h : WellFormed g.numRanks n.rank rs) (hop : supported n.op = true) :
    step g (.group (some rs)) s n = some
      (storeSet s (n.outs.zip (evalOp rs.length (rs.idxOf n.rank) n.op n.params (n.ins.map s)))) := by
  simp only [step, resolve_valid _ _ _ h, hop, ↓reduceIte, localStep]

theorem localStep_skip (rs : List Nat) (s : Store) (n : NodeDecl) (tid : Tid)
    (h : tid ∉ n.outs) : localStep rs s n tid = s tid :=
  storeSet_zip_eq_of_not_mem s n.outs _ tid h

theorem step_skip (g : GraphDecl) (request : Request) (s s' : Store) (n : NodeDecl)
    (tid : Tid) (h : tid ∉ n.outs) (hs : step g request s n = some s') : s' tid = s tid := by
  cases request with
  | global => cases Option.some.inj hs; exact applyNode_skip g s n tid h
  | group ranks =>
    change (match resolve g.numRanks n.rank ranks with
      | none => none
      | some (rs, _) => if supported n.op then some (localStep rs s n) else none) = some s' at hs
    split at hs
    · contradiction
    · split at hs
      · cases Option.some.inj hs; exact localStep_skip _ s n tid h
      · contradiction

/-- Torch chunk refinement uses positive divisible dimensions only; no ragged claim. -/
def ChunkInput (rs : List Nat) (dim : Nat) (x : Tensor) : Prop :=
  dim < x.shape.length ∧ 0 < x.shape.getD dim 0 ∧ rs.length ∣ x.shape.getD dim 0

theorem chunk_out (g : GraphDecl) (s : Store) (rank : Nat) (rs : List Nat)
    (input output dim : Nat) (h : WellFormed g.numRanks rank rs)
    (_hx : ChunkInput rs dim (s input)) :
    step g (.group (some rs)) s
      {rank := rank, op := "OpName.ChunkPrim", ins := [input], outs := [output], params := [dim]} =
    some (storeSet s [(output, chunkPrimDimN dim rs.length (rs.idxOf rank) (s input))]) := by
  exact step_scoped g s _ rs h (by rfl)

theorem world_wellFormed (world rank : Nat) (h : rank < world) :
    WellFormed world rank (List.range world) := by
  refine ⟨?_, List.nodup_range, ?_, List.mem_range.mpr h⟩
  · intro he; have := congrArg List.length he; simp only [List.length_range, List.length_nil] at this; omega
  · intro r hr; exact List.mem_range.mp hr

theorem world_localStep (g : GraphDecl) (s : Store) (n : NodeDecl) (h : n.rank < g.numRanks) :
    localStep (List.range g.numRanks) s n = applyNode g s n := by
  have hi : (List.range g.numRanks).idxOf n.rank = n.rank := by
    have he := (List.nodup_range (n := g.numRanks)).idxOf_getElem (i := n.rank) (by simpa using h)
    simpa only [List.getElem_range] using he
  simp only [localStep, List.length_range, hi, applyNode]

theorem step_world (g : GraphDecl) (s : Store) (n : NodeDecl)
    (h : n.rank < g.numRanks) (hop : supported n.op = true) :
    step g (.group (some (List.range g.numRanks))) s n = some (applyNode g s n) := by
  rw [step_scoped g s n _ (world_wellFormed _ _ h) hop]
  exact congrArg some (world_localStep g s n h)

/-- One ordered graph schedule. Failure propagates, including missing required scopes. -/
def run (g : GraphDecl) (scope : NodeDecl → Request) (nodes : List NodeDecl)
    (init : Option Store) : Option Store :=
  nodes.foldl (fun state n => state.bind (fun s => step g (scope n) s n)) init

def denote (g : GraphDecl) (scope : NodeDecl → Request) (init : Store) : Option Store :=
  run g scope g.nodes (some init)

theorem run_global (g : GraphDecl) (nodes : List NodeDecl) (s : Store) :
    run g (fun _ => .global) nodes (some s) = some (nodes.foldl (applyNode g) s) := by
  induction nodes generalizing s with
  | nil => rfl
  | cons n ns ih => exact ih (applyNode g s n)

theorem denote_global (g : GraphDecl) (s : Store) :
    denote g (fun _ => .global) s = some (denoteGraph g s) := run_global g g.nodes s

theorem run_skip (g : GraphDecl) (scope : NodeDecl → Request) (nodes : List NodeDecl)
    (s s' : Store) (tid : Tid) (h : ∀ n ∈ nodes, tid ∉ n.outs)
    (hs : run g scope nodes (some s) = some s') : s' tid = s tid := by
  induction nodes generalizing s with
  | nil => cases Option.some.inj hs; rfl
  | cons n ns ih =>
    have hn := h n (List.mem_cons_self)
    have ht : ∀ m ∈ ns, tid ∉ m.outs := fun m hm => h m (List.mem_cons_of_mem n hm)
    cases he : step g (scope n) s n with
    | none =>
      have hf : ∀ xs : List NodeDecl, run g scope xs none = none := by
        intro xs; induction xs with
        | nil => rfl
        | cons a as ih => exact ih
      change run g scope ns ((some s).bind (fun t => step g (scope n) t n)) = _ at hs
      simp only [Option.bind_some, he, hf] at hs
      contradiction
    | some t =>
      change run g scope ns (step g (scope n) s n) = _ at hs
      rw [he] at hs
      exact (ih t ht hs).trans (step_skip g (scope n) s t n tid hn he)

#print axioms step_global
#print axioms localStep_skip
#print axioms world_localStep
#print axioms run_global
#print axioms resolve_valid
#print axioms resolve_invalid
#print axioms localIndex_lt
#print axioms step_scoped
#print axioms step_skip
#print axioms chunk_out
#print axioms world_wellFormed
#print axioms step_world
#print axioms denote_global
#print axioms run_skip
end
end TrainVerify.Denote.GroupScopedEval
