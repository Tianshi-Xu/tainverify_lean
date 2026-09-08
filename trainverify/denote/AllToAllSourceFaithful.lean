import denote.GroupScopedEval

namespace TrainVerify.Denote.AllToAllSourceFaithful
set_option maxHeartbeats 500000
noncomputable section

/-- Derived source flow of collectives.py:157–168. Ordered senders each split
on odim, exchange their destination chunk, then concatenate on idim.
This is additive: the legacy gather-then-chunk function is NOT replaced. -/
def tensor (K destination idim odim : Nat) (xs : List Tensor) : Tensor :=
  allGatherPrimDimN idim K 0 (xs.map (chunkPrimDimN odim K destination))

/-- Input-only contract. Positive, equal, divisible shapes; arbitrary natural axes.
The order of xs is the ordered primitive group, not sorted/global rank order. -/
def Inputs (K idim odim : Nat) (xs : List Tensor) : Prop :=
  0 < K ∧ xs.length = K ∧ ∃ sh : Shape,
    (∀ x ∈ xs, x.shape = sh) ∧ idim < sh.length ∧ odim < sh.length ∧
    0 < sh.getD odim 0 ∧ K ∣ sh.getD odim 0

/-- Exact shape for any nonempty ordered sender list and positive K. -/
theorem tensor_shape (K destination idim odim : Nat) (x : Tensor) (xs : List Tensor)
    (hK : K ≠ 0) :
    (tensor K destination idim odim (x :: xs)).shape =
      let sh := x.shape.set odim (x.shape.getD odim 0 / K)
      sh.set idim (sh.getD idim 0 * K) := by
  simp only [tensor, List.map_cons, allGatherPrimDimN, List.head?_cons,
    Option.map_some, Option.getD_some, Tensor.mkShape, chunkPrimDimN, hK, ite_false]

/-- Generic flattened gather index law into the received destination chunks.
No desired output equality, fixed K, model case, or axis special case is assumed. -/
theorem tensor_val (K destination idim odim : Nat) (xs : List Tensor)
    (idx : Fin (prodShape (tensor K destination idim odim xs).shape)) :
    (tensor K destination idim odim xs).val idx =
      let pieces := xs.map (chunkPrimDimN odim K destination)
      let sh := (pieces.head?.map Tensor.shape).getD []
      let d := sh.getD idim 0
      let stride := (sh.drop (idim + 1)).foldl (· * ·) 1
      let full := d * K * stride
      let pre := if full = 0 then 0 else idx.val / full
      let rem := if full = 0 then 0 else idx.val % full
      let j := if stride = 0 then 0 else rem / stride
      let post := if stride = 0 then 0 else rem % stride
      let sender := if d = 0 then 0 else j / d
      let jLocal := if d = 0 then 0 else j % d
      valAt (pieces.getD sender (zeroTensor sh)) (pre * (d * stride) + jLocal * stride + post) := rfl

/-- Flattened value law for each sender's split chunk, completing tensor_val's
sender-selection law down to the original input value. -/
theorem split_val (K destination odim : Nat) (x : Tensor)
    (idx : Fin (prodShape (chunkPrimDimN odim K destination x).shape)) :
    (chunkPrimDimN odim K destination x).val idx =
      let d := x.shape.getD odim 0
      let size := if K = 0 then 0 else d / K
      let stride := (x.shape.drop (odim + 1)).foldl (· * ·) 1
      let block := size * stride
      let pre := if block = 0 then 0 else idx.val / block
      let rem := if block = 0 then 0 else idx.val % block
      let j := if stride = 0 then 0 else rem / stride
      let post := if stride = 0 then 0 else rem % stride
      let dst := if K = 0 then destination else destination % K
      valAt x (pre * (d * stride) + (dst * size + j) * stride + post) := rfl

/-- Original graph input TIDs must be the exact ordered peer read map. This is
external input authority, never an assumption about the output tensor. -/
def NodeContract (rs : List Nat) (peer : Nat → Tid) (s : Store)
    (n : NodeDecl) (idim odim output : Nat) : Prop :=
  n.op = "OpName.AllToAllPrim" ∧ n.params = [idim, odim] ∧
  n.ins = rs.map peer ∧ n.outs = [output] ∧
  Inputs rs.length idim odim (n.ins.map s)

inductive Failure where
  | missingScope
  | rejectedScope
  | invalidNode
  deriving DecidableEq, Repr

/-- One update to the original world store; no per-unit graph or remapped TIDs. -/
def localStep (rs : List Nat) (s : Store) (n : NodeDecl) (idim odim : Nat) : Store :=
  storeSet s (n.outs.zip [tensor rs.length (rs.idxOf n.rank) idim odim (n.ins.map s)])

/-- Validated AllToAll-only node API. Non-AllToAll nodes are rejected; callers
must explicitly integrate with their existing single mixed-node schedule.
`peer` binds ordered process membership to original input TIDs. -/
def step (g : GraphDecl) (scope : Option (List Nat)) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) : Except Failure Store := by
  classical
  exact match scope with
  | none => .error .missingScope
  | some rs => match GroupScopedEval.resolve g.numRanks n.rank (some rs) with
    | none => .error .rejectedScope
    | some (_, _) => match n.params, n.outs with
      | [i, o], [out] => if NodeContract rs peer s n i o out then
          .ok (localStep rs s n i o) else .error .invalidNode
      | _, _ => .error .invalidNode

theorem step_missing (g : GraphDecl) (peer : Nat → Tid) (s : Store) (n : NodeDecl) :
    step g none peer s n = .error .missingScope := rfl

theorem step_rejected (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (h : ¬ GroupScopedEval.WellFormed g.numRanks n.rank rs) :
    step g (some rs) peer s n = .error .rejectedScope := by
  simp only [step, GroupScopedEval.resolve_invalid _ _ _ h]

theorem step_valid (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (i o out : Nat)
    (hg : GroupScopedEval.WellFormed g.numRanks n.rank rs)
    (hc : NodeContract rs peer s n i o out) :
    step g (some rs) peer s n = .ok (localStep rs s n i o) := by
  simp only [step, GroupScopedEval.resolve_valid _ _ _ hg, hc.2.1, hc.2.2.2.1]
  exact if_pos hc

theorem step_invalid (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (i o out : Nat)
    (hg : GroupScopedEval.WellFormed g.numRanks n.rank rs)
    (hp : n.params = [i, o]) (ho : n.outs = [out])
    (hc : ¬ NodeContract rs peer s n i o out) :
    step g (some rs) peer s n = .error .invalidNode := by
  simp only [step, GroupScopedEval.resolve_valid _ _ _ hg, hp, ho]
  exact if_neg hc

theorem localStep_out (rs : List Nat) (s : Store) (n : NodeDecl)
    (i o out : Nat) (ho : n.outs = [out]) :
    localStep rs s n i o out = tensor rs.length (rs.idxOf n.rank) i o (n.ins.map s) := by
  simp only [localStep, ho, List.zip_cons_cons, List.zip_nil_left, storeSet,
    List.find?, decide_true]

theorem localStep_skip (rs : List Nat) (s : Store) (n : NodeDecl)
    (i o tid : Nat) (h : tid ∉ n.outs) : localStep rs s n i o tid = s tid :=
  storeSet_zip_eq_of_not_mem s n.outs _ tid h

theorem step_output (g : GraphDecl) (rs : List Nat) (peer : Nat → Tid)
    (s : Store) (n : NodeDecl) (i o out : Nat)
    (hg : GroupScopedEval.WellFormed g.numRanks n.rank rs)
    (hc : NodeContract rs peer s n i o out) :
    ∃ s', step g (some rs) peer s n = .ok s' ∧
      s' out = tensor rs.length (rs.idxOf n.rank) i o (n.ins.map s) ∧
      (∀ tid, tid ∉ n.outs → s' tid = s tid) ∧ rs.idxOf n.rank < rs.length :=
  ⟨localStep rs s n i o, step_valid g rs peer s n i o out hg hc,
    localStep_out rs s n i o out hc.2.2.2.1,
    localStep_skip rs s n i o, GroupScopedEval.localIndex_lt _ _ _ hg⟩

/-- AllToAll-only ordered schedule over one shared world store. Failure is
propagated; no reordering or independent per-group evaluation is performed. -/
def run (g : GraphDecl) (scope : NodeDecl → Option (List Nat))
    (peer : NodeDecl → Nat → Tid) (s : Store) : Except Failure Store :=
  g.nodes.foldl (fun st n => st.bind (fun t => step g (scope n) (peer n) t n)) (.ok s)

#print axioms split_val
#print axioms step_invalid
#print axioms tensor_shape
#print axioms tensor_val
#print axioms step_missing
#print axioms step_rejected
#print axioms step_valid
#print axioms localStep_out
#print axioms localStep_skip
#print axioms step_output
end
end TrainVerify.Denote.AllToAllSourceFaithful
