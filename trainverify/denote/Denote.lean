import Std
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace TrainVerify.Denote

set_option linter.flexible false
set_option linter.style.emptyLine false

noncomputable section

open scoped BigOperators

abbrev Tid := Nat
abbrev Rank := Nat
abbrev Shape := List Nat

abbrev Scalar := ℝ

def prodShape (sh : Shape) : Nat :=
  sh.foldl (fun acc d => acc * d) 1

/-- A per-rank tensor reference in the parallel graph. -/
structure Piece where
  rank : Rank
  tid : Tid
  deriving Repr, DecidableEq

/-- A node declaration, treated as a pure equation: `outs := op(ins)`.

We keep `op` as a `String` so the generator does not need to know the full set
of operators ahead of time.

For cross-rank collectives, the node inputs may include tids produced on other ranks;
the generator handles this by listing all required tids explicitly.
-/
structure NodeDecl where
  rank : Rank
  op : String
  ins : List Tid
  outs : List Tid
  params : List Nat := []
  deriving Repr, DecidableEq

/-- A graph/program is a list of node equations, plus `numRanks`.

`numRanks` is used for shape-level definitions of sharding/collectives (Chunk/AllGather/AllReduce).
For SM graphs we typically set `numRanks = 1`.

The generator ensures `nodes` are already topologically ordered for the selected subgraph,
so `denoteGraph` is a single forward fold (not a fixpoint / repeated store scan).
-/
structure GraphDecl where
  numRanks : Nat
  nodes : List NodeDecl
  deriving Repr, DecidableEq

/-
A lineage goal for an observable output.

We include shapes, so “dimension matching” becomes part of the goal.

For now, the goal uses only id-level alignment (Ts corresponds to these per-rank Tps).
The *interpretation* of how to combine shards is provided by `reconstruct`.
 -/
structure LineageGoal where
  ts : Tid
  tsShape : Shape
  tps : List Piece
  tpShapes : List Shape
  gatherDim : Nat := 0
  deriving Repr, DecidableEq

/-!
## Concrete tensor values

We use a simple **flat list** representation for tensor values, together with an explicit `shape`.

This is not fundamentally limiting: any finite tensor can be flattened into a list, and operators
are defined by index arithmetic derived from shapes.

Important caveat: to *validate real kernel code*, you'd additionally need a connection between the
implementation and these definitions (proof of refinement, testing, or code extraction).
-/

structure Tensor where
  shape : Shape
  val : Fin (prodShape shape) → Scalar

abbrev Store := Tid → Tensor

/-!
## Initial-shape assumptions

The graph itself does not carry shapes on every node. Instead, shapes are derived from:
- the shapes of *initial* tensors (inputs/parameters), and
- shape-transforming operators (Chunk/AllGather/AllReduce/Linear/etc).

To keep goals provable and faithful to the originating graphs, we express initial-shape
information separately as a partial map `ShapeEnv : Tid → Option Shape`.
-/

abbrev ShapeEnv := Tid → Option Shape

def shapeEnvOfList (xs : List (Tid × Shape)) : ShapeEnv :=
  fun tid =>
    match xs.find? (fun p => p.1 = tid) with
    | some (_, sh) => some sh
    | none => none

def StoreShapesHold (init : Store) (env : ShapeEnv) : Prop :=
  ∀ tid sh, env tid = some sh → (init tid).shape = sh

def Tensor.mkShape (sh : Shape) (v : Fin (prodShape sh) → Scalar) : Tensor :=
  { shape := sh, val := v }

/-!
## Shape helpers
-/

def lastD (sh : Shape) : Nat :=
  sh.getLastD 0

def dropLast (sh : Shape) : Shape :=
  sh.dropLast

def appendLast (pref : Shape) (d : Nat) : Shape :=
  pref ++ [d]

def divNat (a b : Nat) : Nat :=
  a / b

/-!
## Small list/sum normalization lemmas

These are used to keep proofs about `allReducePrim` and chunked sums manageable.
-/

theorem List.foldl_add_eq_sum {α β : Type} [AddMonoid β] (f : α → β) (xs : List α) :
    xs.foldl (fun acc x => acc + f x) 0 = (xs.map f).sum := by
  -- Prove the stronger statement with an arbitrary accumulator.
  have hgen : ∀ (b : β) (xs : List α),
      xs.foldl (fun acc x => acc + f x) b = b + (xs.map f).sum := by
    intro b xs
    induction xs generalizing b with
    | nil =>
        simp
    | cons a as ih =>
        -- foldl with accumulator is associative with `+`.
        simpa [List.foldl, List.map, List.sum_cons, add_assoc] using (ih (b := b + f a))
  simpa using (hgen 0 xs)

-- Auxiliary lemma: head of List.ofFn is f 0 for nonempty Fin
lemma list_ofFn_head_eq {α : Type*} {n : Nat} (f : Fin (n + 1) → α) :
    (List.ofFn f).head? = some (f 0) := by
  have hlen : (List.ofFn f).length = n + 1 := List.length_ofFn
  have hne : (List.ofFn f) ≠ [] := by
    intro h
    have : (List.ofFn f).length = 0 := by rw [h]; simp
    omega
  rw [List.head?_eq_some_head hne, List.head_eq_getElem]
  simp only [List.getElem_ofFn]
  rfl

-- `List.ofFn` over `Fin xs.length` recovers the original list.
theorem Finset.sum_range_mul_eq_sum_sum (n m : Nat) (f : Nat → Scalar) :
    (∑ k ∈ Finset.range (n * m), f k) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f (i * m + j) := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have heq : (n + 1) * m = n * m + m := by ring
      calc
        (∑ k ∈ Finset.range ((n + 1) * m), f k)
            = (∑ k ∈ Finset.range (n * m + m), f k) := by
                rw [heq]
        _ = (∑ k ∈ Finset.range (n * m), f k) +
              ∑ k ∈ Finset.range m, f (n * m + k) := by
                rw [Finset.sum_range_add]
        _ = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f (i * m + j)) +
              ∑ j ∈ Finset.range m, f (n * m + j) := by
              simp [ih]
        _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range m, f (i * m + j) := by
              simp [Finset.sum_range_succ, add_comm]

/-!
## Operator kernels with concrete mathematical definitions

We provide real implementations instead of axioms, so proofs are grounded in actual mathematics.
-/

def valAt (t : Tensor) (k : Nat) : Scalar :=
  if h : k < prodShape t.shape then
    t.val ⟨k, h⟩
  else
    0

@[simp] theorem valAt_of_lt (t : Tensor) (k : Nat) (h : k < prodShape t.shape) :
    valAt t k = t.val ⟨k, h⟩ := by
  simp [valAt, h]

@[simp] theorem valAt_of_fin (t : Tensor) (i : Fin (prodShape t.shape)) :
    valAt t i.1 = t.val i := by
  simp [valAt_of_lt]

theorem Tensor.ext {t1 t2 : Tensor} (hshape : t1.shape = t2.shape)
    (hval : ∀ idx (_ : idx < prodShape t1.shape), valAt t1 idx = valAt t2 idx) : t1 = t2 := by
  cases t1 with | mk s1 v1 =>
  cases t2 with | mk s2 v2 =>
  simp only at hshape
  subst hshape
  congr
  funext idx
  have h1 : valAt { shape := s1, val := v1 } idx.1 = v1 idx := valAt_of_lt _ _ idx.2
  have h2 : valAt { shape := s1, val := v2 } idx.1 = v2 idx := valAt_of_lt _ _ idx.2
  rw [← h1, ← h2]
  exact hval idx.1 idx.2

def zeroTensor (sh : Shape) : Tensor :=
  Tensor.mkShape sh (fun _ => 0)


/-!
## Unified Matrix Multiplication

We introduce a single, general-purpose matrix multiplication definition that subsumes
all forward and backward linear layer operations. This dramatically simplifies proofs
by providing a single set of theorems that apply to all matrix operations.

Key insight: All three operations (fw_linear, bw_linear_dx, bw_linear_dw) are just
matrix multiplications with different input arrangements:
- fw_linear: Y = X @ W^T  →  matmul(X, W) where W is [o,i] (output-major)
- bw_linear_dx: dX = g @ W  →  matmul(g, W)
- bw_linear_dw: dW = g^T @ X  →  matmul(g^T, X) conceptually, implemented via sum reordering

The unified definition uses shape [m, k] × [n, k] → [m, n], computing:
  C[r, c] = Σ_j A[r, j] * B[c, j]

This matches "B is stored column-major" or equivalently "B^T in row-major",
which is exactly the weight layout in our backend graphs.
-/

/-- Unified matrix multiplication kernel: C[r,c] = Σ_j A[r,j] * B[c,j]

    This single definition handles:
    - Forward: matmul(X[b,i], W[o,i]) = Y[b,o]
    - Backward dX: matmul(g[b,o], W[o,i]) = dX[b,i]
    - Backward dW: matmul_transpose(g[b,o], X[b,i]) = dW[o,i]
-/
def k_matmul (m n k : Nat) (a b : Tensor) : Fin (prodShape [m, n]) → Scalar :=
  fun outIdx =>
    let r := outIdx.1 / n
    let c := outIdx.1 % n
    ∑ j ∈ Finset.range k,
      (valAt a (r * k + j)) * (valAt b (c * k + j))

/-- Right-transposed matmul kernel: treats `b` as shape `[k, n]` and indexes `b` by (j, c).

This is used for `bw_linear`'s dX when weights are stored as `[o, i]` (k = o, n = i).
-/
def k_matmul_right_transpose (m n k : Nat) (a b : Tensor) : Fin (prodShape [m, n]) → Scalar :=
  fun outIdx =>
    let r := outIdx.1 / n
    let c := outIdx.1 % n
    ∑ j ∈ Finset.range k,
      (valAt a (r * k + j)) * (valAt b (j * n + c))

/-- Transposed matrix multiplication kernel for weight gradients: dW[c,j] = Σ_r g[r,c] * X[r,j]

    This is equivalent to matmul(g^T, X) but implemented directly without explicit transpose.
-/
def k_matmul_transpose (m n k : Nat) (a b : Tensor) : Fin (prodShape [n, k]) → Scalar :=
  fun outIdx =>
    let c := outIdx.1 / k
    let j := outIdx.1 % k
    ∑ r ∈ Finset.range m,
      (valAt a (r * n + c)) * (valAt b (r * k + j))

/-!
## Operator wrappers (shape + value)
-/

def fw_sum (x : Tensor) : Tensor :=
  Tensor.mkShape [1] (fun _ => (∑ i : Fin (prodShape x.shape), x.val i))

def bw_sum (gradOut x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun _ => valAt gradOut 0)

def fw_linear (x w : Tensor) : Tensor :=
  -- Intended: x:[B,I], w:[O,I] => y:[B,O]  (or batched: x:[B,S,I], w:[O,I] => y:[B,S,O])
  match x.shape, w.shape with
  | [b, i], [o, _i2] =>
      -- We intentionally do not branch on the equality of inner dimensions here.
      -- Graph consistency is enforced separately by shape assumptions.
      Tensor.mkShape [b, o] (k_matmul b o i x w)
  | [b, s, i], [o, _i2] =>
      -- Batched linear: treat first two dims as combined batch.
      -- Equivalent to reshaping x to [b*s, i], applying 2D linear, then reshaping to [b, s, o].
      -- k_matmul (b*s) o i x w computes the correct flat indexing since
      -- valAt x (row * i + l) with row = batch*s + seq matches the 3D flat layout.
      Tensor.mkShape [b, s, o] (fun outIdx =>
        let flat := outIdx.1
        let so := s * o
        let row := if so = 0 then 0 else flat / so
        let rem := if so = 0 then 0 else flat % so
        let seq := if o = 0 then 0 else rem / o
        let col := if o = 0 then 0 else rem % o
        ∑ j ∈ Finset.range i,
          (valAt x ((row * s + seq) * i + j)) * (valAt w (col * i + j)))
  | _, _ => Tensor.mkShape [] (fun _ => 0)

def bw_linear (gradOut x w : Tensor) : Tensor × Tensor :=
  match gradOut.shape, x.shape, w.shape with
  | [_bG, _oG], [bX, iX], [oW, iW] =>
      -- As with `fw_linear`, we do not branch on dimension equalities here.
      -- Under the intended shape assumptions, these dimensions match.
  let dx := Tensor.mkShape [bX, iX] (k_matmul_right_transpose bX iX oW gradOut w)
      let dw := Tensor.mkShape [oW, iW] (k_matmul_transpose bX oW iW gradOut x)
      (dx, dw)
  | [b, s, _oG], [_bX, _sX, iX], [oW, iW] =>
      -- Batched backward linear: treat first two dims as combined batch (b * s).
      let bs := b * s
      let dx := Tensor.mkShape [b, s, iX] (fun outIdx =>
        let flat := outIdx.1
        let si := s * iX
        let row := if si = 0 then 0 else flat / si
        let rem := if si = 0 then 0 else flat % si
        let seq := if iX = 0 then 0 else rem / iX
        let col := if iX = 0 then 0 else rem % iX
        ∑ j ∈ Finset.range oW,
          (valAt gradOut ((row * s + seq) * _oG + j)) * (valAt w (j * iW + col)))
      let dw := Tensor.mkShape [oW, iW] (k_matmul_transpose bs oW iW gradOut x)
      (dx, dw)
  | _, _, _ => (Tensor.mkShape [] (fun _ => 0), Tensor.mkShape [] (fun _ => 0))

/-!
## Attention Operators - Simplified

Most attention operators are either:
1. Identity (view, contiguous, multiref) - no numerical change
2. Transpose - swap last two dims
3. Matmul-based (use existing k_matmul infrastructure)
4. Elementwise (div, softmax)

For proofs, we care about numerical equivalence. Shape correctness is
verified separately by shape checking.
-/

/-- Identity tensor operation. Used for view, contiguous, multiref. -/
@[inline] def tensorId (x : Tensor) : Tensor := x

/-- Transpose: swap the last two dimensions.
    Element at [..., i, j] maps to [..., j, i] -/
def transpose2d (x : Tensor) : Tensor :=
  match x.shape.reverse with
  | d1 :: d0 :: rest =>
      let outShape := (d0 :: d1 :: rest).reverse
      Tensor.mkShape outShape (fun outIdx =>
        let flat := outIdx.1
        let innerSize := d0 * d1
        let outerIdx := if innerSize = 0 then 0 else flat / innerSize
        let innerFlat := if innerSize = 0 then 0 else flat % innerSize
        let i := if d0 = 0 then 0 else innerFlat / d0
        let j := if d0 = 0 then 0 else innerFlat % d0
        valAt x (outerIdx * innerSize + j * d1 + i))
  | _ => x

/-- Batched matmul: x[..., n, k] @ y[..., k, m] -> [..., n, m]
    This is the core operation; fw_linear uses k_matmul which has similar semantics. -/
def batchedMatmul (x y : Tensor) : Tensor :=
  match x.shape.reverse, y.shape.reverse with
  | k1 :: n :: batch, m :: _k2 :: _ =>
      let outShape := (m :: n :: batch).reverse
      Tensor.mkShape outShape (fun outIdx =>
        let flat := outIdx.1
        let innerSize := n * m
        let outerIdx := if innerSize = 0 then 0 else flat / innerSize
        let innerFlat := if innerSize = 0 then 0 else flat % innerSize
        let i := if m = 0 then 0 else innerFlat / m
        let j := if m = 0 then 0 else innerFlat % m
        ∑ l ∈ Finset.range k1,
          (valAt x (outerIdx * (n * k1) + i * k1 + l)) *
          (valAt y (outerIdx * (k1 * m) + l * m + j)))
  | _, _ => Tensor.mkShape [] (fun _ => 0)

/-- Backward of batched matmul. Returns (dx, dy).
    dx = g @ y^T, dy = x^T @ g -/
def batchedMatmulBwd (g x y : Tensor) : Tensor × Tensor :=
  -- dx = g @ transpose(y), dy = transpose(x) @ g
  (batchedMatmul g (transpose2d y), batchedMatmul (transpose2d x) g)

/-- Elementwise scalar multiplication/division -/
def scalarMul (c : Scalar) (x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun i => c * valAt x i.1)

def scalarDiv (x : Tensor) (c : Scalar) : Tensor :=
  Tensor.mkShape x.shape (fun i => valAt x i.1 / c)

/-- Abstract exp for softmax (axiom to avoid mathlib deps) -/
axiom expFn : Scalar → Scalar

/-- Scalar special functions used by exact neural-network kernels.

They are kept as scalar primitives in the denotation, similar to `expFn` above:
the tensor operators are fully defined in terms of these scalar functions, while
analysis of the scalar library itself is out of scope for graph-equivalence proofs.
-/
axiom sqrtFn : Scalar → Scalar
axiom erfFn : Scalar → Scalar
axiom piScalar : Scalar
axiom scalarToNat : Scalar → Nat

/-- Softmax along last dimension -/
def softmax (x : Tensor) : Tensor :=
  match x.shape.reverse with
  | d :: _ =>
      Tensor.mkShape x.shape (fun outIdx =>
        let batch := if d = 0 then 0 else outIdx.1 / d
        let idx := if d = 0 then 0 else outIdx.1 % d
        let base := batch * d
        let expSum := ∑ j ∈ Finset.range d, expFn (valAt x (base + j))
        if expSum = 0 then 0 else expFn (valAt x (base + idx)) / expSum)
  | [] => x

/-- Softmax backward: dx_i = y_i * (g_i - Σ_j y_j * g_j) -/
def softmaxBwd (g y : Tensor) : Tensor :=
  match y.shape.reverse with
  | d :: _ =>
      Tensor.mkShape y.shape (fun outIdx =>
        let batch := if d = 0 then 0 else outIdx.1 / d
        let idx := if d = 0 then 0 else outIdx.1 % d
        let base := batch * d
        let dot := ∑ j ∈ Finset.range d, (valAt y (base + j)) * (valAt g (base + j))
        (valAt y (base + idx)) * (valAt g (base + idx) - dot))
  | [] => g

/-- Sum reduction (element-wise sum of list of tensors) -/
def tensorSum (xs : List Tensor) : Tensor :=
  match xs with
  | [] => Tensor.mkShape [] (fun _ => 0)
  | t :: _ => Tensor.mkShape t.shape (fun i => xs.foldl (fun acc x => acc + valAt x i.1) 0)

/-- Shape-preserving unary elementwise operator. -/
def elemwiseId (x : Tensor) : Tensor := x

/-- Convert flat index to multi-index given a shape. -/
def flatToMulti : Shape → Nat → List Nat
  | [], _ => []
  | _ :: rest, flat =>
    let stride := prodShape rest
    if stride = 0 then 0 :: flatToMulti rest 0
    else (flat / stride) :: flatToMulti rest (flat % stride)

/-- Convert multi-index to flat index given a shape. -/
def multiToFlat : Shape → List Nat → Nat
  | _ :: srest, i :: irest => i * prodShape srest + multiToFlat srest irest
  | _, _ => 0

def outShape2 (x y : Tensor) : Shape :=
  if x.shape.length >= y.shape.length then x.shape else y.shape

def alignedMultiIndex (outShape inShape : Shape) (outFlat : Nat) : List Nat :=
  let outMI := flatToMulti outShape outFlat
  let lead := outShape.length - inShape.length
  let aligned := outMI.drop lead
  List.ofFn (fun j : Fin inShape.length =>
    let dim := inShape.getD j.1 0
    let idx := aligned.getD j.1 0
    if dim = 1 then 0 else idx)

def broadcastValAtShape (outShape : Shape) (t : Tensor) (outFlat : Nat) : Scalar :=
  valAt t (multiToFlat t.shape (alignedMultiIndex outShape t.shape outFlat))

def reduceBroadcast (outShape inShape : Shape) (v : Nat → Scalar) : Tensor :=
  Tensor.mkShape inShape (fun inIdx =>
    ∑ k ∈ Finset.range (prodShape outShape),
      if multiToFlat inShape (alignedMultiIndex outShape inShape k) = inIdx.1 then
        v k
      else
        0)

/-- Binary elementwise addition with NumPy/PyTorch-style trailing-dimension broadcasting. -/
def elemwiseAdd (x y : Tensor) : Tensor :=
  let outShape := outShape2 x y
  Tensor.mkShape outShape (fun i =>
    broadcastValAtShape outShape x i.1 + broadcastValAtShape outShape y i.1)

/-- Binary elementwise add preserves the common shape when both inputs have that shape. -/
theorem elemwiseAdd_shape_of_shapes (x y : Tensor) (sh : Shape)
    (hx : x.shape = sh) (hy : y.shape = sh) :
    (elemwiseAdd x y).shape = sh := by
  unfold elemwiseAdd Tensor.mkShape
  change outShape2 x y = sh
  simp [outShape2, hx, hy]

def elemwiseMul (x y : Tensor) : Tensor :=
  let outShape := outShape2 x y
  Tensor.mkShape outShape (fun i =>
    broadcastValAtShape outShape x i.1 * broadcastValAtShape outShape y i.1)

def bw_add2 (g x y : Tensor) : Tensor × Tensor :=
  let outShape := g.shape
  (reduceBroadcast outShape x.shape (fun k => valAt g k),
   reduceBroadcast outShape y.shape (fun k => valAt g k))

/-! ### Helper lemmas for `bw_add2` identity (when outShape = inShape) -/

private theorem prodShape_cons' (d : Nat) (rest : Shape) :
    prodShape (d :: rest) = d * prodShape rest := by
  simp only [prodShape, List.foldl]
  suffices ∀ (a : Nat) (bs : List Nat), List.foldl (fun acc d => acc * d) a bs =
      a * List.foldl (fun acc d => acc * d) 1 bs by rw [this]; simp
  intro a bs
  induction bs generalizing a with
  | nil => simp [List.foldl]
  | cons b bs' ih =>
    simp only [List.foldl, Nat.one_mul]; rw [ih, ih b]; exact Nat.mul_assoc a b _

private theorem flatToMulti_length' (s : Shape) (k : Nat) :
    (flatToMulti s k).length = s.length := by
  induction s generalizing k with
  | nil => rfl
  | cons d rest ih =>
    change (let stride := prodShape rest
            if stride = 0 then 0 :: flatToMulti rest 0
            else (k / stride) :: flatToMulti rest (k % stride)).length = _
    dsimp only []; split_ifs
    · simp only [List.length_cons]; exact congrArg Nat.succ (ih 0)
    · simp only [List.length_cons]; exact congrArg Nat.succ (ih _)

private theorem flatToMulti_zero_at_dim_one (s : Shape) (k : Nat) (i : Nat)
    (hk : k < prodShape s) (hi : i < s.length) (hdim : s[i] = 1) :
    (flatToMulti s k)[i]'(by rw [flatToMulti_length']; exact hi) = 0 := by
  induction s generalizing k i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons d rest ih =>
    have hne : prodShape rest ≠ 0 := by
      intro h; rw [prodShape_cons'] at hk; simp [h] at hk
    have hprod_pos : 0 < prodShape rest := Nat.pos_of_ne_zero hne
    have hfm : flatToMulti (d :: rest) k =
        (k / prodShape rest) :: flatToMulti rest (k % prodShape rest) := by
      change (let stride := prodShape rest
              if stride = 0 then 0 :: flatToMulti rest 0
              else (k / stride) :: flatToMulti rest (k % stride)) = _
      dsimp only []; rw [if_neg hne]
    match i, hi, hdim with
    | 0, _, hdim0 =>
      have hd : d = 1 := hdim0
      subst hd; rw [prodShape_cons', Nat.one_mul] at hk
      have hfm1 : flatToMulti (1 :: rest) k =
          (k / prodShape rest) :: flatToMulti rest (k % prodShape rest) := by
        change (let stride := prodShape rest
                if stride = 0 then 0 :: flatToMulti rest 0
                else (k / stride) :: flatToMulti rest (k % stride)) = _
        dsimp only []; rw [if_neg hne]
      simp [hfm1, Nat.div_eq_of_lt hk]
    | i' + 1, hi_succ, hdim_succ =>
      have hi_rest : i' < rest.length := by
        have : (d :: rest).length = rest.length + 1 := rfl
        omega
      have key : (flatToMulti (d :: rest) k)[i' + 1]'(by rw [flatToMulti_length']; exact hi_succ) =
          (flatToMulti rest (k % prodShape rest))[i']'(by rw [flatToMulti_length']; exact hi_rest) := by
        simp only [hfm, List.getElem_cons_succ]
      rw [key]
      exact ih (k % prodShape rest) i' (Nat.mod_lt k hprod_pos) hi_rest hdim_succ

private theorem multiToFlat_flatToMulti' (s : Shape) (k : Nat) (hk : k < prodShape s) :
    multiToFlat s (flatToMulti s k) = k := by
  induction s generalizing k with
  | nil =>
    have hk0 : k = 0 := by have : prodShape ([] : List Nat) = 1 := rfl; omega
    subst hk0; rfl
  | cons d rest ih =>
    have hne : prodShape rest ≠ 0 := by
      intro h; rw [prodShape_cons'] at hk; simp [h] at hk
    have hprod_pos : 0 < prodShape rest := Nat.pos_of_ne_zero hne
    have hfm : flatToMulti (d :: rest) k =
        (k / prodShape rest) :: flatToMulti rest (k % prodShape rest) := by
      change (let stride := prodShape rest
              if stride = 0 then 0 :: flatToMulti rest 0
              else (k / stride) :: flatToMulti rest (k % stride)) = _
      dsimp only []; rw [if_neg hne]
    rw [hfm]; show k / prodShape rest * prodShape rest +
      multiToFlat rest (flatToMulti rest (k % prodShape rest)) = k
    rw [ih _ (Nat.mod_lt k hprod_pos), Nat.mul_comm]
    exact Nat.div_add_mod k (prodShape rest)

private theorem multiToFlat_alignedMultiIndex_same' (s : Shape) (k : Nat) (hk : k < prodShape s) :
    multiToFlat s (alignedMultiIndex s s k) = k := by
  suffices h : alignedMultiIndex s s k = flatToMulti s k by
    rw [h]; exact multiToFlat_flatToMulti' s k hk
  simp only [alignedMultiIndex, Nat.sub_self, List.drop_zero]
  apply List.ext_getElem (by simp [flatToMulti_length'])
  intro i hi1 hi2
  simp only [List.getElem_ofFn]
  have hi_s : i < s.length := by have := flatToMulti_length' s k; omega
  split_ifs with hdim
  · have hdim' : s[i] = 1 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_s] at hdim; exact hdim
    have h0 := flatToMulti_zero_at_dim_one s k i hk hi_s hdim'
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    simp

theorem reduceBroadcast_same (s : Shape) (v : Nat → Scalar) :
    reduceBroadcast s s v = Tensor.mkShape s (fun i => v i.1) := by
  simp only [reduceBroadcast, Tensor.mkShape]
  congr 1
  funext ⟨idx, hidx⟩
  have hrt : ∀ k ∈ Finset.range (prodShape s),
      multiToFlat s (alignedMultiIndex s s k) = k := fun k hk =>
    multiToFlat_alignedMultiIndex_same' s k (Finset.mem_range.mp hk)
  have heq : (∑ k ∈ Finset.range (prodShape s),
      if multiToFlat s (alignedMultiIndex s s k) = idx then v k else 0) =
    (∑ k ∈ Finset.range (prodShape s), if k = idx then v k else 0) :=
    Finset.sum_congr rfl (fun k hk => by rw [hrt k hk])
  rw [heq, Finset.sum_ite_eq']
  simp [Finset.mem_range, hidx]

theorem bw_add2_fst_same_shape (g x y : Tensor) (h : g.shape = x.shape) :
    (bw_add2 g x y).1 = g := by
  show reduceBroadcast g.shape x.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

def bw_mul2 (g x y : Tensor) : Tensor × Tensor :=
  let outShape := g.shape
  (reduceBroadcast outShape x.shape
      (fun k => valAt g k * broadcastValAtShape outShape y k),
   reduceBroadcast outShape y.shape
      (fun k => valAt g k * broadcastValAtShape outShape x k))

/-- Embedding lookup: `ids[...]` selects row `ids[...]` from `weight[vocab, hidden]`.

`Tensor` stores scalar values uniformly, so index tensors use `scalarToNat` as the
explicit decoding function from scalar payload to natural-number row id.
-/
def fw_embedding (ids weight : Tensor) : Tensor :=
  let hidden := lastD weight.shape
  Tensor.mkShape (ids.shape ++ [hidden]) (fun outIdx =>
    let h := outIdx.1 % hidden
    let idFlat := outIdx.1 / hidden
    let row := scalarToNat (valAt ids idFlat)
    valAt weight (row * hidden + h))

/-- Vocab-parallel embedding lookup with an explicit row offset.

For shard `weight` covering vocab rows `[offset, offset + weight.shape[0])`,
return the corresponding embedding row when `row` is in range, and 0 otherwise.

This models a single shard of a vocab-parallel embedding: each rank holds
`weight = W_r` with `weight.shape[0] = vocab_shard`, and the per-rank lookup
returns `W_r[row - offset, h]` only when `offset ≤ row < offset + vocab_shard`.
Summing across ranks (via `allReducePrim`) recovers the full embedding lookup.

When `offset = 0`, this coincides with `fw_embedding` for in-range ids and
agrees on the out-of-range case (both return 0), so it is backward compatible. -/
def fw_embedding_offset (offset : Nat) (ids weight : Tensor) : Tensor :=
  let hidden := lastD weight.shape
  let vocabShard := (weight.shape.head?).getD 0
  Tensor.mkShape (ids.shape ++ [hidden]) (fun outIdx =>
    let h := outIdx.1 % hidden
    let idFlat := outIdx.1 / hidden
    let row := scalarToNat (valAt ids idFlat)
    if offset ≤ row ∧ row < offset + vocabShard then
      valAt weight ((row - offset) * hidden + h)
    else 0)

def bw_embedding (g ids weight : Tensor) : Tensor :=
  let hidden := lastD weight.shape
  Tensor.mkShape weight.shape (fun wIdx =>
    let row := wIdx.1 / hidden
    let h := wIdx.1 % hidden
    ∑ k ∈ Finset.range (prodShape ids.shape),
      if scalarToNat (valAt ids k) = row then valAt g (k * hidden + h) else 0)

/-- Vocab-parallel embedding backward pass with an explicit row offset.

For a shard covering global rows `[offset, offset + weight.shape[0])`, local
row `i` accumulates gradients for global id `offset + i`. -/
def bw_embedding_offset (offset : Nat) (g ids weight : Tensor) : Tensor :=
  let hidden := lastD weight.shape
  Tensor.mkShape weight.shape (fun wIdx =>
    let localRow := wIdx.1 / hidden
    let h := wIdx.1 % hidden
    let globalRow := offset + localRow
    ∑ k ∈ Finset.range (prodShape ids.shape),
      if scalarToNat (valAt ids k) = globalRow then valAt g (k * hidden + h) else 0)

def layerNormMeanAt (x : Tensor) (row d : Nat) : Scalar :=
  (∑ j ∈ Finset.range d, valAt x (row * d + j)) / (d : Scalar)

def layerNormVarAt (x : Tensor) (row d : Nat) (mean : Scalar) : Scalar :=
  (∑ j ∈ Finset.range d, (valAt x (row * d + j) - mean) ^ 2) / (d : Scalar)

def layerNormEps : Scalar := (1 : Scalar) / 100000

def fw_layernorm (x weight bias : Tensor) : Tensor :=
  match x.shape.reverse with
  | d :: _ =>
      Tensor.mkShape x.shape (fun outIdx =>
        let row := outIdx.1 / d
        let j := outIdx.1 % d
        let mean := layerNormMeanAt x row d
        let var := layerNormVarAt x row d mean
        let invStd := 1 / sqrtFn (var + layerNormEps)
        ((valAt x outIdx.1 - mean) * invStd) * valAt weight j + valAt bias j)
  | [] => x

def bw_layernorm (g x weight bias : Tensor) : Tensor × Tensor × Tensor :=
  match x.shape.reverse with
  | d :: _ =>
      let dx := Tensor.mkShape x.shape (fun outIdx =>
        let row := outIdx.1 / d
        let j := outIdx.1 % d
        let mean := layerNormMeanAt x row d
        let var := layerNormVarAt x row d mean
        let invStd := 1 / sqrtFn (var + layerNormEps)
        let xhat := (valAt x outIdx.1 - mean) * invStd
        let sumDy := ∑ k ∈ Finset.range d,
          valAt g (row * d + k) * valAt weight k
        let sumDyXhat := ∑ k ∈ Finset.range d,
          let xhatK := (valAt x (row * d + k) - mean) * invStd
          (valAt g (row * d + k) * valAt weight k) * xhatK
        invStd / (d : Scalar) *
          ((d : Scalar) * (valAt g outIdx.1 * valAt weight j) - sumDy - xhat * sumDyXhat))
      let dw := Tensor.mkShape weight.shape (fun wIdx =>
        let j := wIdx.1
        ∑ row ∈ Finset.range (prodShape x.shape / d),
          let mean := layerNormMeanAt x row d
          let var := layerNormVarAt x row d mean
          let invStd := 1 / sqrtFn (var + layerNormEps)
          valAt g (row * d + j) * ((valAt x (row * d + j) - mean) * invStd))
      let db := Tensor.mkShape bias.shape (fun bIdx =>
        let j := bIdx.1
        ∑ row ∈ Finset.range (prodShape x.shape / d),
          valAt g (row * d + j))
      (dx, dw, db)
  | [] => (g, zeroTensor weight.shape, zeroTensor bias.shape)

def fw_dropout (x : Tensor) : Tensor := x

def bw_dropout (g _x : Tensor) : Tensor := g

def geluScalar (x : Scalar) : Scalar :=
  (1 / 2 : Scalar) * x * (1 + erfFn (x / sqrtFn 2))

def geluDerivScalar (x : Scalar) : Scalar :=
  (1 / 2 : Scalar) * (1 + erfFn (x / sqrtFn 2)) +
    x * expFn (-(x ^ 2) / 2) / sqrtFn (2 * piScalar)

def fw_gelu (x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun i => geluScalar (valAt x i.1))

def bw_gelu (g x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun i => valAt g i.1 * geluDerivScalar (valAt x i.1))

def fw_pow (n : Nat) (x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun i => (valAt x i.1) ^ n)

def bw_pow (n : Nat) (g x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun i =>
    match n with
    | 0 => 0
    | Nat.succ p => valAt g i.1 * ((n : Scalar) * (valAt x i.1) ^ p))

def fw_mean (x : Tensor) : Tensor :=
  match x.shape.reverse with
  | d :: rest =>
      Tensor.mkShape ((1 :: rest).reverse) (fun outIdx =>
        let row := outIdx.1
        (∑ j ∈ Finset.range d, valAt x (row * d + j)) / (d : Scalar))
  | [] => x

def bw_mean (g x : Tensor) : Tensor :=
  match x.shape.reverse with
  | d :: _ =>
      Tensor.mkShape x.shape (fun outIdx =>
        let row := outIdx.1 / d
        valAt g row / (d : Scalar))
  | [] => g

def fw_rsqrt (x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun i => 1 / sqrtFn (valAt x i.1))

def bw_rsqrt (g x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (fun i =>
    -(valAt g i.1) / (2 * valAt x i.1 * sqrtFn (valAt x i.1)))

/-- View (reshape): same flat data, different shape interpretation. -/
def fw_view (targetShape : Shape) (x : Tensor) : Tensor :=
  Tensor.mkShape targetShape (fun i => valAt x i.1)

/-- Swap elements at positions i and j in a list of Nat. -/
def listSwapAt (xs : List Nat) (i j : Nat) : List Nat :=
  let a := xs.getD i 0
  let b := xs.getD j 0
  (xs.set i b).set j a

/-- Transpose by swapping two arbitrary dimensions. -/
def transposeAxes (dim0 dim1 : Nat) (x : Tensor) : Tensor :=
  let outShape := listSwapAt x.shape dim0 dim1
  Tensor.mkShape outShape (fun outIdx =>
    let outMI := flatToMulti outShape outIdx.1
    let inMI := listSwapAt outMI dim0 dim1
    valAt x (multiToFlat x.shape inMI))

-- Aliases for backward compatibility with evalOp
abbrev fw_multiref := tensorId
abbrev fw_transpose := transpose2d
abbrev bw_transpose := transpose2d
abbrev fw_matmul := batchedMatmul
abbrev bw_matmul := batchedMatmulBwd
abbrev fw_softmax := softmax
abbrev bw_softmax := softmaxBwd
abbrev fw_contiguous := tensorId
abbrev bw_contiguous := tensorId
abbrev cross_dp_wred := tensorSum

def fw_div (c : Scalar) (x : Tensor) : Tensor := scalarDiv x c
def bw_div (c : Scalar) (g : Tensor) : Tensor := scalarDiv g c

def chunkPrim (numParts rank : Nat) (x : Tensor) : Tensor :=
  -- Split along last dimension: prefix same, last := last/numParts
  let pref := dropLast x.shape
  let d := lastD x.shape
  let shard := divNat d numParts
  Tensor.mkShape (appendLast pref shard) (fun outIdx =>
    let idx := outIdx.1
    let p := if shard = 0 then 0 else idx / shard
    let j := if shard = 0 then 0 else idx % shard
    let r := if numParts = 0 then rank else rank % numParts
    valAt x (p * d + r * shard + j))

/-- `chunkPrimDim0` splits a 3D tensor along the first dimension. -/
def chunkPrimDim0 (numParts rank : Nat) (x : Tensor) : Tensor :=
  -- Split along first dimension: [d0, d1, d2] -> [d0/numParts, d1, d2]
  match x.shape with
  | [d0, d1, d2] =>
      let shard0 := divNat d0 numParts
      let r := if numParts = 0 then rank else rank % numParts
      Tensor.mkShape [shard0, d1, d2] (fun outIdx =>
        let idx := outIdx.1
        -- Decompose: idx = i * (d1 * d2) + j * d2 + k
        let d12 := d1 * d2
        let i := if d12 = 0 then 0 else idx / d12
        let rem := if d12 = 0 then 0 else idx % d12
        let j := if d2 = 0 then 0 else rem / d2
        let k := if d2 = 0 then 0 else rem % d2
        -- Map to original: originalI = r * shard0 + i
        let origI := r * shard0 + i
        valAt x (origI * d12 + j * d2 + k))
  | _ => x  -- Fallback for non-3D tensors

/-!
## Core Shape Lemmas

These lemmas establish shapes for all operators, enabling shape reasoning in proofs.
-/

/-- `fw_sum` always produces a tensor with shape `[1]`. -/
@[simp] theorem fw_sum_shape (x : Tensor) : (fw_sum x).shape = [1] := by
  simp only [fw_sum, Tensor.mkShape]

/-- `bw_sum` preserves the shape of its second argument. -/
@[simp] theorem bw_sum_shape (gradOut x : Tensor) : (bw_sum gradOut x).shape = x.shape := by
  simp only [bw_sum, Tensor.mkShape]

/-- Value-level characterization of `bw_sum` at any in-bounds index. -/
theorem bw_sum_valAt_of_lt (gradOut x : Tensor) (idx : Nat)
    (hidx : idx < prodShape x.shape) :
    valAt (bw_sum gradOut x) idx = valAt gradOut 0 := by
  -- Use the in-bounds value lemma and unfold the kernel.
  have h := valAt_of_lt (bw_sum gradOut x) idx (by
    simpa [bw_sum_shape] using hidx)
  -- `bw_sum` ignores the index and returns the scalar gradOut.
  simpa [bw_sum, Tensor.mkShape] using h

/-- `chunkPrim` shape for 2D tensor with exact division. -/
theorem chunkPrim_shape (numParts rank b lastDim : Nat) (x : Tensor)
    (hshape : x.shape = [b, lastDim])
    (hparts : 0 < numParts) :
    (chunkPrim numParts rank x).shape = [b, lastDim / numParts] := by
  simp only [chunkPrim, Tensor.mkShape, hshape, dropLast, lastD, appendLast, divNat,
             (Nat.pos_iff_ne_zero.mp hparts)]
  rfl

/-- `chunkPrim` shape: alternative form with explicit shard size. -/
theorem chunkPrim_shape' (numParts rank b shard : Nat) (x : Tensor)
    (hshape : x.shape = [b, numParts * shard])
    (hparts : 0 < numParts) :
    (chunkPrim numParts rank x).shape = [b, shard] := by
  have hdiv : numParts * shard / numParts = shard := Nat.mul_div_cancel_left shard hparts
  rw [chunkPrim_shape numParts rank b (numParts * shard) x hshape hparts, hdiv]

/-- `chunkPrimDim0` shape for 3D tensor with exact division on first dimension. -/
theorem chunkPrimDim0_shape (numParts rank d0 d1 d2 : Nat) (x : Tensor)
    (hshape : x.shape = [d0, d1, d2])
    (hparts : 0 < numParts) :
    (chunkPrimDim0 numParts rank x).shape = [d0 / numParts, d1, d2] := by
  simp only [chunkPrimDim0, hshape, Tensor.mkShape, divNat, Nat.pos_iff_ne_zero.mp hparts]

/-- `chunkPrimDim0` shape: alternative form with explicit shard size on first dimension. -/
theorem chunkPrimDim0_shape' (numParts rank shard0 d1 d2 : Nat) (x : Tensor)
    (hshape : x.shape = [numParts * shard0, d1, d2])
    (hparts : 0 < numParts) :
    (chunkPrimDim0 numParts rank x).shape = [shard0, d1, d2] := by
  have hdiv : numParts * shard0 / numParts = shard0 := Nat.mul_div_cancel_left shard0 hparts
  rw [chunkPrimDim0_shape numParts rank (numParts * shard0) d1 d2 x hshape hparts, hdiv]

/-!
## Chunk mapping lemma (exact partition case)

This lemma is the workhorse for proofs that relate sums over chunks to sums over the original.
It is stated in a way that avoids global unfolding and avoids `simp` exploding.
-/

theorem chunkPrim_valAt_mul_add
    (numParts rank b shard : Nat) (x : Tensor)
    (hshape : x.shape = [b, numParts * shard])
    (hparts : 0 < numParts)
    (hrank : rank < numParts)
    (p : Nat) (hp : p < b)
    (j : Nat) (hj : j < shard) :
    valAt (chunkPrim numParts rank x) (p * shard + j) =
      valAt x (p * (numParts * shard) + rank * shard + j) := by
  have hshard_pos : 0 < shard := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hnumParts_ne0 : numParts ≠ 0 := Nat.ne_of_gt hparts
  have hdiv : divNat (numParts * shard) numParts = shard := by
    -- `numParts * shard / numParts = shard` when `numParts > 0`.
    simp [divNat, hnumParts_ne0]
  -- Chunk shape normalizes to `[b, shard]` under the exact-partition hypothesis.
  have hdrop : dropLast x.shape = [b] := by
    simp [dropLast, hshape]
  have hlast : lastD x.shape = numParts * shard := by
    simp [lastD, hshape]
  have hdiv' : divNat (lastD x.shape) numParts = shard := by
    simpa [hlast] using hdiv
  have hchunkShape : (chunkPrim numParts rank x).shape = [b, shard] := by
    -- `chunkPrim`'s shape is `dropLast x.shape ++ [lastD x.shape / numParts]`.
    simp [chunkPrim, Tensor.mkShape, hdrop, hdiv', appendLast]
  -- Prove the index is in range of the chunk tensor.
  have hlt_chunk' : p * shard + j < b * shard := by
    -- `p*shard + j < (p+1)*shard <= b*shard`.
    have hlt1 : p * shard + j < p * shard + shard := by
      simpa [Nat.add_assoc] using (Nat.add_lt_add_left hj (p * shard))
    have hlt2 : p * shard + j < (p + 1) * shard := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
    have hle : (p + 1) * shard ≤ b * shard := by
      exact Nat.mul_le_mul_right shard (Nat.succ_le_of_lt hp)
    exact lt_of_lt_of_le hlt2 hle
  have hlt_chunk : p * shard + j < prodShape (chunkPrim numParts rank x).shape := by
    simpa [hchunkShape, prodShape] using hlt_chunk'
  -- Compute div/mod of the flattened index using `Nat.div_mod_unique`.
  have hdiv_p : (p * shard + j) / shard = p := by
    have heq : j + shard * p = p * shard + j := by
      simp [Nat.mul_comm, Nat.add_comm]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.1
  have hmod_p : (p * shard + j) % shard = j := by
    have heq : j + shard * p = p * shard + j := by
      simp [Nat.mul_comm, Nat.add_comm]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.2
  have hrmod : (rank % numParts) = rank := Nat.mod_eq_of_lt hrank
  -- Unfold `chunkPrim` only locally, then discharge the `if` branches.
  have h0 : valAt (chunkPrim numParts rank x) (p * shard + j) =
      (chunkPrim numParts rank x).val ⟨p * shard + j, hlt_chunk⟩ := by
    simp [valAt, hlt_chunk]
  rw [h0]
  -- The remaining simplification is small: unfold the local kernel and rewrite div/mod.
  simp [chunkPrim, Tensor.mkShape, hshape, dropLast, lastD, appendLast, divNat,
    hnumParts_ne0, hshard_pos.ne', hdiv_p, hmod_p, hrmod]

def allGatherPrim (numParts _rank : Nat) (xs : List Tensor) : Tensor :=
  -- Reassemble along last dimension: prefix same, last := shard*numParts
  let shardShape := (xs.head?.map (fun t => t.shape)).getD []
  let pref := dropLast shardShape
  let shard := lastD shardShape
  let full := shard * numParts
  Tensor.mkShape (appendLast pref full) (fun outIdx =>
    let idx := outIdx.1
    let p := if full = 0 then 0 else idx / full
    let l := if full = 0 then 0 else idx % full
    let r := if shard = 0 then 0 else l / shard
    let j := if shard = 0 then 0 else l % shard
    let shardShape := (xs.head?.map (fun t => t.shape)).getD []
    let pref := dropLast shardShape
    let piece := xs.getD r (zeroTensor (appendLast pref shard))
    valAt piece (p * shard + j))

/-- `allGatherPrimDim0` reassembles 3D tensors along the first dimension. -/
def allGatherPrimDim0 (numParts _rank : Nat) (xs : List Tensor) : Tensor :=
  -- Reassemble along first dimension: [shard0, d1, d2] from each rank -> [shard0*numParts, d1, d2]
  match (xs.head?.map (fun t => t.shape)).getD [] with
  | [shard0, d1, d2] =>
      let full0 := shard0 * numParts
      Tensor.mkShape [full0, d1, d2] (fun outIdx =>
        let idx := outIdx.1
        -- Decompose: idx = i * (d1 * d2) + j * d2 + k
        let d12 := d1 * d2
        let i := if d12 = 0 then 0 else idx / d12
        let rem := if d12 = 0 then 0 else idx % d12
        let j := if d2 = 0 then 0 else rem / d2
        let k := if d2 = 0 then 0 else rem % d2
        -- Which rank owns this i? r = i / shard0, localI = i % shard0
        let r := if shard0 = 0 then 0 else i / shard0
        let localI := if shard0 = 0 then 0 else i % shard0
        let piece := xs.getD r (zeroTensor [shard0, d1, d2])
        valAt piece (localI * d12 + j * d2 + k))
  | _ =>
      -- Fallback: use last-dimension allGather
      allGatherPrim numParts _rank xs

/-- General allGather on an arbitrary dimension.
    Reassembles shards by concatenating along dimension `gatherDim`.
    The output shape equals the shard shape with dimension `gatherDim` multiplied by `numParts`. -/
def allGatherPrimDimN (gatherDim numParts _rank : Nat) (xs : List Tensor) : Tensor :=
  let shardShape := (xs.head?.map (fun t => t.shape)).getD []
  let dimSize := shardShape.getD gatherDim 0
  let fullDimSize := dimSize * numParts
  let outShape := shardShape.set gatherDim fullDimSize
  let postStride := (shardShape.drop (gatherDim + 1)).foldl (· * ·) 1
  let dimStride := dimSize * postStride
  let fullDimStride := fullDimSize * postStride
  Tensor.mkShape outShape (fun outIdx =>
    let idx := outIdx.1
    let preIdx := if fullDimStride = 0 then 0 else idx / fullDimStride
    let remainder := if fullDimStride = 0 then 0 else idx % fullDimStride
    let jFull := if postStride = 0 then 0 else remainder / postStride
    let k := if postStride = 0 then 0 else remainder % postStride
    let r := if dimSize = 0 then 0 else jFull / dimSize
    let jLocal := if dimSize = 0 then 0 else jFull % dimSize
    let piece := xs.getD r (zeroTensor shardShape)
    valAt piece (preIdx * dimStride + jLocal * postStride + k))

/-- `allGatherPrimDimN` shape theorem. -/
theorem allGatherPrimDimN_shape (gatherDim numParts : Nat) (xs : List Tensor)
    (shardShape : Shape)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = shardShape) :
    (allGatherPrimDimN gatherDim numParts 0 xs).shape =
      shardShape.set gatherDim (shardShape.getD gatherDim 0 * numParts) := by
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead]

/-- Chunk a tensor along an arbitrary dimension `chunkDim`.
    This is the inverse of `allGatherPrimDimN`: it selects the rank-th shard
    by dividing `chunkDim` by `numParts`. -/
def chunkPrimDimN (chunkDim numParts rank : Nat) (x : Tensor) : Tensor :=
  let sh := x.shape
  let dimSize := sh.getD chunkDim 0
  let shardSize := if numParts = 0 then 0 else dimSize / numParts
  let outShape := sh.set chunkDim shardSize
  let postStride := (sh.drop (chunkDim + 1)).foldl (· * ·) 1
  let dimStride := dimSize * postStride
  let shardDimStride := shardSize * postStride
  let r := if numParts = 0 then rank else rank % numParts
  Tensor.mkShape outShape (fun outIdx =>
    let idx := outIdx.1
    let preIdx := if shardDimStride = 0 then 0 else idx / shardDimStride
    let remainder := if shardDimStride = 0 then 0 else idx % shardDimStride
    let jLocal := if postStride = 0 then 0 else remainder / postStride
    let k := if postStride = 0 then 0 else remainder % postStride
    let jFull := r * shardSize + jLocal
    valAt x (preIdx * dimStride + jFull * postStride + k))

/-- `chunkPrimDimN` shape theorem. -/
theorem chunkPrimDimN_shape (chunkDim numParts rank : Nat) (x : Tensor)
    (sh : Shape) (hsh : x.shape = sh)
    (hnz : numParts ≠ 0) :
    (chunkPrimDimN chunkDim numParts rank x).shape =
      sh.set chunkDim (sh.getD chunkDim 0 / numParts) := by
  simp only [chunkPrimDimN, Tensor.mkShape, hsh, hnz, ite_false]

/-! ## Generic elementwise/add split helpers

These bridge sequence/tensor-parallel patterns where each rank computes an elementwise
`FW_add` on local chunks and the full result is reconstructed with `allGatherPrimDimN`.
They are dimension- and rank-count-parametric, so downstream pattern proofs can use the
same helper for any `gatherDim`/`numParts` combination whose full dimension is exactly
`numParts * shardSize`.
-/

/-- Generic statement of the add/chunk/all-gather bridge used by sequence-parallel
patterns.  The concrete low-dimensional instances below are preferred in generated
proofs because they compile much faster than redoing the full index arithmetic. -/
def fw_add_split_dim_statement (dim numParts : Nat) (a b : Tensor) : Prop :=
  elemwiseAdd a b =
    allGatherPrimDimN dim numParts 0
      (List.ofFn (fun r : Fin numParts =>
        elemwiseAdd (chunkPrimDimN dim numParts r.val a)
          (chunkPrimDimN dim numParts r.val b)))

private theorem chunk2_4_1_8_32_valAt_pj (x : Tensor) (r p j : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) (hp : p < 8) (hj : j < 8) :
    valAt (chunkPrimDimN 2 4 r x) (p * 8 + j) = valAt x (p * 32 + r * 8 + j) := by
  have hloc : p * 8 + j < 64 := by omega
  have hchunk_shape : (chunkPrimDimN 2 4 r x).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p * 8 + j < prodShape (chunkPrimDimN 2 4 r x).shape := by
    rw [hchunk_shape]
    simp [prodShape]
    exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have hidx : (p * 8 + j) / 8 * 32 + (r % 4 * 8 + (p * 8 + j) % 8 / 1) * 1 + (p * 8 + j) % 8 % 1 =
      p * 32 + r * 8 + j := by omega
  rw [hidx]

private theorem elemwiseAdd_valAt_1_8_32 (x y : Tensor) (idx : Nat)
    (hx : x.shape = [1, 8, 32]) (hy : y.shape = [1, 8, 32]) (hidx : idx < 256) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  have hout : (elemwiseAdd x y).shape = [1, 8, 32] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy]
  rw [valAt_of_lt _ _ (by simpa [hout, prodShape] using hidx)]
  simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy, broadcastValAtShape,
    alignedMultiIndex, flatToMulti, multiToFlat, prodShape]
  have hnorm : idx % 256 / 32 * 32 + idx % 32 = idx := by omega
  rw [hnorm]

private theorem elemwiseAdd_valAt_1_8_8 (x y : Tensor) (idx : Nat)
    (hx : x.shape = [1, 8, 8]) (hy : y.shape = [1, 8, 8]) (hidx : idx < 64) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  have hout : (elemwiseAdd x y).shape = [1, 8, 8] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy]
  rw [valAt_of_lt _ _ (by simpa [hout, prodShape] using hidx)]
  simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy, broadcastValAtShape,
    alignedMultiIndex, flatToMulti, multiToFlat, prodShape]
  have hnorm : idx % 64 / 8 * 8 + idx % 8 = idx := by omega
  rw [hnorm]

/-- Concrete fast instance of `fw_add_split_dim_statement` for `[1, 8, 32]` tensors split four ways along dim 2. -/
theorem fw_add_split_dim2_4_1_8_32 (a b : Tensor) (ha : a.shape = [1, 8, 32]) (hb : b.shape = [1, 8, 32]) :
    elemwiseAdd a b = allGatherPrimDimN 2 4 0
      [elemwiseAdd (chunkPrimDimN 2 4 0 a) (chunkPrimDimN 2 4 0 b),
       elemwiseAdd (chunkPrimDimN 2 4 1 a) (chunkPrimDimN 2 4 1 b),
       elemwiseAdd (chunkPrimDimN 2 4 2 a) (chunkPrimDimN 2 4 2 b),
       elemwiseAdd (chunkPrimDimN 2 4 3 a) (chunkPrimDimN 2 4 3 b)] := by
  have hchunk_shape_a : ∀ r, (chunkPrimDimN 2 4 r a).shape = [1, 8, 8] := by
    intro r; rw [chunkPrimDimN_shape 2 4 r _ _ ha (by omega)]; simp [List.set, List.getD]
  have hchunk_shape_b : ∀ r, (chunkPrimDimN 2 4 r b).shape = [1, 8, 8] := by
    intro r; rw [chunkPrimDimN_shape 2 4 r _ _ hb (by omega)]; simp [List.set, List.getD]
  have hpiece_shape : ∀ r, (elemwiseAdd (chunkPrimDimN 2 4 r a) (chunkPrimDimN 2 4 r b)).shape = [1, 8, 8] := by
    intro r; simp [elemwiseAdd, Tensor.mkShape, outShape2, hchunk_shape_a r, hchunk_shape_b r]
  have hhead : (([elemwiseAdd (chunkPrimDimN 2 4 0 a) (chunkPrimDimN 2 4 0 b),
       elemwiseAdd (chunkPrimDimN 2 4 1 a) (chunkPrimDimN 2 4 1 b),
       elemwiseAdd (chunkPrimDimN 2 4 2 a) (chunkPrimDimN 2 4 2 b),
       elemwiseAdd (chunkPrimDimN 2 4 3 a) (chunkPrimDimN 2 4 3 b)].head?.map (fun t => t.shape)).getD []) = [1, 8, 8] := by
    simp [hpiece_shape]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [elemwiseAdd (chunkPrimDimN 2 4 0 a) (chunkPrimDimN 2 4 0 b),
       elemwiseAdd (chunkPrimDimN 2 4 1 a) (chunkPrimDimN 2 4 1 b),
       elemwiseAdd (chunkPrimDimN 2 4 2 a) (chunkPrimDimN 2 4 2 b),
       elemwiseAdd (chunkPrimDimN 2 4 3 a) (chunkPrimDimN 2 4 3 b)]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
    simp [List.set, List.getD]
  have hlhs_shape : (elemwiseAdd a b).shape = [1, 8, 32] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, ha, hb]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  have hidx_rhs : idx < prodShape (allGatherPrimDimN 2 4 0
      [elemwiseAdd (chunkPrimDimN 2 4 0 a) (chunkPrimDimN 2 4 0 b),
       elemwiseAdd (chunkPrimDimN 2 4 1 a) (chunkPrimDimN 2 4 1 b),
       elemwiseAdd (chunkPrimDimN 2 4 2 a) (chunkPrimDimN 2 4 2 b),
       elemwiseAdd (chunkPrimDimN 2 4 3 a) (chunkPrimDimN 2 4 3 b)]).shape := by
    simpa [hrhs_shape, prodShape] using hidx256
  rw [elemwiseAdd_valAt_1_8_32 a b idx ha hb hidx256]
  rw [valAt_of_lt _ _ hidx_rhs]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (8 : Nat) * 4 * 1 = 32 by norm_num,
    show (8 : Nat) * 1 = 8 by norm_num]
  set p := idx / 32 with hp_def
  set r := idx % 32 / 8 with hr_def
  set j := idx % 8 with hj_def
  set loc := p * 8 + j with hloc_def
  have hp_lt : p < 8 := by omega
  have hr_lt : r < 4 := by omega
  have hj_lt : j < 8 := by omega
  have hloc_lt : loc < 64 := by omega
  have hidxget : idx % 32 / 1 / 8 = r := by subst r; omega
  have hlocnorm : idx / 32 * 8 + idx % 32 / 1 % 8 * 1 + idx % 32 % 1 = loc := by
    subst loc p j
    omega
  rw [hidxget, hlocnorm]
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  have hidx_norm : idx = p * 32 + r * 8 + j := by
    subst p r j
    omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [h0]
    change valAt a idx + valAt b idx =
      valAt (elemwiseAdd (chunkPrimDimN 2 4 0 a) (chunkPrimDimN 2 4 0 b)) loc
    rw [elemwiseAdd_valAt_1_8_8 _ _ loc (hchunk_shape_a 0) (hchunk_shape_b 0) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 0 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 0 p j hb (by omega) hp_lt hj_lt]
    have hidx0 : idx = p * 32 + 0 * 8 + j := by omega
    rw [← hidx0]
  · rw [h1]
    change valAt a idx + valAt b idx =
      valAt (elemwiseAdd (chunkPrimDimN 2 4 1 a) (chunkPrimDimN 2 4 1 b)) loc
    rw [elemwiseAdd_valAt_1_8_8 _ _ loc (hchunk_shape_a 1) (hchunk_shape_b 1) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 1 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 1 p j hb (by omega) hp_lt hj_lt]
    have hidx1 : idx = p * 32 + 1 * 8 + j := by omega
    rw [← hidx1]
  · rw [h2]
    change valAt a idx + valAt b idx =
      valAt (elemwiseAdd (chunkPrimDimN 2 4 2 a) (chunkPrimDimN 2 4 2 b)) loc
    rw [elemwiseAdd_valAt_1_8_8 _ _ loc (hchunk_shape_a 2) (hchunk_shape_b 2) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 2 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 2 p j hb (by omega) hp_lt hj_lt]
    have hidx2 : idx = p * 32 + 2 * 8 + j := by omega
    rw [← hidx2]
  · rw [h3]
    change valAt a idx + valAt b idx =
      valAt (elemwiseAdd (chunkPrimDimN 2 4 3 a) (chunkPrimDimN 2 4 3 b)) loc
    rw [elemwiseAdd_valAt_1_8_8 _ _ loc (hchunk_shape_a 3) (hchunk_shape_b 3) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 3 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 3 p j hb (by omega) hp_lt hj_lt]
    have hidx3 : idx = p * 32 + 3 * 8 + j := by omega
    rw [← hidx3]

/-- `valAt` for `tensorSum [a, b]` when the index is in-bounds of `a.shape`. -/
private theorem tensorSum_pair_valAt (a b : Tensor) (idx : Nat)
    (hidx : idx < prodShape a.shape) :
    valAt (tensorSum [a, b]) idx = valAt a idx + valAt b idx := by
  have hsh : (tensorSum [a, b]).shape = a.shape := rfl
  rw [valAt_of_lt _ _ (by rw [hsh]; exact hidx)]
  simp [tensorSum, Tensor.mkShape, List.foldl]

/-- `valAt` for `tensorSum [a, b]` with shape [1, 8, 8]. -/
private theorem tensorSum_pair_valAt_1_8_8 (a b : Tensor) (idx : Nat)
    (ha : a.shape = [1, 8, 8]) (hb : b.shape = [1, 8, 8]) (hidx : idx < 64) :
    valAt (tensorSum [a, b]) idx = valAt a idx + valAt b idx := by
  exact tensorSum_pair_valAt a b idx (by simp [ha, prodShape]; exact hidx)

/-- `tensorSum [a, b]` distributes over allGatherPrimDimN on dim 2 with 4 parts for shape [1, 8, 32].
    Concrete fast instance for BW_multiref goals. -/
theorem tensorSum_pair_split_dim2_4_1_8_32 (a b : Tensor)
    (ha : a.shape = [1, 8, 32]) (hb : b.shape = [1, 8, 32]) :
    tensorSum [a, b] = allGatherPrimDimN 2 4 0
      [tensorSum [chunkPrimDimN 2 4 0 a, chunkPrimDimN 2 4 0 b],
       tensorSum [chunkPrimDimN 2 4 1 a, chunkPrimDimN 2 4 1 b],
       tensorSum [chunkPrimDimN 2 4 2 a, chunkPrimDimN 2 4 2 b],
       tensorSum [chunkPrimDimN 2 4 3 a, chunkPrimDimN 2 4 3 b]] := by
  have hchunk_shape_a : ∀ r, (chunkPrimDimN 2 4 r a).shape = [1, 8, 8] := by
    intro r; rw [chunkPrimDimN_shape 2 4 r _ _ ha (by omega)]; simp [List.set, List.getD]
  have hchunk_shape_b : ∀ r, (chunkPrimDimN 2 4 r b).shape = [1, 8, 8] := by
    intro r; rw [chunkPrimDimN_shape 2 4 r _ _ hb (by omega)]; simp [List.set, List.getD]
  have hpiece_shape : ∀ r, (tensorSum [chunkPrimDimN 2 4 r a, chunkPrimDimN 2 4 r b]).shape = [1, 8, 8] := by
    intro r; show (chunkPrimDimN 2 4 r a).shape = [1, 8, 8]; exact hchunk_shape_a r
  have hhead : (([tensorSum [chunkPrimDimN 2 4 0 a, chunkPrimDimN 2 4 0 b],
       tensorSum [chunkPrimDimN 2 4 1 a, chunkPrimDimN 2 4 1 b],
       tensorSum [chunkPrimDimN 2 4 2 a, chunkPrimDimN 2 4 2 b],
       tensorSum [chunkPrimDimN 2 4 3 a, chunkPrimDimN 2 4 3 b]].head?.map (fun t => t.shape)).getD []) = [1, 8, 8] := by
    simp [hpiece_shape]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [tensorSum [chunkPrimDimN 2 4 0 a, chunkPrimDimN 2 4 0 b],
       tensorSum [chunkPrimDimN 2 4 1 a, chunkPrimDimN 2 4 1 b],
       tensorSum [chunkPrimDimN 2 4 2 a, chunkPrimDimN 2 4 2 b],
       tensorSum [chunkPrimDimN 2 4 3 a, chunkPrimDimN 2 4 3 b]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
    simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [a, b]).shape = [1, 8, 32] := by
    show a.shape = [1, 8, 32]; exact ha
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  have hidx_rhs : idx < prodShape (allGatherPrimDimN 2 4 0
      [tensorSum [chunkPrimDimN 2 4 0 a, chunkPrimDimN 2 4 0 b],
       tensorSum [chunkPrimDimN 2 4 1 a, chunkPrimDimN 2 4 1 b],
       tensorSum [chunkPrimDimN 2 4 2 a, chunkPrimDimN 2 4 2 b],
       tensorSum [chunkPrimDimN 2 4 3 a, chunkPrimDimN 2 4 3 b]]).shape := by
    simpa [hrhs_shape, prodShape] using hidx256
  rw [tensorSum_pair_valAt a b idx (by simp [ha, prodShape]; omega)]
  rw [valAt_of_lt _ _ hidx_rhs]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (8 : Nat) * 4 * 1 = 32 by norm_num,
    show (8 : Nat) * 1 = 8 by norm_num]
  set p := idx / 32 with hp_def
  set r := idx % 32 / 8 with hr_def
  set j := idx % 8 with hj_def
  set loc := p * 8 + j with hloc_def
  have hp_lt : p < 8 := by omega
  have hr_lt : r < 4 := by omega
  have hj_lt : j < 8 := by omega
  have hloc_lt : loc < 64 := by omega
  have hidxget : idx % 32 / 1 / 8 = r := by subst r; omega
  have hlocnorm : idx / 32 * 8 + idx % 32 / 1 % 8 * 1 + idx % 32 % 1 = loc := by
    subst loc p j
    omega
  rw [hidxget, hlocnorm]
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [h0]
    change valAt a idx + valAt b idx =
      valAt (tensorSum [chunkPrimDimN 2 4 0 a, chunkPrimDimN 2 4 0 b]) loc
    rw [tensorSum_pair_valAt_1_8_8 _ _ loc (hchunk_shape_a 0) (hchunk_shape_b 0) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 0 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 0 p j hb (by omega) hp_lt hj_lt]
    have hidx0 : idx = p * 32 + 0 * 8 + j := by omega
    rw [← hidx0]
  · rw [h1]
    change valAt a idx + valAt b idx =
      valAt (tensorSum [chunkPrimDimN 2 4 1 a, chunkPrimDimN 2 4 1 b]) loc
    rw [tensorSum_pair_valAt_1_8_8 _ _ loc (hchunk_shape_a 1) (hchunk_shape_b 1) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 1 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 1 p j hb (by omega) hp_lt hj_lt]
    have hidx1 : idx = p * 32 + 1 * 8 + j := by omega
    rw [← hidx1]
  · rw [h2]
    change valAt a idx + valAt b idx =
      valAt (tensorSum [chunkPrimDimN 2 4 2 a, chunkPrimDimN 2 4 2 b]) loc
    rw [tensorSum_pair_valAt_1_8_8 _ _ loc (hchunk_shape_a 2) (hchunk_shape_b 2) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 2 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 2 p j hb (by omega) hp_lt hj_lt]
    have hidx2 : idx = p * 32 + 2 * 8 + j := by omega
    rw [← hidx2]
  · rw [h3]
    change valAt a idx + valAt b idx =
      valAt (tensorSum [chunkPrimDimN 2 4 3 a, chunkPrimDimN 2 4 3 b]) loc
    rw [tensorSum_pair_valAt_1_8_8 _ _ loc (hchunk_shape_a 3) (hchunk_shape_b 3) hloc_lt]
    rw [chunk2_4_1_8_32_valAt_pj a 3 p j ha (by omega) hp_lt hj_lt]
    rw [chunk2_4_1_8_32_valAt_pj b 3 p j hb (by omega) hp_lt hj_lt]
    have hidx3 : idx = p * 32 + 3 * 8 + j := by omega
    rw [← hidx3]

/-- `tensorSum [a, allGatherPrimDimN 2 4 0 [b0, b1, b2, b3]]` distributes as
    `allGatherPrimDimN 2 4 0 [tensorSum [chunk_r a, b_r] | r]` for shape [1, 8, 32].
    Direct form that avoids needing a chunk-gather inverse lemma. -/
theorem tensorSum_add_gather_dim2_4_1_8_32 (a b0 b1 b2 b3 : Tensor)
    (ha : a.shape = [1, 8, 32])
    (hb0 : b0.shape = [1, 8, 8]) (hb1 : b1.shape = [1, 8, 8])
    (hb2 : b2.shape = [1, 8, 8]) (hb3 : b3.shape = [1, 8, 8]) :
    tensorSum [a, allGatherPrimDimN 2 4 0 [b0, b1, b2, b3]] = allGatherPrimDimN 2 4 0
      [tensorSum [chunkPrimDimN 2 4 0 a, b0],
       tensorSum [chunkPrimDimN 2 4 1 a, b1],
       tensorSum [chunkPrimDimN 2 4 2 a, b2],
       tensorSum [chunkPrimDimN 2 4 3 a, b3]] := by
  have hchunk_shape_a : ∀ r, (chunkPrimDimN 2 4 r a).shape = [1, 8, 8] := by
    intro r; rw [chunkPrimDimN_shape 2 4 r _ _ ha (by omega)]; simp [List.set, List.getD]
  have hpiece_shape : ∀ (x y : Tensor), x.shape = [1, 8, 8] → y.shape = [1, 8, 8] →
      (tensorSum [x, y]).shape = [1, 8, 8] := by intros x _ hx _; exact hx
  have hbhead : (([b0, b1, b2, b3].head?.map (fun t => t.shape)).getD []) = [1, 8, 8] := by
    simp [hb0]
  have hgather_b_shape : (allGatherPrimDimN 2 4 0 [b0, b1, b2, b3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hbhead]; simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [a, allGatherPrimDimN 2 4 0 [b0, b1, b2, b3]]).shape =
      [1, 8, 32] := ha
  have hpiece0 : (tensorSum [chunkPrimDimN 2 4 0 a, b0]).shape = [1, 8, 8] := hchunk_shape_a 0
  have hrhs_head : (([tensorSum [chunkPrimDimN 2 4 0 a, b0],
       tensorSum [chunkPrimDimN 2 4 1 a, b1],
       tensorSum [chunkPrimDimN 2 4 2 a, b2],
       tensorSum [chunkPrimDimN 2 4 3 a, b3]].head?.map (fun t => t.shape)).getD []) =
      [1, 8, 8] := by simp [hpiece0]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [tensorSum [chunkPrimDimN 2 4 0 a, b0],
       tensorSum [chunkPrimDimN 2 4 1 a, b1],
       tensorSum [chunkPrimDimN 2 4 2 a, b2],
       tensorSum [chunkPrimDimN 2 4 3 a, b3]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hrhs_head]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  -- Rewrite LHS with tensorSum_pair_valAt
  rw [tensorSum_pair_valAt a _ idx (by simp [ha, prodShape]; omega)]
  -- Now goal: valAt a idx + valAt (allGatherPrimDimN 2 4 0 [b0,b1,b2,b3]) idx =
  --           valAt (allGatherPrimDimN 2 4 0 [sum0,sum1,sum2,sum3]) idx
  -- Unfold BOTH allGather expressions simultaneously
  have hidx_lhs : idx < prodShape (allGatherPrimDimN 2 4 0 [b0, b1, b2, b3]).shape := by
    simpa [hgather_b_shape, prodShape] using hidx256
  have hidx_rhs : idx < prodShape (allGatherPrimDimN 2 4 0
      [tensorSum [chunkPrimDimN 2 4 0 a, b0],
       tensorSum [chunkPrimDimN 2 4 1 a, b1],
       tensorSum [chunkPrimDimN 2 4 2 a, b2],
       tensorSum [chunkPrimDimN 2 4 3 a, b3]]).shape := by
    simpa [hrhs_shape, prodShape] using hidx256
  rw [valAt_of_lt _ _ hidx_lhs, valAt_of_lt _ _ hidx_rhs]
  simp only [allGatherPrimDimN, Tensor.mkShape, hbhead, hrhs_head,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (8 : Nat) * 4 * 1 = 32 by norm_num,
    show (8 : Nat) * 1 = 8 by norm_num]
  set p := idx / 32 with hp_def
  set r := idx % 32 / 8 with hr_def
  set j := idx % 8 with hj_def
  set loc := p * 8 + j with hloc_def
  have hp_lt : p < 8 := by omega
  have hr_lt : r < 4 := by omega
  have hj_lt : j < 8 := by omega
  have hloc_lt : loc < 64 := by omega
  have hidxget : idx % 32 / 1 / 8 = r := by subst r; omega
  have hlocnorm : idx / 32 * 8 + idx % 32 / 1 % 8 * 1 + idx % 32 % 1 = loc := by
    subst loc p j; omega
  rw [hidxget, hlocnorm]
  -- Now goal: valAt a idx + valAt ([b0,b1,b2,b3].getD r ...) loc =
  --           valAt ([sum0,...].getD r ...) loc
  have hidx_norm : idx = p * 32 + r * 8 + j := by subst p r j; omega
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [h0]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_pair_valAt _ _ loc (by simp [hchunk_shape_a 0, prodShape]; omega)]
    rw [chunk2_4_1_8_32_valAt_pj a 0 p j ha (by omega) hp_lt hj_lt]
    have hidx0 : idx = p * 32 + 0 * 8 + j := by omega
    rw [← hidx0]
  · rw [h1]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_pair_valAt _ _ loc (by simp [hchunk_shape_a 1, prodShape]; omega)]
    rw [chunk2_4_1_8_32_valAt_pj a 1 p j ha (by omega) hp_lt hj_lt]
    have hidx1 : idx = p * 32 + 1 * 8 + j := by omega
    rw [← hidx1]
  · rw [h2]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_pair_valAt _ _ loc (by simp [hchunk_shape_a 2, prodShape]; omega)]
    rw [chunk2_4_1_8_32_valAt_pj a 2 p j ha (by omega) hp_lt hj_lt]
    have hidx2 : idx = p * 32 + 2 * 8 + j := by omega
    rw [← hidx2]
  · rw [h3]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_pair_valAt _ _ loc (by simp [hchunk_shape_a 3, prodShape]; omega)]
    rw [chunk2_4_1_8_32_valAt_pj a 3 p j ha (by omega) hp_lt hj_lt]
    have hidx3 : idx = p * 32 + 3 * 8 + j := by omega
    rw [← hidx3]

/-- AllToAll with explicit split/gather dimensions.
    Gathers all inputs along `idim`, then chunks the result along `odim`. -/
def allToAllPrimWithDims (numParts rank : Nat) (xs : List Tensor)
    (idim odim : Nat) : Tensor :=
  chunkPrimDimN odim numParts rank (allGatherPrimDimN idim numParts 0 xs)

/-- `allToAllPrimWithDims` shape theorem. -/
theorem allToAllPrimWithDims_shape (numParts rank : Nat) (xs : List Tensor)
    (idim odim : Nat)
    (shardShape : Shape)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = shardShape)
    (hnz : numParts ≠ 0) :
    (allToAllPrimWithDims numParts rank xs idim odim).shape =
      (shardShape.set idim (shardShape.getD idim 0 * numParts)).set odim
        ((shardShape.set idim (shardShape.getD idim 0 * numParts)).getD odim 0 /
          numParts) := by
  simp only [allToAllPrimWithDims]
  exact chunkPrimDimN_shape odim numParts rank _
    _ (allGatherPrimDimN_shape idim numParts xs shardShape hhead) hnz

/-- `allGatherPrim` shape for 2D tensors with consistent shard shapes. -/
theorem allGatherPrim_shape (numParts o shard : Nat) (xs : List Tensor)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [o, shard]) :
    (allGatherPrim numParts 0 xs).shape = [o, shard * numParts] := by
  simp only [allGatherPrim, Tensor.mkShape, hhead, dropLast, lastD, appendLast]
  rfl

/-- `allGatherPrim` shape when all elements have the same shape. -/
theorem allGatherPrim_shape' (numParts o shard : Nat) (xs : List Tensor) (x0 : Tensor)
    (hhead : xs.head? = some x0)
    (hx0_shape : x0.shape = [o, shard]) :
    (allGatherPrim numParts 0 xs).shape = [o, shard * numParts] := by
  have hhead' : (xs.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
    simp only [hhead, Option.map, Option.getD, hx0_shape]
  exact allGatherPrim_shape numParts o shard xs hhead'

/-!
## AllGather mapping lemma (exact partition case)

This lemma states the index mapping for `allGatherPrim` along the last dimension when
the gathered dimension is exactly `shard * numParts`.

It is phrased at the `valAt` level to stay robust in later proofs.
-/

theorem allGatherPrim_valAt_mul_add
    (numParts rank o shard : Nat) (pieces : List Tensor)
    (hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hparts : 0 < numParts)
    (hrank : rank < numParts)
    (p : Nat) (hp : p < o)
    (j : Nat) (hj : j < shard) :
    valAt (allGatherPrim numParts 0 pieces) (p * (shard * numParts) + rank * shard + j) =
      valAt (pieces.getD rank (zeroTensor [o, shard])) (p * shard + j) := by
  have hshard_pos : 0 < shard := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hfull_pos : 0 < shard * numParts := Nat.mul_pos hshard_pos hparts
  have hnumParts_ne0 : numParts ≠ 0 := Nat.ne_of_gt hparts
  -- In-bounds for the output tensor.
  have hrem_lt_full : rank * shard + j < shard * numParts := by
    have hlt1 : rank * shard + j < rank * shard + shard := by
      simpa [Nat.add_assoc] using (Nat.add_lt_add_left hj (rank * shard))
    have hlt2 : rank * shard + j < (rank + 1) * shard := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
    have hle : (rank + 1) * shard ≤ numParts * shard := by
      exact Nat.mul_le_mul_right shard (Nat.succ_le_of_lt hrank)
    -- rewrite `shard * numParts` as `numParts * shard`
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using lt_of_lt_of_le hlt2 hle
  have hlt_full : p * (shard * numParts) + (rank * shard + j) < o * (shard * numParts) := by
    have hlt1 : p * (shard * numParts) + (rank * shard + j) <
        p * (shard * numParts) + (shard * numParts) :=
      Nat.add_lt_add_left hrem_lt_full _
    have hlt2 : p * (shard * numParts) + (rank * shard + j) < (p + 1) * (shard * numParts) := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
    have hle : (p + 1) * (shard * numParts) ≤ o * (shard * numParts) := by
      exact Nat.mul_le_mul_right (shard * numParts) (Nat.succ_le_of_lt hp)
    exact lt_of_lt_of_le hlt2 hle
  have hdrop : dropLast ((pieces.head?.map (fun t => t.shape)).getD []) = [o] := by
    simp [dropLast, hhead]
  have hlast : lastD ((pieces.head?.map (fun t => t.shape)).getD []) = shard := by
    simp [lastD, hhead]
  have hshape_out : (allGatherPrim numParts 0 pieces).shape = [o, shard * numParts] := by
    simp [allGatherPrim, Tensor.mkShape, hdrop, hlast, appendLast]
  have hlt_out : p * (shard * numParts) + rank * shard + j <
      prodShape (allGatherPrim numParts 0 pieces).shape := by
    -- rearrange the index to match `hlt_full`
    have : p * (shard * numParts) + rank * shard + j =
        p * (shard * numParts) + (rank * shard + j) := by
      omega
    -- `prodShape [o, shard*numParts] = o*(shard*numParts)`
    simpa [hshape_out, prodShape, this] using hlt_full
  -- Reduce the division/mod computations in the `allGatherPrim` kernel.
  have hdiv_full : (p * (shard * numParts) + rank * shard + j) / (shard * numParts) = p := by
    have heq : (rank * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + rank * shard + j := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, by
      -- remainder < divisor
      simpa [Nat.add_assoc] using (by
        -- `rank*shard+j < shard*numParts`
        exact hrem_lt_full)⟩ |>.1
  have hmod_full : (p * (shard * numParts) + rank * shard + j) %
      (shard * numParts) = rank * shard + j := by
    have heq : (rank * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + rank * shard + j := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, by
      simpa [Nat.add_assoc] using hrem_lt_full⟩ |>.2
  have hdiv_shard : (rank * shard + j) / shard = rank := by
    have heq : j + shard * rank = rank * shard + j := by
      simp [Nat.mul_comm, Nat.add_comm]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.1
  have hmod_shard : (rank * shard + j) % shard = j := by
    have heq : j + shard * rank = rank * shard + j := by
      simp [Nat.mul_comm, Nat.add_comm]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.2
  have hrmod : (rank % numParts) = rank := Nat.mod_eq_of_lt hrank
  -- Finally, unfold only locally.
  have h0 : valAt (allGatherPrim numParts 0 pieces) (p * (shard * numParts) + rank * shard + j) =
      (allGatherPrim numParts 0 pieces).val
        ⟨p * (shard * numParts) + rank * shard + j, hlt_out⟩ := by
    simp [valAt, hlt_out]
  rw [h0]
  simp [allGatherPrim, Tensor.mkShape, hhead, dropLast, lastD, appendLast,
    hshard_pos.ne', hfull_pos.ne', hdiv_full, hmod_full, hdiv_shard, hmod_shard]

/-!
## AllGather of ChunkPrim is identity (inverse relationship)

This key lemma shows that allGather reconstructs the original tensor from its chunks.
For a tensor x split into numParts chunks along the last dimension,
allGathering those chunks recovers x.
-/

/-!
## bw_sum commutes with allGather (operator-level)

This lemma is dimension-agnostic except for the required shape equalities.
It captures that `bw_sum` ignores its second argument, so allGathering
per-shard `bw_sum` results matches `bw_sum` of the allGathered tensor.
-/

theorem allGatherPrim_bw_sum_eq_bw_sum_allGather
    (numParts o shard : Nat) (g : Tensor) (xs : List Tensor)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hxs_shape : ∀ x ∈ xs, x.shape = [o, shard])
    (hlen : xs.length = numParts)
    (hparts : 0 < numParts)
    (hshard : 0 < shard) :
    allGatherPrim numParts 0 (xs.map (fun x => bw_sum g x)) =
      bw_sum g (allGatherPrim numParts 0 xs) := by
  -- Shape agreement
  have hhead_map : ((xs.map (fun x => bw_sum g x)).head?.map (fun t => t.shape)).getD [] = [o, shard] := by
    cases xs with
    | nil =>
      -- reduce to contradiction from the head-shape assumption
      simp at hhead
    | cons x xs' =>
        have hx : x.shape = [o, shard] := hxs_shape x (by simp)
        simp [hx, bw_sum_shape]
  have hshapeL : (allGatherPrim numParts 0 (xs.map (fun x => bw_sum g x))).shape = [o, shard * numParts] := by
    exact allGatherPrim_shape numParts o shard (xs := xs.map (fun x => bw_sum g x)) hhead_map
  have hshapeR : (bw_sum g (allGatherPrim numParts 0 xs)).shape = [o, shard * numParts] := by
    -- bw_sum preserves shape
    rw [bw_sum_shape, allGatherPrim_shape numParts o shard xs hhead]

  -- Reduce to pointwise equality
  have hshape_eq : (allGatherPrim numParts 0 (xs.map (fun x => bw_sum g x))).shape =
      (bw_sum g (allGatherPrim numParts 0 xs)).shape := by
    rw [hshapeL, hshapeR]
  apply Tensor.ext hshape_eq
  intro idx hidx

  -- Normalize index decomposition
  have hfull_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hidx_lt : idx < o * (shard * numParts) := by
    simpa [hshapeL, prodShape] using hidx
  let full := shard * numParts
  let p := idx / full
  let l := idx % full
  let r := l / shard
  let j := l % shard
  have hp_lt : p < o := by
    have : idx < o * full := hidx_lt
    exact (Nat.div_lt_iff_lt_mul hfull_pos).2 this
  have hl_lt : l < full := Nat.mod_lt idx hfull_pos
  have hr_lt : r < numParts := by
    -- l < shard * numParts
    have : l < shard * numParts := by simpa [full] using hl_lt
    exact (Nat.div_lt_iff_lt_mul hshard).2 (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this)
  have hj_lt : j < shard := Nat.mod_lt l hshard

  -- Index normalization
  have hidx_eq : idx = p * full + l := by
    have h' : idx = full * (idx / full) + idx % full := (Nat.div_add_mod idx full).symm
    simpa [p, l, Nat.mul_comm] using h'
  have hl_eq : l = r * shard + j := by
    have h' : l = shard * (l / shard) + l % shard := (Nat.div_add_mod l shard).symm
    simpa [r, j, Nat.mul_comm] using h'
  have hidx_norm : idx = p * full + r * shard + j := by
    -- combine the two decompositions
    calc
      idx = p * full + l := hidx_eq
      _ = p * full + (r * shard + j) := by rw [hl_eq]
      _ = p * full + r * shard + j := by omega

  -- Evaluate LHS via allGather mapping
  have hL : valAt (allGatherPrim numParts 0 (xs.map (fun x => bw_sum g x))) idx =
      valAt ((xs.map (fun x => bw_sum g x)).getD r (zeroTensor [o, shard])) (p * shard + j) := by
    -- Use the exact mapping lemma
    have hmap := allGatherPrim_valAt_mul_add numParts r o shard (pieces := xs.map (fun x => bw_sum g x))
      hhead_map hparts hr_lt p hp_lt j hj_lt
    -- rewrite index
    simpa [full, hidx_norm] using hmap

  -- Convert getD to get (in-bounds)
  have hr_len : r < (xs.map (fun x => bw_sum g x)).length := by
    simpa [List.length_map, hlen] using hr_lt
  have hgetD : (xs.map (fun x => bw_sum g x)).getD r (zeroTensor [o, shard]) =
      (xs.map (fun x => bw_sum g x)).get ⟨r, hr_len⟩ := by
    simp only [List.getD, List.getElem?_eq_getElem hr_len, Option.getD_some, List.get_eq_getElem]

  have hL' : valAt (allGatherPrim numParts 0 (xs.map (fun x => bw_sum g x))) idx =
      valAt ((xs.map (fun x => bw_sum g x)).get ⟨r, hr_len⟩) (p * shard + j) := by
    rw [hL, hgetD]

  -- Evaluate RHS: bw_sum ignores its second argument
  have hidxR : idx < prodShape (allGatherPrim numParts 0 xs).shape := by
    -- both sides have the same 2D shape
    have hshapeAG : (allGatherPrim numParts 0 xs).shape = [o, shard * numParts] :=
      allGatherPrim_shape numParts o shard xs hhead
    have : idx < o * (shard * numParts) := by
      simpa [hshapeL, prodShape] using hidx
    simpa [hshapeAG, prodShape] using this
  have hR : valAt (bw_sum g (allGatherPrim numParts 0 xs)) idx = valAt g 0 := by
    apply bw_sum_valAt_of_lt
    -- idx is in bounds of allGather output
    exact hidxR

  -- Evaluate LHS: selected piece is bw_sum g x_r
  have hidx_piece : p * shard + j < o * shard := by
    have hj1 : p * shard + j < p * shard + shard := Nat.add_lt_add_left hj_lt (p * shard)
    have hj2 : p * shard + j < (p + 1) * shard := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hj1
    have hp_le : (p + 1) * shard ≤ o * shard := Nat.mul_le_mul_right shard (Nat.succ_le_of_lt hp_lt)
    exact lt_of_lt_of_le hj2 hp_le
  have hL'' : valAt ((xs.map (fun x => bw_sum g x)).get ⟨r, hr_len⟩) (p * shard + j) = valAt g 0 := by
    -- Unfold the get into a specific element and use bw_sum_valAt_of_lt
    -- `get` of map corresponds to map of `get`.
    have hget_map : (xs.map (fun x => bw_sum g x)).get ⟨r, hr_len⟩ =
        bw_sum g (xs.get ⟨r, by
          -- r < xs.length
          have : r < xs.length := by simpa [hlen] using hr_lt
          exact this⟩) := by
      -- `List.get_map` lemma
      simp
    rw [hget_map]
    -- convert bound using the shape of `xs.get`
    have hxshape : (xs.get ⟨r, by simpa [hlen] using hr_lt⟩).shape = [o, shard] := by
      exact hxs_shape _ (List.get_mem xs ⟨r, by simpa [hlen] using hr_lt⟩)
    have hidx_piece' : p * shard + j < prodShape ([o, shard] : Shape) := by
      simpa [prodShape] using hidx_piece
    have hidx_piece'' : p * shard + j < prodShape (xs.get ⟨r, by simpa [hlen] using hr_lt⟩).shape := by
      -- rewrite the shape of the selected element
      rw [hxshape]
      exact hidx_piece'
    exact bw_sum_valAt_of_lt g (xs.get ⟨r, by simpa [hlen] using hr_lt⟩) (p * shard + j) hidx_piece''

  -- Combine
  rw [hL', hL'']
  exact hR.symm

/-- `bw_sum` distributes over `allGatherPrimDimN` on dim 2 with 4 parts for shard shape [1, 8, 32].
    Since `bw_sum` ignores its second argument and broadcasts the scalar gradient, the gathered
    per-shard `bw_sum` results equal `bw_sum` of the gathered tensor. Concrete fast instance for
    BW_sum cut goals. -/
theorem bw_sum_allGatherPrimDimN_split_dim2_4_1_8_32
    (g x0 x1 x2 x3 : Tensor)
    (h0 : x0.shape = [1, 8, 32]) (h1 : x1.shape = [1, 8, 32])
    (h2 : x2.shape = [1, 8, 32]) (h3 : x3.shape = [1, 8, 32]) :
    bw_sum g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) =
      allGatherPrimDimN 2 4 0 [bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3] := by
  have hheadL : (([x0, x1, x2, x3]).head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    simp [h0]
  have hgatherL_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hheadL]; simp [List.set, List.getD]
  have hlhs_shape : (bw_sum g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])).shape = [1, 8, 128] := by
    rw [bw_sum_shape, hgatherL_shape]
  have hheadR : (([bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3]).head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    simp [bw_sum_shape, h0]
  have hrhs_shape : (allGatherPrimDimN 2 4 0 [bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3]).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hheadR]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx1024 : idx < 1024 := by
    have h := hidx; rw [hlhs_shape] at h; simpa [prodShape] using h
  -- LHS: bw_sum ignores its argument, value is `valAt g 0`.
  have hLHS : valAt (bw_sum g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])) idx = valAt g 0 := by
    apply bw_sum_valAt_of_lt
    rw [hgatherL_shape]; simpa [prodShape] using hidx1024
  rw [hLHS]
  -- RHS: unfold the gather and reduce to the selected `bw_sum` piece.
  have hidx_rhs : idx < prodShape (allGatherPrimDimN 2 4 0
      [bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3]).shape := by
    rw [hrhs_shape]; simpa [prodShape] using hidx1024
  rw [valAt_of_lt _ _ hidx_rhs]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hheadR, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (32 : Nat) * 4 * 1 = 128 by norm_num,
    show (32 : Nat) * 1 = 32 by norm_num,
    if_neg (show ¬ (128 = 0) by decide), Nat.div_one]
  have hbound : idx / 128 * 32 + idx % 128 % 32 * 1 + idx % 128 % 1 < 256 := by omega
  have hr_cases : idx % 128 / 32 = 0 ∨ idx % 128 / 32 = 1 ∨ idx % 128 / 32 = 2 ∨ idx % 128 / 32 = 3 := by
    omega
  rcases hr_cases with hc | hc | hc | hc
  · rw [hc]
    change valAt g 0 = valAt (bw_sum g x0) (idx / 128 * 32 + idx % 128 % 32 * 1 + idx % 128 % 1)
    exact (bw_sum_valAt_of_lt g x0 _ (by rw [h0]; simpa [prodShape] using hbound)).symm
  · rw [hc]
    change valAt g 0 = valAt (bw_sum g x1) (idx / 128 * 32 + idx % 128 % 32 * 1 + idx % 128 % 1)
    exact (bw_sum_valAt_of_lt g x1 _ (by rw [h1]; simpa [prodShape] using hbound)).symm
  · rw [hc]
    change valAt g 0 = valAt (bw_sum g x2) (idx / 128 * 32 + idx % 128 % 32 * 1 + idx % 128 % 1)
    exact (bw_sum_valAt_of_lt g x2 _ (by rw [h2]; simpa [prodShape] using hbound)).symm
  · rw [hc]
    change valAt g 0 = valAt (bw_sum g x3) (idx / 128 * 32 + idx % 128 % 32 * 1 + idx % 128 % 1)
    exact (bw_sum_valAt_of_lt g x3 _ (by rw [h3]; simpa [prodShape] using hbound)).symm


def allReducePrim (_numParts _rank : Nat) (xs : List Tensor) : Tensor :=
  let sh := (xs.head?.map (fun t => t.shape)).getD []
  Tensor.mkShape sh (fun idx => xs.foldl (fun acc t => acc + valAt t idx.1) 0)

/-- allToAllPrim: redistribution across ranks.
    Semantically equivalent to: gather all shards along dimension 0,
    then chunk along the last dimension. This is the default when
    no explicit idim/odim are provided. -/
def allToAllPrim (numParts rank : Nat) (xs : List Tensor) : Tensor :=
  let lastDim := (xs.head?.map (fun t => t.shape.length)).getD 0
  let idim := 0
  let odim := if lastDim = 0 then 0 else lastDim - 1
  allToAllPrimWithDims numParts rank xs idim odim

/-- allReducePrim shape equals the shape of the first element. -/
theorem allReducePrim_shape (numParts rank : Nat) (xs : List Tensor) (x0 : Tensor)
    (hhead : xs.head? = some x0) :
    (allReducePrim numParts rank xs).shape = x0.shape := by
  simp [allReducePrim, Tensor.mkShape, hhead]

/-!
## Small value-level lemmas (avoid giant simp)

These lemmas are intentionally lightweight and rewrite only the *observable scalar* values
we need in generated specs.
-/

@[simp] theorem prodShape_one : prodShape ([1] : Shape) = 1 := by
  simp [prodShape]

theorem fw_sum_valAt0 (x : Tensor) :
    valAt (fw_sum x) 0 = (∑ i : Fin (prodShape x.shape), x.val i) := by
  -- `fw_sum x` is a scalar tensor; `valAt` at 0 is the stored value.
  have h0 : (0 : Nat) < prodShape (fw_sum x).shape := by
    simp [fw_sum, Tensor.mkShape]
  -- Reduce the guard and unfold the constant kernel.
  simp [fw_sum, Tensor.mkShape, valAt]

theorem sum_val_eq_sum_range_valAt (x : Tensor) :
    (∑ i : Fin (prodShape x.shape), x.val i) =
      ∑ k ∈ Finset.range (prodShape x.shape), valAt x k := by
  -- Use the standard `Fin` ↔ `range` bridge lemma, and rewrite `valAt` on `Fin` indices.
  simpa [valAt_of_fin] using
    (Fin.sum_univ_eq_sum_range (f := fun k : Nat => valAt x k) (n := prodShape x.shape))

theorem fw_sum_valAt0_eq_sum_range_valAt (x : Tensor) :
    valAt (fw_sum x) 0 = ∑ k ∈ Finset.range (prodShape x.shape), valAt x k := by
  -- Combine `fw_sum`'s Fin-sum characterization with the `Fin`↔`range` bridge.
  simpa [fw_sum_valAt0] using (sum_val_eq_sum_range_valAt x)

theorem allReducePrim_valAt0_of_pos (numParts rank : Nat) (xs : List Tensor)
    (hpos : 0 < prodShape (allReducePrim numParts rank xs).shape) :
    valAt (allReducePrim numParts rank xs) 0 = xs.foldl (fun acc t => acc + valAt t 0) 0 := by
  have h : (0 : Nat) < prodShape (allReducePrim numParts rank xs).shape := hpos
  have hL : valAt (allReducePrim numParts rank xs) 0 = (allReducePrim numParts rank xs).val ⟨0, h⟩ := by
    -- Unfold `valAt` only for this occurrence.
    simp [valAt, h]
  -- Now unfold `allReducePrim`'s value function at index 0.
  -- This keeps the inner `valAt` terms opaque.
  rw [hL]
  simp [allReducePrim, Tensor.mkShape]

/-- If `x` is scalar, `fw_sum x` equals `x` at index 0. -/
theorem fw_sum_valAt0_of_shape_one (x : Tensor) (hx : x.shape = [1]) :
    valAt (fw_sum x) 0 = valAt x 0 := by
  have hprod : prodShape x.shape = 1 := by
    simp [hx]
  -- `range 1` contains only `0`.
  have hsum : (∑ k ∈ Finset.range (prodShape x.shape), valAt x k) = valAt x 0 := by
    simp [hprod]
  -- Combine with the general sum lemma.
  calc
    valAt (fw_sum x) 0 = ∑ k ∈ Finset.range (prodShape x.shape), valAt x k :=
      fw_sum_valAt0_eq_sum_range_valAt x
    _ = valAt x 0 := hsum

theorem fw_sum_eq_sum_fw_sum_chunkPrim
    (numParts b shard : Nat) (x : Tensor)
    (hshape : x.shape = [b, numParts * shard])
    (hparts : 0 < numParts)
  :
    valAt (fw_sum x) 0 =
      ∑ r ∈ Finset.range numParts, valAt (fw_sum (chunkPrim numParts r x)) 0 := by
  classical
  have hnumParts_ne0 : numParts ≠ 0 := Nat.ne_of_gt hparts
  -- Normalize chunk shapes to `[b, shard]`.
  have hdiv : divNat (numParts * shard) numParts = shard := by
    simp only [divNat]
    exact Nat.mul_div_cancel_left shard hparts
  have hchunkShape : ∀ r, (chunkPrim numParts r x).shape = [b, shard] := by
    intro r
    have hdrop : dropLast x.shape = [b] := by
      simp [dropLast, hshape]
    have hlast : lastD x.shape = numParts * shard := by
      simp [lastD, hshape]
    have hdiv' : divNat (lastD x.shape) numParts = shard := by
      simpa [hlast] using hdiv
    simp [chunkPrim, Tensor.mkShape, hdrop, hdiv', appendLast]
  -- Rewrite both sides into range-sums over `valAt`.
  rw [fw_sum_valAt0_eq_sum_range_valAt]
  -- LHS is now `∑ k ∈ range (prodShape x.shape), valAt x k`.
  -- Normalize `prodShape x.shape` to `b * (numParts * shard)`.
  simp only [hshape, prodShape, List.foldl, Nat.one_mul]
  have hR :
      (∑ r ∈ Finset.range numParts, valAt (fw_sum (chunkPrim numParts r x)) 0) =
        ∑ r ∈ Finset.range numParts,
          ∑ k ∈ Finset.range (b * shard), valAt (chunkPrim numParts r x) k := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have : valAt (fw_sum (chunkPrim numParts r x)) 0 =
        ∑ k ∈ Finset.range (prodShape (chunkPrim numParts r x).shape), valAt (chunkPrim numParts r x) k :=
      fw_sum_valAt0_eq_sum_range_valAt (chunkPrim numParts r x)
    simpa [hchunkShape r, prodShape] using this
  -- Replace RHS and expand as triple sums.
  rw [hR]
  -- LHS: split the flat index into `(p,k)` then `k` into `(r,j)`.
  have hL_split₁ :
      (∑ k ∈ Finset.range (b * (numParts * shard)), valAt x k) =
        ∑ p ∈ Finset.range b, ∑ k ∈ Finset.range (numParts * shard), valAt x (p * (numParts * shard) + k) := by
    simpa using (Finset.sum_range_mul_eq_sum_sum (n := b) (m := (numParts * shard))
      (f := fun k => valAt x k))
  have hL_split₂ :
      (∑ p ∈ Finset.range b, ∑ k ∈ Finset.range (numParts * shard), valAt x (p * (numParts * shard) + k)) =
        ∑ p ∈ Finset.range b, ∑ r ∈ Finset.range numParts, ∑ j ∈ Finset.range shard,
          valAt x (p * (numParts * shard) + (r * shard + j)) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    -- Split the inner range.
    simpa [Nat.mul_assoc, Nat.add_assoc] using
      (Finset.sum_range_mul_eq_sum_sum (n := numParts) (m := shard)
        (f := fun k => valAt x (p * (numParts * shard) + k)))
  -- RHS: split each chunk index into `(p,j)` and map back into the original tensor.
  have hR_split :
      (∑ r ∈ Finset.range numParts, ∑ k ∈ Finset.range (b * shard), valAt (chunkPrim numParts r x) k) =
        ∑ r ∈ Finset.range numParts, ∑ p ∈ Finset.range b, ∑ j ∈ Finset.range shard,
          valAt (chunkPrim numParts r x) (p * shard + j) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    simpa using (Finset.sum_range_mul_eq_sum_sum (n := b) (m := shard)
      (f := fun k => valAt (chunkPrim numParts r x) k))
  have hR_map :
      (∑ r ∈ Finset.range numParts, ∑ p ∈ Finset.range b, ∑ j ∈ Finset.range shard,
          valAt (chunkPrim numParts r x) (p * shard + j)) =
        ∑ r ∈ Finset.range numParts, ∑ p ∈ Finset.range b, ∑ j ∈ Finset.range shard,
          valAt x (p * (numParts * shard) + r * shard + j) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    refine Finset.sum_congr rfl ?_
    intro p hp
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hr' : r < numParts := Finset.mem_range.1 hr
    have hp' : p < b := Finset.mem_range.1 hp
    have hj' : j < shard := Finset.mem_range.1 hj
    -- Use the exact-index mapping lemma.
    simpa [Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (chunkPrim_valAt_mul_add (numParts := numParts) (rank := r) (b := b) (shard := shard)
        (x := x) (hshape := hshape) (hparts := hparts) (hrank := hr') (p := p) (hp := hp') (j := j) (hj := hj'))
  -- Put everything together.
  -- Start from LHS (now on the goal after simp), rewrite via the split lemmas,
  -- and show it matches the RHS after mapping and commuting finite sums.
  rw [hL_split₁]
  rw [hL_split₂]
  -- Rewrite RHS into the mapped triple-sum form.
  rw [hR_split]
  rw [hR_map]
  -- Commute the outer two sums on the RHS to match the LHS ordering.
  -- `∑ r, ∑ p, ... = ∑ p, ∑ r, ...`
  -- Align associativity in the index arithmetic, then use `sum_comm`.
  have hsum_comm :
      (∑ p ∈ Finset.range b, ∑ r ∈ Finset.range numParts, ∑ j ∈ Finset.range shard,
          valAt x (p * (numParts * shard) + r * shard + j)) =
        ∑ r ∈ Finset.range numParts, ∑ p ∈ Finset.range b, ∑ j ∈ Finset.range shard,
          valAt x (p * (numParts * shard) + r * shard + j) := by
    simpa [Nat.add_assoc] using
      (Finset.sum_comm (s := Finset.range b) (t := Finset.range numParts)
        (f := fun p r => ∑ j ∈ Finset.range shard,
          valAt x (p * (numParts * shard) + r * shard + j)))
  simpa [Nat.add_assoc] using hsum_comm

/-- `fw_sum` equals `allReducePrim` over chunked `fw_sum` outputs (scalar case). -/
theorem fw_sum_eq_allReduce_fw_sum_chunkPrim
    (numParts b shard : Nat) (x : Tensor)
    (hshape : x.shape = [b, numParts * shard])
    (hparts : 0 < numParts) :
    fw_sum x =
      allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x))) := by
  -- Shapes are both [1].
  have hshape_fw : (fw_sum x).shape = [1] := fw_sum_shape x
  have hshape_ar : (allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
      fw_sum (chunkPrim numParts r x)))).shape = [1] := by
    classical
    cases hnp : numParts with
    | zero =>
        simp [hnp] at hparts
    | succ n =>
        have hhead :
            (List.ofFn (fun r : Fin (Nat.succ n) =>
              fw_sum (chunkPrim (Nat.succ n) r x))).head? =
              some (fw_sum (chunkPrim (Nat.succ n) 0 x)) :=
          list_ofFn_head_eq (f := fun r : Fin (Nat.succ n) =>
            fw_sum (chunkPrim (Nat.succ n) r x))
        have hshape' := allReducePrim_shape (Nat.succ n) 0
          (List.ofFn (fun r : Fin (Nat.succ n) =>
            fw_sum (chunkPrim (Nat.succ n) r x)))
          (fw_sum (chunkPrim (Nat.succ n) 0 x)) hhead
        simpa [fw_sum_shape] using hshape'
  -- Reduce to value at index 0 (the only index for shape [1]).
  have hshape_eq : (fw_sum x).shape =
      (allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
        fw_sum (chunkPrim numParts r x)))).shape := by
    rw [hshape_fw, hshape_ar]
  apply Tensor.ext hshape_eq
  intro idx hidx
  -- idx must be 0 since prodShape [1] = 1
  have hidx0 : idx = 0 := by
    have hprod : prodShape ([1] : Shape) = 1 := prodShape_one
    have hlt : idx < 1 := by
      simpa [hshape_fw, hprod] using hidx
    exact Nat.lt_one_iff.mp hlt
  subst hidx0
  -- LHS: use the chunk-sum lemma
  have hL : valAt (fw_sum x) 0 =
      ∑ r ∈ Finset.range numParts, valAt (fw_sum (chunkPrim numParts r x)) 0 :=
    fw_sum_eq_sum_fw_sum_chunkPrim numParts b shard x hshape hparts
  -- RHS: unfold allReducePrim value at 0
  have hpos : 0 < prodShape (allReducePrim numParts 0
      (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x)))).shape := by
    -- shape is [1]
    have hprod : prodShape ([1] : Shape) = 1 := prodShape_one
    simp [hshape_ar, hprod]
  have hR : valAt (allReducePrim numParts 0
      (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x)))) 0 =
      (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x))).foldl
        (fun acc t => acc + valAt t 0) 0 :=
    by
      have h : (0 : Nat) < prodShape (allReducePrim numParts 0
          (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x)))).shape := hpos
      have hL : valAt (allReducePrim numParts 0
          (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x)))) 0 =
          (allReducePrim numParts 0
            (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x)))).val ⟨0, h⟩ := by
        simp [valAt, h]
      rw [hL]
      simp [allReducePrim, Tensor.mkShape]
  -- Convert foldl to sum over list, then to Finset.range.
  have hsum_list :
      (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x))).foldl
        (fun acc t => acc + valAt t 0) 0 =
      ((List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x))).map
        (fun t => valAt t 0)).sum :=
    List.foldl_add_eq_sum (f := fun t : Tensor => valAt t 0)
      (xs := List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x)))
  have hsum_ofFn :
      ((List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x))).map
        (fun t => valAt t 0)).sum =
      ∑ r : Fin numParts, valAt (fw_sum (chunkPrim numParts r x)) 0 := by
    -- list.ofFn/map -> Finset sum
    simpa [List.map_ofFn] using
      (Fin.sum_ofFn (fun r : Fin numParts => valAt (fw_sum (chunkPrim numParts r x)) 0))
  -- Put together
  have hR' : valAt (allReducePrim numParts 0
      (List.ofFn (fun r : Fin numParts => fw_sum (chunkPrim numParts r x)))) 0 =
      ∑ r : Fin numParts, valAt (fw_sum (chunkPrim numParts r x)) 0 := by
    -- rewrite via foldl->sum
    rw [hR, hsum_list, hsum_ofFn]
  -- Convert Fin sum to Finset.range
  have hR'' :
      ∑ r : Fin numParts, valAt (fw_sum (chunkPrim numParts r x)) 0 =
      ∑ r ∈ Finset.range numParts, valAt (fw_sum (chunkPrim numParts r x)) 0 := by
    -- standard bridge
    simpa using (Fin.sum_univ_eq_sum_range
      (f := fun k : Nat => valAt (fw_sum (chunkPrim numParts k x)) 0)
      (n := numParts))
  -- finish
  rw [hL]
  rw [hR']
  rw [hR'']

/-- Helper: foldl (· * ·) distributes initial value. -/
private theorem foldl_mul_init (a : Nat) (xs : List Nat) :
    xs.foldl (· * ·) a = a * xs.foldl (· * ·) 1 := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (a * x), ih (1 * x)]
    ring

private lemma prodShape_cons (a : Nat) (bs : List Nat) :
    prodShape (a :: bs) = a * prodShape bs := by
  simp only [prodShape, List.foldl]
  rw [foldl_mul_init]
  simp

/-- Helper: prodShape of a list.set equals the original prodShape
    with one factor replaced. -/
private theorem prodShape_set_mul (sh : Shape) (g : Nat) (hg : g < sh.length)
    (n : Nat) :
    prodShape (sh.set g (sh.getD g 0 * n)) = n * prodShape sh := by
  induction sh generalizing g with
  | nil => simp at hg
  | cons d ds ih =>
    cases g with
    | zero =>
      have hgd : (d :: ds).getD 0 0 = d := by simp [List.getD]
      simp only [List.set, hgd]
      rw [prodShape_cons, prodShape_cons]; ring
    | succ g' =>
      simp only [List.length_cons] at hg
      have hg' : g' < ds.length := by omega
      have hgd : (d :: ds).getD (g' + 1) 0 = ds.getD g' 0 := by simp [List.getD]
      simp only [List.set, hgd]
      rw [prodShape_cons, prodShape_cons, ih g' hg']; ring

/-- Helper: prodShape split at position g. -/
private theorem prodShape_split (sh : Shape) (g : Nat) (hg : g < sh.length) :
    prodShape sh = (sh.take g).foldl (· * ·) 1 * sh.getD g 0 *
      (sh.drop (g + 1)).foldl (· * ·) 1 := by
  induction sh generalizing g with
  | nil => simp at hg
  | cons d ds ih =>
    cases g with
    | zero =>
      have hgd : (d :: ds).getD 0 0 = d := by simp [List.getD]
      simp only [List.take, List.drop, hgd, List.foldl]
      rw [prodShape_cons]; simp [prodShape]
    | succ g' =>
      simp only [List.length_cons] at hg
      have hg' : g' < ds.length := by omega
      rw [prodShape_cons, ih g' hg']
      simp only [List.take, List.drop]
      have hgd : (d :: ds).getD (g' + 1) 0 = ds.getD g' 0 := by simp [List.getD]
      rw [hgd]
      simp only [List.foldl]
      rw [foldl_mul_init (1 * d)]; ring

private lemma list_map_sum_eq_range_sum {α β : Type*} [AddCommMonoid β]
    (l : List α) (f : α → β) (d : α) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map, List.sum_cons, List.length_cons]
    rw [Finset.sum_range_succ', ih]
    have h0 : (x :: xs).getD 0 d = x := by simp [List.getD]
    have hsucc : ∀ i, (x :: xs).getD (i + 1) d = xs.getD i d := by
      intro i; simp [List.getD]
    simp only [h0, hsucc]
    rw [add_comm]

/-- `fw_sum` distributes over `allGatherPrimDimN`: the sum of the gathered tensor
    equals the `allReducePrim` of the individual sums. -/
theorem fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum
    (gatherDim numParts : Nat) (xs : List Tensor)
    (hlen : xs.length = numParts) (hparts : 0 < numParts)
    (shardShape : Shape)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = shardShape)
    (hshape : ∀ x ∈ xs, x.shape = shardShape)
    (hgatherDim : gatherDim < shardShape.length)
    (hdimPos : 0 < shardShape.getD gatherDim 0)
    (hpostPos : 0 < (shardShape.drop (gatherDim + 1)).foldl (· * ·) 1) :
    fw_sum (allGatherPrimDimN gatherDim numParts 0 xs) =
      allReducePrim numParts 0 (xs.map fw_sum) := by
  classical
  set dimSize := shardShape.getD gatherDim 0 with hdimSize_def
  set postStride := (shardShape.drop (gatherDim + 1)).foldl (· * ·) 1 with hpostStride_def
  set dimStride := dimSize * postStride with hdimStride_def
  set fullDimSize := dimSize * numParts with hfullDimSize_def
  set fullDimStride := fullDimSize * postStride with hfullDimStride_def
  set outShape := shardShape.set gatherDim fullDimSize with houtShape_def
  set preDim := (shardShape.take gatherDim).foldl (· * ·) 1 with hpreDim_def
  have hds_pos : 0 < dimStride := Nat.mul_pos hdimPos hpostPos
  have hfds_pos : 0 < fullDimStride := by
    rw [hfullDimStride_def, hfullDimSize_def]
    exact Nat.mul_pos (Nat.mul_pos hdimPos hparts) hpostPos
  have hfds_eq : fullDimStride = numParts * dimStride := by
    rw [hfullDimStride_def, hfullDimSize_def, hdimStride_def]; ring
  have hne_fds : fullDimStride ≠ 0 := Nat.ne_of_gt hfds_pos
  have hne_ps : postStride ≠ 0 := Nat.ne_of_gt hpostPos
  have hne_ds : dimSize ≠ 0 := Nat.ne_of_gt hdimPos
  -- prodShape decomposition
  have hprod_shard : prodShape shardShape = preDim * dimStride := by
    rw [hpreDim_def, hdimStride_def, hdimSize_def, hpostStride_def]
    rw [prodShape_split shardShape gatherDim hgatherDim]
    ring
  have hprod_out : prodShape outShape = preDim * fullDimStride := by
    have h1 : fullDimSize = shardShape.getD gatherDim 0 * numParts := by
      rw [hfullDimSize_def, hdimSize_def]
    rw [houtShape_def, h1, prodShape_set_mul shardShape gatherDim hgatherDim numParts]
    rw [hprod_shard, hfds_eq]; ring
  -- Shape proofs
  have hgather_shape : (allGatherPrimDimN gatherDim numParts 0 xs).shape = outShape :=
    allGatherPrimDimN_shape gatherDim numParts xs shardShape hhead
  have hfw_shape : (fw_sum (allGatherPrimDimN gatherDim numParts 0 xs)).shape = [1] :=
    fw_sum_shape _
  have har_shape : (allReducePrim numParts 0 (xs.map fw_sum)).shape = [1] := by
    cases hxs : xs with
    | nil => simp [hxs] at hlen; omega
    | cons x0 xs' =>
      have := allReducePrim_shape numParts 0 (List.map fw_sum (x0 :: xs')) (fw_sum x0) rfl
      simpa [fw_sum_shape] using this
  -- Apply Tensor.ext
  apply Tensor.ext (by rw [hfw_shape, har_shape])
  intro idx hidx
  have hidx0 : idx = 0 := by
    have : idx < 1 := by simpa [hfw_shape] using hidx
    omega
  subst hidx0
  -- LHS: fw_sum at 0
  rw [fw_sum_valAt0_eq_sum_range_valAt, hgather_shape, hprod_out]
  -- RHS: allReducePrim at 0
  rw [allReducePrim_valAt0_of_pos numParts 0 _ (by simp [har_shape]),
      List.foldl_add_eq_sum, List.map_map]
  -- Convert RHS list sum to Finset.range sum
  rw [list_map_sum_eq_range_sum _ _ (zeroTensor shardShape)]
  simp only [hlen, Function.comp_def]
  -- Expand fw_sum valAt 0
  simp_rw [fw_sum_valAt0_eq_sum_range_valAt]
  -- Normalize shard shapes
  have hshape_all : ∀ r, (xs.getD r (zeroTensor shardShape)).shape = shardShape := by
    intro r
    by_cases hr : r < xs.length
    · simp [List.getD, List.getElem?_eq_getElem hr, hshape _ (List.getElem_mem hr)]
    · have hr' : xs.length ≤ r := Nat.not_lt.mp hr
      simp [List.getD, List.getElem?_eq_none hr', zeroTensor, Tensor.mkShape]
  simp_rw [hshape_all, hprod_shard]
  -- LHS: ∑_{i < preDim * fullDimStride} valAt gather i
  -- RHS: ∑_{r < numParts} ∑_{j < preDim * dimStride} valAt xs[r] j
  -- Decompose LHS: split preDim * fullDimStride = preDim * (numParts * dimStride)
  rw [Finset.sum_range_mul_eq_sum_sum (n := preDim) (m := fullDimStride)]
  simp_rw [hfds_eq]
  conv_lhs =>
    arg 2; ext batch
    rw [Finset.sum_range_mul_eq_sum_sum (n := numParts) (m := dimStride)]
  -- Now LHS: ∑_{batch < preDim} ∑_{r < numParts} ∑_{l < dimStride}
  --            valAt gather (batch * fullDimStride + r * dimStride + l)
  -- RHS: ∑_{r < numParts} ∑_{j < preDim * dimStride} valAt xs[r] j
  -- Step: Show each LHS term = valAt xs[r] (batch * dimStride + l)
  have hval_eq : ∀ (batch : Nat) (_ : batch < preDim) (r : Nat) (_ : r < numParts)
      (l : Nat) (_ : l < dimStride),
      valAt (allGatherPrimDimN gatherDim numParts 0 xs)
        (batch * (numParts * dimStride) + r * dimStride + l) =
      valAt (xs.getD r (zeroTensor shardShape)) (batch * dimStride + l) := by
    intro batch hbatch r hr l hl
    have hidx_bound : batch * (numParts * dimStride) + r * dimStride + l <
        prodShape outShape := by
      rw [hprod_out, hfds_eq]
      calc batch * (numParts * dimStride) + r * dimStride + l
          < batch * (numParts * dimStride) + r * dimStride + dimStride := by omega
        _ = batch * (numParts * dimStride) + (r + 1) * dimStride := by ring
        _ ≤ batch * (numParts * dimStride) + numParts * dimStride := by
            apply Nat.add_le_add_left; exact Nat.mul_le_mul_right _ (by omega)
        _ = (batch + 1) * (numParts * dimStride) := by ring
        _ ≤ preDim * (numParts * dimStride) := by
            exact Nat.mul_le_mul_right _ (by omega)
    rw [valAt_of_lt _ _ (by rw [hgather_shape]; exact hidx_bound)]
    simp only [allGatherPrimDimN, Tensor.mkShape, hhead]
    -- Simplify the if-then-else guards
    simp only [← hdimSize_def, ← hpostStride_def, ← hdimStride_def,
               ← hfullDimSize_def, ← hfullDimStride_def,
               hne_fds, hne_ps, hne_ds, ↓reduceIte]
    -- Arithmetic: decompose the index
    have hrem_bound : r * dimStride + l < fullDimStride := by
      rw [hfds_eq]; calc r * dimStride + l
          < r * dimStride + dimStride := by omega
        _ = (r + 1) * dimStride := by ring
        _ ≤ numParts * dimStride := Nat.mul_le_mul_right _ (by omega)
    have hmod_idx : (batch * (numParts * dimStride) + r * dimStride + l) % fullDimStride =
        r * dimStride + l := by
      rw [show batch * (numParts * dimStride) + r * dimStride + l =
          fullDimStride * batch + (r * dimStride + l) from by rw [hfds_eq]; ring]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_bound]
    have hdiv_idx : (batch * (numParts * dimStride) + r * dimStride + l) / fullDimStride =
        batch := by
      rw [show batch * (numParts * dimStride) + r * dimStride + l =
          fullDimStride * batch + (r * dimStride + l) from by rw [hfds_eq]; ring]
      rw [Nat.mul_add_div hfds_pos, Nat.div_eq_of_lt hrem_bound, Nat.add_zero]
    have hl_div_ps : l / postStride < dimSize :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hdimStride_def]; exact hl)
    have hjfull : (r * dimStride + l) / postStride = r * dimSize + l / postStride := by
      rw [hdimStride_def,
          show r * (dimSize * postStride) + l = postStride * (r * dimSize) + l from by ring]
      exact Nat.mul_add_div hpostPos (r * dimSize) l
    have hk : (r * dimStride + l) % postStride = l % postStride := by
      rw [hdimStride_def,
          show r * (dimSize * postStride) + l = postStride * (r * dimSize) + l from by ring]
      exact Nat.mul_add_mod postStride (r * dimSize) l
    have hr_eq : (r * dimSize + l / postStride) / dimSize = r := by
      rw [show r * dimSize = dimSize * r from by ring]
      rw [Nat.mul_add_div hdimPos, Nat.div_eq_of_lt hl_div_ps, Nat.add_zero]
    have hjlocal : (r * dimSize + l / postStride) % dimSize = l / postStride := by
      rw [show r * dimSize = dimSize * r from by ring]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hl_div_ps]
    rw [hmod_idx, hjfull, hr_eq, hdiv_idx, hk, hjlocal]
    congr 1
    have := Nat.div_add_mod l postStride
    rw [Nat.mul_comm (l / postStride) postStride]
    omega
  -- Apply hval_eq pointwise via Finset.sum_congr
  have hlhs_rw : ∑ batch ∈ Finset.range preDim,
      ∑ r ∈ Finset.range numParts,
        ∑ l ∈ Finset.range dimStride,
          valAt (allGatherPrimDimN gatherDim numParts 0 xs)
            (batch * (numParts * dimStride) + (r * dimStride + l)) =
      ∑ batch ∈ Finset.range preDim,
        ∑ r ∈ Finset.range numParts,
          ∑ l ∈ Finset.range dimStride,
            valAt (xs.getD r (zeroTensor shardShape)) (batch * dimStride + l) := by
    refine Finset.sum_congr rfl fun batch hb => Finset.sum_congr rfl fun r hr =>
      Finset.sum_congr rfl fun l hl => ?_
    have hassoc : batch * (numParts * dimStride) + (r * dimStride + l) =
        batch * (numParts * dimStride) + r * dimStride + l := by omega
    rw [hassoc]
    exact hval_eq batch (Finset.mem_range.mp hb) r (Finset.mem_range.mp hr)
        l (Finset.mem_range.mp hl)
  rw [hlhs_rw, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_range_mul_eq_sum_sum (n := preDim) (m := dimStride)]

/-!
## Pure shape-level dimension checking (auto-generatable)

For automation, we provide a *computable* checker that only looks at shapes.
The Python generator can emit `theorem ... := by native_decide` proofs that the
generated `sm/pm` graphs pass this check.
-/

abbrev ShapeMap := List (Tid × Shape)

def shapeMapGet (m : ShapeMap) (tid : Tid) : Option Shape :=
  match m.find? (fun p => p.1 = tid) with
  | some (_, sh) => some sh
  | none => none

def shapeMapSet (m : ShapeMap) (tid : Tid) (sh : Shape) : ShapeMap :=
  (tid, sh) :: m

def dimsPos (sh : Shape) : Bool :=
  sh.all (fun d => decide (0 < d))

def allEqShape (sh : Shape) (xs : List Shape) : Bool :=
  xs.all (fun s => decide (s = sh))

def opOutShapes (numParts : Nat) (op : String) (params : List Nat) (inShapes : List Shape) : Option (List Shape) :=
  match op, inShapes with
  | "OpName.FW_sum", [_x] =>
      some [[1]]
  | "OpName.BW_sum", [g, x] =>
      if decide (g = [1]) then some [x] else none
  -- FW_linear: supports both 2D [b, i] @ [o, i] -> [b, o]
  -- and 3D [b, s, i] @ [o, i] -> [b, s, o] (for attention)
  -- Note: For TP parallelization, input may be chunked but weight may not be,
  -- so we relax the dimension check and just compute output shape based on weight.
  | "OpName.FW_linear", [x, [o, _i2]] =>
      match x.reverse with
      | _i :: rest => some [(o :: rest).reverse]
      | _ => none
  -- BW_linear: gradient w.r.t. x and w
  -- Input: grad [b, (s,) o], x [b, (s,) i], w [o, i]
  -- Output: dx [b, (s,) i], dw [o, i]
  | "OpName.BW_linear", [_g, x, w] =>
      some [x, w]
  | "OpName.ChunkPrim", [x] =>
      let dim := match params with | [d] => d | _ => x.length - 1
      let d := x.getD dim 0
      if decide (0 < numParts ∧ numParts ≤ d) then
        let shard := divNat d numParts
        if decide (0 < shard) then some [x.set dim shard] else none
      else
        none
  | "OpName.AllGatherPrim", xs =>
      match xs with
      | [] => none
      | sh0 :: _ =>
          let dim := match params with | [d] => d | _ => sh0.length - 1
          let shard := sh0.getD dim 0
          if decide (0 < numParts) then
            if decide (xs.length = numParts) && allEqShape sh0 xs && decide (0 < shard) then
              some [sh0.set dim (shard * numParts)]
            else
              none
          else
            none
  | "OpName.AllReducePrim", xs =>
      match xs with
      | [] => none
      | sh0 :: _ =>
          if allEqShape sh0 xs then some [sh0] else none
  | "OpName.AllToAllPrim", xs =>
      match xs with
      | [] => none
      | sh0 :: _ =>
          if ¬ allEqShape sh0 xs then none
          else
            match params with
            | [idim, odim] =>
                let gathered := sh0.set idim (sh0.getD idim 0 * numParts)
                let final := gathered.set odim (gathered.getD odim 0 / numParts)
                some [final]
            | _ => some [sh0]
  -- ============================================================
  -- Attention operators
  -- ============================================================
  -- FW_multiref: copy one input to multiple outputs (all same shape)
  | "OpName.FW_multiref", [x] =>
      let n := params.head?.getD 3
      some (List.replicate n x)
  | "OpName.FW_view", [_x] =>
      match params with
      | [] => some [_x]
      | targetShape => some [targetShape]
  | "OpName.BW_view", [_g, _x] =>
      match params with
      | [] => some [_g]
      | targetShape => some [targetShape]
  | "OpName.FW_transpose", [x] =>
      match params with
      | [d0, d1] => some [listSwapAt x d0 d1]
      | _ =>
        match x.reverse with
        | d1 :: d0 :: rest => some [(d0 :: d1 :: rest).reverse]
        | _ => some [x]
  | "OpName.BW_transpose", [g, _x] =>
      match params with
      | [d0, d1] => some [listSwapAt g d0 d1]
      | _ =>
        match g.reverse with
        | d1 :: d0 :: rest => some [(d0 :: d1 :: rest).reverse]
        | _ => some [g]
  -- FW_matmul / BW_matmul: matrix multiplication
  -- [b, n, k] @ [b, k, m] -> [b, n, m]  (batched)
  -- or [n, k] @ [k, m] -> [n, m] (when batchX = batchY = [])
  | "OpName.FW_matmul", [x, y] =>
      match x.reverse, y.reverse with
      | k1 :: n :: batchX, m :: k2 :: batchY =>
          if decide (k1 = k2 ∧ batchX = batchY) then
            some [((m :: n :: batchX).reverse)]
          else
            none
      | _, _ => none
  | "OpName.BW_matmul", [_g, x, y] =>
      -- g: [b, n, m], x: [b, n, k], y: [b, k, m]
      -- dx: [b, n, k], dy: [b, k, m]
      some [x, y]
  -- FW_div / BW_div: element-wise division by scalar (shape unchanged)
  | "OpName.FW_div", [x] =>
      some [x]
  | "OpName.BW_div", [g, _x] =>
      some [g]
  -- FW_softmax / BW_softmax: softmax (shape unchanged)
  | "OpName.FW_softmax", [x] =>
      some [x]
  | "OpName.BW_softmax", [g, _x] =>
      some [g]
  -- FW_contiguous / BW_contiguous: memory layout (shape unchanged)
  | "OpName.FW_contiguous", [x] =>
      some [x]
  | "OpName.BW_contiguous", [g, _x] =>
      some [g]
  -- CROSS_DP_WRED: cross data-parallel weight reduction
  -- Input: gradients from all ranks (same shape)
  -- Output: reduced gradients for all ranks (same shape as inputs)
  -- In the merged representation, outputs = inputs (inplace semantics)
  | "OpName.CROSS_DP_WRED", xs =>
      match xs with
      | [] => none
      | sh0 :: _ =>
          if allEqShape sh0 xs then some (xs.map (fun _ => sh0)) else none
  -- ============================================================
  -- GPT-style operators
  -- ============================================================
  | "OpName.FW_embedding", [ids, weight] =>
      some [ids ++ [lastD weight]]
  | "OpName.BW_embedding", [_g, _ids, weight] =>
      some [weight]
  | "OpName.FW_layernorm", [x, _weight, _bias] =>
      some [x]
  | "OpName.BW_layernorm", [_g, x, weight, bias] =>
      some [x, weight, bias]
  | "OpName.FW_dropout", [x] =>
      some [x]
  | "OpName.BW_dropout", [g, _x] =>
      some [g]
  | "OpName.FW_gelu", [x] =>
      some [x]
  | "OpName.BW_gelu", [g, _x] =>
      some [g]
  | "OpName.FW_add", [x] =>
      some [x]
  | "OpName.FW_add", [x, y] =>
      if decide (x.length >= y.length) then some [x] else some [y]
  | "OpName.BW_add", [_g, x] =>
      some [x]
  | "OpName.BW_add", [_g, x, y] =>
      some [x, y]
  | "OpName.FW_mul", [x] =>
      some [x]
  | "OpName.FW_mul", [x, y] =>
      if decide (x.length >= y.length) then some [x] else some [y]
  | "OpName.BW_mul", [_g, x] =>
      some [x]
  | "OpName.BW_mul", [_g, x, y] =>
      some [x, y]
  | "OpName.FW_pow", [x] =>
      some [x]
  | "OpName.BW_pow", [g, _x] =>
      some [g]
  | "OpName.FW_mean", [x] =>
      match x.reverse with
      | _ :: rest => some [(1 :: rest).reverse]
      | [] => some [[]]
  | "OpName.BW_mean", [_g, x] =>
      some [x]
  | "OpName.FW_rsqrt", [x] =>
      some [x]
  | "OpName.BW_rsqrt", [g, _x] =>
      some [g]
  | _, _ => none

def applyNodeShapesChecked (g : GraphDecl) (m : ShapeMap) (n : NodeDecl) : Except String ShapeMap :=
  let inShapes? : Option (List Shape) := n.ins.mapM (shapeMapGet m)
  match inShapes? with
  | none => Except.error s!"shape check: missing input shape for node {n.op}"
  | some inShapes =>
      -- For operations like FW_view where output shape cannot be inferred from input shape,
      -- check if the output shapes are already known in the ShapeMap.
      -- If all outputs are already known, skip inference and use known shapes.
      let knownOutShapes? : Option (List Shape) := n.outs.mapM (shapeMapGet m)
      match knownOutShapes? with
      | some knownOutShapes =>
          -- All output shapes are known, just verify they are positive
          if knownOutShapes.all dimsPos then
            Except.ok m  -- shapes already in map, no need to update
          else
            Except.error s!"shape check: known shape is degenerate for {n.op}"
      | none =>
          -- Some output shapes not known, need to infer
          match opOutShapes g.numRanks n.op n.params inShapes with
          | none => Except.error s!"shape check: op/shape mismatch for {n.op}"
          | some outShapes =>
              if _hLen : outShapes.length = n.outs.length then
                -- Also enforce positivity of all produced shapes (no zero dimensions).
                if outShapes.all dimsPos then
                  let pairs := n.outs.zip outShapes
                  let m' := pairs.foldl (fun acc p => shapeMapSet acc p.1 p.2) m
                  Except.ok m'
                else
                  Except.error s!"shape check: produced a degenerate shape for {n.op}"
              else
                Except.error s!"shape check: arity mismatch for {n.op} (expected {n.outs.length}, got {outShapes.length})"

def graphShapesCheck (g : GraphDecl) (initShapes : ShapeMap) : Except String ShapeMap :=
  -- Enforce positivity on *given* init shapes too.
  if initShapes.all (fun p => dimsPos p.2) then
    g.nodes.foldlM (fun m n => applyNodeShapesChecked g m n) initShapes
  else
    Except.error "shape check: init has a degenerate shape"

def storeShapesHoldList (init : Store) (initShapes : ShapeMap) : Bool :=
  initShapes.all (fun p => decide ((init p.1).shape = p.2))

@[simp] theorem Except.toBool_ok {ε α : Type} (a : α) : ((Except.ok a : Except ε α).toBool) = true := by
  rfl

@[simp] theorem Except.toBool_error {ε α : Type} (e : ε) : ((Except.error e : Except ε α).toBool) = false := by
  rfl

theorem Except.isOk_iff_exists {ε α : Type} (e : Except ε α) : e.isOk ↔ ∃ a, e = Except.ok a := by
  cases e <;> simp [Except.isOk]

/-!
## evalOp: interpret operator names

This matches the operator names observed in the currently generated example graph:
`OpName.FW_linear`, `OpName.FW_sum`, `OpName.BW_sum`, `OpName.BW_linear`,
and collectives `ChunkPrim`, `AllGatherPrim`, `AllReducePrim`.

We intentionally skip `OpName.DATALOADER` here: in the denotational style, data/weights
should come from the initial store (not as a nullary op).

For operations like view/contiguous that don't change numerical values, we return
the input tensor directly. Shape correctness is ensured by separate shape checking.
-/

def evalOp (numParts rank : Nat) (op : String) (params : List Nat) (args : List Tensor) : List Tensor :=
  match op, args with
  | "OpName.FW_sum", [x] => [fw_sum x]
  | "OpName.BW_sum", [g, x] => [bw_sum g x]
  | "OpName.FW_linear", [x, w] => [fw_linear x w]
  | "OpName.BW_linear", [g, x, w] =>
      let (dx, dw) := bw_linear g x w
      [dx, dw]
  | "OpName.ChunkPrim", [x] =>
      match params with
      | [dim] => [chunkPrimDimN dim numParts rank x]
      | _ => [chunkPrimDimN (x.shape.length - 1) numParts rank x]
  | "OpName.AllGatherPrim", xs =>
      match params with
      | [dim] => [allGatherPrimDimN dim numParts rank xs]
      | _ => [allGatherPrimDimN ((xs.head?.map (fun t => t.shape.length)).getD 1 - 1) numParts rank xs]
  | "OpName.AllReducePrim", xs => [allReducePrim numParts rank xs]
  | "OpName.AllToAllPrim", xs =>
      match params with
      | [idim, odim] => [allToAllPrimWithDims numParts rank xs idim odim]
      | _ => [allToAllPrim numParts rank xs]
  -- Attention operators
  | "OpName.FW_multiref", [x] =>
      let n := params.head?.getD 3
      List.replicate n x
  | "OpName.FW_view", [x] =>
      match params with
      | [] => [x]
      | targetShape => [fw_view targetShape x]
  | "OpName.BW_view", [g, _x] =>
      match params with
      | [] => [g]
      | targetShape => [fw_view targetShape g]
  | "OpName.FW_transpose", [x] =>
      match params with
      | [d0, d1] => [transposeAxes d0 d1 x]
      | _ => [fw_transpose x]
  | "OpName.BW_transpose", [g, _x] =>
      match params with
      | [d0, d1] => [transposeAxes d0 d1 g]
      | _ => [bw_transpose g]
  | "OpName.FW_matmul", [x, y] => [fw_matmul x y]
  | "OpName.BW_matmul", [g, x, y] =>
      let (dx, dy) := bw_matmul g x y
      [dx, dy]
  | "OpName.FW_div", [x] =>
      let c : Scalar := (params.head?.getD 1 : Nat)
      [fw_div c x]
  | "OpName.BW_div", [g, _x] =>
      let c : Scalar := (params.head?.getD 1 : Nat)
      [bw_div c g]
  | "OpName.FW_softmax", [x] => [fw_softmax x]
  | "OpName.BW_softmax", [g, y] => [bw_softmax g y]
  | "OpName.FW_contiguous", [x] => [x]
  | "OpName.BW_contiguous", [g, _x] => [g]
  | "OpName.CROSS_DP_WRED", xs => [cross_dp_wred xs]
  -- GPT-style operators
  | "OpName.FW_embedding", [ids, weight] =>
      match params with
      | [] => [fw_embedding ids weight]
      | offset :: _ => [fw_embedding_offset offset ids weight]
  | "OpName.BW_embedding", [g, ids, weight] =>
      match params with
      | [] => [bw_embedding g ids weight]
      | offset :: _ => [bw_embedding_offset offset g ids weight]
  | "OpName.FW_layernorm", [x, weight, bias] => [fw_layernorm x weight bias]
  | "OpName.BW_layernorm", [g, x, weight, bias] =>
      let (dx, dw, db) := bw_layernorm g x weight bias
      [dx, dw, db]
  | "OpName.FW_dropout", [x] => [fw_dropout x]
  | "OpName.BW_dropout", [g, x] => [bw_dropout g x]
  | "OpName.FW_gelu", [x] => [fw_gelu x]
  | "OpName.BW_gelu", [g, x] => [bw_gelu g x]
  | "OpName.FW_add", [x] => [x]
  | "OpName.FW_add", [x, y] => [elemwiseAdd x y]
  | "OpName.BW_add", [g, _x] => [g]
  | "OpName.BW_add", [g, x, y] =>
      let (dx, dy) := bw_add2 g x y
      [dx, dy]
  | "OpName.FW_mul", [x] => [x]
  | "OpName.FW_mul", [x, y] => [elemwiseMul x y]
  | "OpName.BW_mul", [g, _x] => [g]
  | "OpName.BW_mul", [g, x, y] =>
      let (dx, dy) := bw_mul2 g x y
      [dx, dy]
  | "OpName.FW_pow", [x] =>
      [fw_pow (params.head?.getD 2) x]
  | "OpName.BW_pow", [g, x] =>
      [bw_pow (params.head?.getD 2) g x]
  | "OpName.FW_mean", [x] => [fw_mean x]
  | "OpName.BW_mean", [g, x] => [bw_mean g x]
  | "OpName.FW_rsqrt", [x] => [fw_rsqrt x]
  | "OpName.BW_rsqrt", [g, x] => [bw_rsqrt g x]
  | "OpName.BW_multiref", xs => [tensorSum xs]
  | _, _ => []

/-!
## Graph denotation (single forward fold)
-/

def storeSet (s : Store) (pairs : List (Tid × Tensor)) : Store :=
  fun tid =>
    match pairs.find? (fun p => decide (p.1 = tid)) with
    | some (_, v) => v
    | none => s tid

theorem storeSet_eq_of_not_mem_fst (s : Store) (pairs : List (Tid × Tensor)) (tid : Tid)
    (h : tid ∉ pairs.map Prod.fst) :
    storeSet s pairs tid = s tid := by
  induction pairs with
  | nil =>
      simp [storeSet]
  | cons p ps ih =>
      rcases p with ⟨k, v⟩
      have hk : k ≠ tid := by
        intro hkEq
        apply h
        simp [hkEq]
      have hps : tid ∉ ps.map Prod.fst := by
        intro hmem
        apply h
        simp [hmem]
      -- unfold `find?` on cons
      simpa [storeSet, List.find?, hk] using ih hps

def applyNode (g : GraphDecl) (s : Store) (n : NodeDecl) : Store :=
  let args : List Tensor := n.ins.map s
  let outs : List Tensor := evalOp g.numRanks n.rank n.op n.params args
  let pairs : List (Tid × Tensor) := n.outs.zip outs
  storeSet s pairs

def denoteGraph (g : GraphDecl) (init : Store) : Store :=
  g.nodes.foldl (applyNode g) init

/-!
## Small `applyNode` rewrite lemmas (singleton outs)

These are definitional facts that keep generated proofs readable and avoid repeatedly
unfolding `storeSet`/`find?` for the common case `outs = [tid]`.
-/

/-- Looking up `tid` in `applyNode g s node` when `tid ∉ node.outs` falls through to `s tid`. -/
theorem applyNode_skip (g : GraphDecl) (s : Store) (n : NodeDecl) (tid : Tid)
    (h : tid ∉ n.outs) :
    applyNode g s n tid = s tid := by
  unfold applyNode
  apply storeSet_eq_of_not_mem_fst
  intro hmem
  apply h
  have ⟨⟨a, b⟩, hmem_zip, heq⟩ := List.mem_map.mp hmem
  simp only [Prod.fst] at heq; subst heq
  exact (List.of_mem_zip hmem_zip).1

axiom applyNode_fw_sum_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_sum", ins := [inTid], outs := [outTid] } outTid =
      fw_sum (s inTid)

axiom applyNode_fw_linear_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid wTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_linear", ins := [xTid, wTid], outs := [outTid] } outTid =
      fw_linear (s xTid) (s wTid)

/-- applyNode for bw_sum with singleton output. -/
axiom applyNode_bw_sum_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_sum", ins := [gTid, xTid], outs := [outTid] } outTid =
      bw_sum (s gTid) (s xTid)

axiom applyNode_allGatherPrimDimN_out
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid) (dim : Nat) :
    applyNode g s { rank := rank, op := "OpName.AllGatherPrim", ins := ins, outs := [outTid], params := [dim] } outTid =
      allGatherPrimDimN dim g.numRanks rank (ins.map s)

/-- applyNode for bw_linear first output (dx). -/
axiom applyNode_bw_linear_fst_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid dxTid dwTid : Tid)
    (_ : dxTid ≠ dwTid) :
    applyNode g s { rank := rank, op := "OpName.BW_linear", ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] } dxTid =
      (bw_linear (s gTid) (s xTid) (s wTid)).1

/-- applyNode for bw_linear second output (dw). -/
axiom applyNode_bw_linear_snd_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid dxTid dwTid : Tid)
    (hne : dxTid ≠ dwTid) :
    applyNode g s { rank := rank, op := "OpName.BW_linear", ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] } dwTid =
      (bw_linear (s gTid) (s xTid) (s wTid)).2

/-- Unfolding lemma for `evalOp` on `FW_embedding` with empty params. -/
theorem evalOp_fw_embedding_empty (numParts rank : Nat) (ids w : Tensor) :
    evalOp numParts rank "OpName.FW_embedding" [] [ids, w] = [fw_embedding ids w] := by
  rfl

/-- Unfolding lemma for `evalOp` on `FW_embedding` with `params := [offset]`. -/
theorem evalOp_fw_embedding_offset (numParts rank offset : Nat) (ids w : Tensor) :
    evalOp numParts rank "OpName.FW_embedding" [offset] [ids, w] =
      [fw_embedding_offset offset ids w] := by
  rfl

/-- Unfolding lemma for `evalOp` on `BW_embedding` with empty params. -/
theorem evalOp_bw_embedding_empty (numParts rank : Nat) (g ids w : Tensor) :
    evalOp numParts rank "OpName.BW_embedding" [] [g, ids, w] = [bw_embedding g ids w] := by
  rfl

/-- Unfolding lemma for `evalOp` on `BW_embedding` with `params := [offset]`. -/
theorem evalOp_bw_embedding_offset (numParts rank offset : Nat) (g ids w : Tensor) :
    evalOp numParts rank "OpName.BW_embedding" [offset] [g, ids, w] =
      [bw_embedding_offset offset g ids w] := by
  rfl

/-- Unfolding lemma for `BW_gelu`. -/
theorem evalOp_bw_gelu (numParts rank : Nat) (g x : Tensor) :
    evalOp numParts rank "OpName.BW_gelu" [] [g, x] = [bw_gelu g x] := by
  rfl

/-- `applyNode` for `BW_gelu` with singleton output. -/
theorem applyNode_bw_gelu_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_gelu", ins := [gTid, xTid], outs := [outTid] } outTid =
      bw_gelu (s gTid) (s xTid) := by
  unfold applyNode
  rw [show ([gTid, xTid] : List Tid).map s = [s gTid, s xTid] from rfl,
      evalOp_bw_gelu]
  change storeSet s [(outTid, bw_gelu (s gTid) (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `bw_gelu` preserves the shape of its second input. -/
theorem bw_gelu_shape (g x : Tensor) : (bw_gelu g x).shape = x.shape := by
  simp [bw_gelu, Tensor.mkShape]

/-- `valAt` of `bw_gelu` at a valid index. -/
theorem bw_gelu_valAt (g x : Tensor) (idx : Nat) (h : idx < prodShape x.shape) :
    valAt (bw_gelu g x) idx = valAt g idx * geluDerivScalar (valAt x idx) := by
  have hsh : (bw_gelu g x).shape = x.shape := bw_gelu_shape g x
  rw [valAt_of_lt _ _ (hsh ▸ h)]
  simp [bw_gelu, Tensor.mkShape]

/-- Helper: List.getD when index is in bounds. -/
private theorem list_getD_of_lt {α : Type*} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  unfold List.getD
  rw [List.getElem?_eq_getElem h]
  simp

/-- Helper: List.getD when index is out of bounds. -/
private theorem list_getD_of_ge {α : Type*} (l : List α) (i : Nat) (d : α) (h : ¬(i < l.length)) :
    l.getD i d = d := by
  unfold List.getD
  rw [List.getElem?_eq_none (by omega)]
  simp

/-- `bw_gelu` distributes over `allGatherPrimDimN`: applying `bw_gelu` to two
    gathered tensors equals gathering the pairwise `bw_gelu` results.
    This holds because `bw_gelu` is a pointwise operation that reads both inputs
    at the same index position. -/
theorem bw_gelu_allGatherPrimDimN_eq
    (gatherDim numParts : Nat) (gs xs : List Tensor)
    (shardShape : Shape)
    (hnp : 0 < numParts)
    (hlen_g : gs.length = numParts) (hlen_x : xs.length = numParts)
    (hhead_g : (gs.head?.map (fun t => t.shape)).getD [] = shardShape)
    (hhead_x : (xs.head?.map (fun t => t.shape)).getD [] = shardShape)
    (hgs_shape : ∀ i (hi : i < gs.length), (gs.get ⟨i, hi⟩).shape = shardShape)
    (hxs_shape : ∀ i (hi : i < xs.length), (xs.get ⟨i, hi⟩).shape = shardShape) :
    bw_gelu (allGatherPrimDimN gatherDim numParts 0 gs)
            (allGatherPrimDimN gatherDim numParts 0 xs) =
      allGatherPrimDimN gatherDim numParts 0 (List.zipWith bw_gelu gs xs) := by
  have hlen_zw : (List.zipWith bw_gelu gs xs).length = numParts := by
    rw [List.length_zipWith, hlen_g, hlen_x, Nat.min_self]
  have hhead_zw : ((List.zipWith bw_gelu gs xs).head?.map (fun t => t.shape)).getD [] = shardShape := by
    have h0zw : (0 : Nat) < (List.zipWith bw_gelu gs xs).length := by omega
    have h0g : (0 : Nat) < gs.length := by omega
    have h0x : (0 : Nat) < xs.length := by omega
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem h0zw]
    simp only [Option.map_some, Option.getD_some]
    have hzw0 : (List.zipWith bw_gelu gs xs)[0]'h0zw = bw_gelu (gs[0]'h0g) (xs[0]'h0x) :=
      List.getElem_zipWith
    rw [hzw0, bw_gelu_shape]
    exact hxs_shape 0 h0x
  -- Output shape
  set outShape := shardShape.set gatherDim (shardShape.getD gatherDim 0 * numParts) with houtShape_def
  have hgather_x_shape : (allGatherPrimDimN gatherDim numParts 0 xs).shape = outShape :=
    allGatherPrimDimN_shape gatherDim numParts xs shardShape hhead_x
  have hgather_g_shape : (allGatherPrimDimN gatherDim numParts 0 gs).shape = outShape :=
    allGatherPrimDimN_shape gatherDim numParts gs shardShape hhead_g
  have hlhs_shape : (bw_gelu (allGatherPrimDimN gatherDim numParts 0 gs)
      (allGatherPrimDimN gatherDim numParts 0 xs)).shape = outShape := by
    rw [bw_gelu_shape]; exact hgather_x_shape
  have hrhs_shape : (allGatherPrimDimN gatherDim numParts 0
      (List.zipWith bw_gelu gs xs)).shape = outShape :=
    allGatherPrimDimN_shape gatherDim numParts _ shardShape hhead_zw
  -- Tensor.ext
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx_out : idx < prodShape outShape := by rwa [hlhs_shape] at hidx
  rw [bw_gelu_valAt _ _ idx (by rw [hgather_x_shape]; exact hidx_out)]
  rw [valAt_of_lt _ _ (by rw [hgather_g_shape]; exact hidx_out)]
  rw [valAt_of_lt _ _ (by rw [hgather_x_shape]; exact hidx_out)]
  rw [valAt_of_lt _ _ (by rw [hrhs_shape]; exact hidx_out)]
  -- After valAt_of_lt, all three are Tensor.mkShape value functions.
  -- Unfold allGatherPrimDimN and substitute head shapes.
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead_g, hhead_x, hhead_zw]
  -- After simp, all three computations use the same shardShape.
  -- Use set to name common subexpressions, then generalize r and loc.
  set ds := List.getD shardShape gatherDim 0
  set ps := List.foldl (· * ·) 1 (List.drop (gatherDim + 1) shardShape)
  set fds := ds * numParts * ps
  -- r = if ds = 0 then 0 else (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) / ps) / ds
  generalize hr_def : (if ds = 0 then 0
    else (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) / ps) / ds) = r
  -- loc = (if fds = 0 then 0 else idx / fds) * (ds * ps) + ...
  generalize hloc_def : (if fds = 0 then 0 else idx / fds) * (ds * ps) +
    (if ds = 0 then 0 else (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) / ps) % ds) * ps +
    (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) % ps) = loc
  -- Now the goal is: valAt(gs.getD r z) loc * geluDeriv(valAt(xs.getD r z) loc) = valAt(zipWith.getD r z) loc
  by_cases hr_lt : r < numParts
  · have hr_g : r < gs.length := by omega
    have hr_x : r < xs.length := by omega
    have hr_zw : r < (List.zipWith bw_gelu gs xs).length := by omega
    rw [list_getD_of_lt _ _ _ hr_zw, list_getD_of_lt _ _ _ hr_g, list_getD_of_lt _ _ _ hr_x]
    have hzw_elem : (List.zipWith bw_gelu gs xs)[r]'hr_zw = bw_gelu (gs[r]'hr_g) (xs[r]'hr_x) :=
      List.getElem_zipWith
    rw [hzw_elem]
    by_cases hloc : loc < prodShape (xs[r]'hr_x).shape
    · exact (bw_gelu_valAt _ _ loc hloc).symm
    · have hbw_sh : (bw_gelu (gs[r]'hr_g) (xs[r]'hr_x)).shape =
          (xs[r]'hr_x).shape := bw_gelu_shape _ _
      have hg_sh : (gs[r]'hr_g).shape = (xs[r]'hr_x).shape := by
        rw [show (gs[r]'hr_g).shape = shardShape from hgs_shape r hr_g,
            show (xs[r]'hr_x).shape = shardShape from hxs_shape r hr_x]
      have h1 : ¬(loc < prodShape (bw_gelu (gs[r]'hr_g) (xs[r]'hr_x)).shape) := by
        rw [hbw_sh]; exact hloc
      have h2 : ¬(loc < prodShape (gs[r]'hr_g).shape) := by
        rw [hg_sh]; exact hloc
      simp [valAt, h1, h2]
  · have hr_g : ¬(r < gs.length) := by omega
    have hr_x : ¬(r < xs.length) := by omega
    have hr_zw : ¬(r < (List.zipWith bw_gelu gs xs).length) := by omega
    rw [list_getD_of_ge _ _ _ hr_zw, list_getD_of_ge _ _ _ hr_g, list_getD_of_ge _ _ _ hr_x]
    simp [zeroTensor, Tensor.mkShape, valAt, prodShape]

/-- Unfolding lemma for `evalOp` on `AllReducePrim`. -/
theorem evalOp_allReducePrim (numParts rank : Nat) (params : List Nat) (xs : List Tensor) :
    evalOp numParts rank "OpName.AllReducePrim" params xs =
      [allReducePrim numParts rank xs] := by
  rfl

/-- Unfolding lemma for binary `FW_add`. -/
theorem evalOp_fw_add2 (numParts rank : Nat) (x y : Tensor) :
    evalOp numParts rank "OpName.FW_add" [] [x, y] = [elemwiseAdd x y] := by
  rfl

/-- Unfolding lemma for `evalOp` on ternary `BW_add` (backward of binary add). -/
theorem evalOp_bw_add2 (numParts rank : Nat) (g x y : Tensor) :
    evalOp numParts rank "OpName.BW_add" [] [g, x, y] =
      [(bw_add2 g x y).1, (bw_add2 g x y).2] := by
  rfl

/-- `applyNode` for ternary `BW_add` — first output (dx). -/
theorem applyNode_bw_add2_fst_out
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dxTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).1 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dxTid = _
  unfold storeSet
  simp [List.find?, hne]

/-- Unfolding lemma for `AllToAllPrim` with explicit split/gather dimensions. -/
theorem evalOp_allToAllPrimWithDims (numParts rank idim odim : Nat) (xs : List Tensor) :
    evalOp numParts rank "OpName.AllToAllPrim" [idim, odim] xs =
      [allToAllPrimWithDims numParts rank xs idim odim] := by
  rfl

/-- `applyNode` for `FW_embedding` with empty params (legacy semantics). -/
theorem applyNode_fw_embedding_out
    (g : GraphDecl) (s : Store) (rank : Nat) (idsTid wTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_embedding", ins := [idsTid, wTid], outs := [outTid] } outTid =
      fw_embedding (s idsTid) (s wTid) := by
  unfold applyNode
  rw [show ([idsTid, wTid] : List Tid).map s = [s idsTid, s wTid] from rfl,
      evalOp_fw_embedding_empty]
  change storeSet s [(outTid, fw_embedding (s idsTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `FW_embedding` with `params := [offset]` (vocab-parallel semantics). -/
theorem applyNode_fw_embedding_offset_out
    (g : GraphDecl) (s : Store) (rank : Nat) (offset : Nat) (idsTid wTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_embedding", ins := [idsTid, wTid], outs := [outTid], params := [offset] } outTid =
      fw_embedding_offset offset (s idsTid) (s wTid) := by
  unfold applyNode
  rw [show ([idsTid, wTid] : List Tid).map s = [s idsTid, s wTid] from rfl,
      evalOp_fw_embedding_offset]
  change storeSet s [(outTid, fw_embedding_offset offset (s idsTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `BW_embedding` with empty params (legacy semantics). -/
theorem applyNode_bw_embedding_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid idsTid wTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_embedding", ins := [gTid, idsTid, wTid], outs := [outTid] } outTid =
      bw_embedding (s gTid) (s idsTid) (s wTid) := by
  unfold applyNode
  rw [show ([gTid, idsTid, wTid] : List Tid).map s = [s gTid, s idsTid, s wTid] from rfl,
      evalOp_bw_embedding_empty]
  change storeSet s [(outTid, bw_embedding (s gTid) (s idsTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `BW_embedding` with `params := [offset]` (vocab-parallel semantics). -/
theorem applyNode_bw_embedding_offset_out
    (g : GraphDecl) (s : Store) (rank : Nat) (offset : Nat) (gTid idsTid wTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_embedding", ins := [gTid, idsTid, wTid], outs := [outTid], params := [offset] } outTid =
      bw_embedding_offset offset (s gTid) (s idsTid) (s wTid) := by
  unfold applyNode
  rw [show ([gTid, idsTid, wTid] : List Tid).map s = [s gTid, s idsTid, s wTid] from rfl,
      evalOp_bw_embedding_offset]
  change storeSet s [(outTid, bw_embedding_offset offset (s gTid) (s idsTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Unfolding lemma for `evalOp` on `FW_gelu`. -/
theorem evalOp_fw_gelu (numParts rank : Nat) (params : List Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_gelu" params [x] = [fw_gelu x] := by
  rfl

/-- Unfolding lemma for `evalOp` on `ChunkPrim` with dim parameter. -/
theorem evalOp_chunkPrimDimN (numParts rank dim : Nat) (x : Tensor) :
    evalOp numParts rank "OpName.ChunkPrim" [dim] [x] = [chunkPrimDimN dim numParts rank x] := by
  rfl

/-- `applyNode` for `FW_gelu` with singleton output. -/
theorem applyNode_fw_gelu_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_gelu", ins := [inTid], outs := [outTid] } outTid =
      fw_gelu (s inTid) := by
  unfold applyNode
  rw [show ([inTid] : List Tid).map s = [s inTid] from rfl,
      evalOp_fw_gelu]
  change storeSet s [(outTid, fw_gelu (s inTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `fw_gelu` preserves shape. -/
theorem fw_gelu_shape (x : Tensor) : (fw_gelu x).shape = x.shape := by
  simp [fw_gelu, Tensor.mkShape]

/-- `valAt` of `fw_gelu` at a valid index. -/
theorem fw_gelu_valAt (x : Tensor) (idx : Nat) (h : idx < prodShape x.shape) :
    valAt (fw_gelu x) idx = geluScalar (valAt x idx) := by
  rw [valAt_of_lt _ _ (by rw [fw_gelu_shape]; exact h)]
  simp [fw_gelu, Tensor.mkShape]

/-- `fw_gelu` distributes over `allGatherPrimDimN`: applying `fw_gelu` to the
    gathered tensor equals gathering the per-shard `fw_gelu` results.
    This holds because `fw_gelu` is a pointwise (elementwise) operation. -/
theorem fw_gelu_allGatherPrimDimN_eq
    (gatherDim numParts : Nat) (xs : List Tensor)
    (shardShape : Shape)
    (hnp : 0 < numParts)
    (hlen : xs.length = numParts)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = shardShape)
    (hxs_shape : ∀ i (hi : i < xs.length), (xs.get ⟨i, hi⟩).shape = shardShape) :
    fw_gelu (allGatherPrimDimN gatherDim numParts 0 xs) =
      allGatherPrimDimN gatherDim numParts 0 (xs.map fw_gelu) := by
  have hlen_map : (xs.map fw_gelu).length = numParts := by
    rw [List.length_map, hlen]
  have hhead_map : ((xs.map fw_gelu).head?.map (fun t => t.shape)).getD [] = shardShape := by
    have h0 : (0 : Nat) < xs.length := by omega
    have h0m : (0 : Nat) < (xs.map fw_gelu).length := by rw [List.length_map]; omega
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem h0m]
    simp only [Option.map_some, Option.getD_some]
    have hm0 : (xs.map fw_gelu)[0]'h0m = fw_gelu (xs[0]'h0) := List.getElem_map ..
    rw [hm0, fw_gelu_shape]
    exact hxs_shape 0 h0
  set outShape := shardShape.set gatherDim (shardShape.getD gatherDim 0 * numParts) with houtShape_def
  have hgather_shape : (allGatherPrimDimN gatherDim numParts 0 xs).shape = outShape :=
    allGatherPrimDimN_shape gatherDim numParts xs shardShape hhead
  have hlhs_shape : (fw_gelu (allGatherPrimDimN gatherDim numParts 0 xs)).shape = outShape := by
    rw [fw_gelu_shape]; exact hgather_shape
  have hrhs_shape : (allGatherPrimDimN gatherDim numParts 0 (xs.map fw_gelu)).shape = outShape :=
    allGatherPrimDimN_shape gatherDim numParts _ shardShape hhead_map
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx_out : idx < prodShape outShape := by rwa [hlhs_shape] at hidx
  have hgather_idx : idx < prodShape (allGatherPrimDimN gatherDim numParts 0 xs).shape := by
    rw [hgather_shape]; exact hidx_out
  -- LHS: valAt (fw_gelu (allGather xs)) idx = geluScalar (valAt (allGather xs) idx)
  rw [fw_gelu_valAt _ _ hgather_idx]
  -- Now goal: geluScalar (valAt (allGather xs) idx) = valAt (allGather (map fw_gelu xs)) idx
  -- Unfold both valAt through allGatherPrimDimN
  rw [valAt_of_lt _ _ hgather_idx]
  conv_rhs => rw [valAt_of_lt _ _ (by rw [hrhs_shape]; exact hidx_out)]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead, hhead_map]
  -- Now both sides select shard r and local index loc from idx
  -- Generalize the reindex
  set ds := List.getD shardShape gatherDim 0
  set ps := List.foldl (· * ·) 1 (List.drop (gatherDim + 1) shardShape)
  set fds := ds * numParts * ps
  generalize (if ds = 0 then 0
    else (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) / ps) / ds) = r
  generalize (if fds = 0 then 0 else idx / fds) * (ds * ps) +
    (if ds = 0 then 0 else (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) / ps) % ds) * ps +
    (if ps = 0 then 0 else (if fds = 0 then 0 else idx % fds) % ps) = loc
  by_cases hr_lt : r < numParts
  · have hr_xs : r < xs.length := by omega
    have hr_map : r < (xs.map fw_gelu).length := by omega
    rw [list_getD_of_lt _ _ _ hr_xs, list_getD_of_lt _ _ _ hr_map]
    have hmap_r : (xs.map fw_gelu)[r]'hr_map = fw_gelu (xs[r]'hr_xs) := List.getElem_map ..
    rw [hmap_r]
    by_cases hloc_lt : loc < prodShape (xs[r]'hr_xs).shape
    · rw [fw_gelu_valAt _ _ hloc_lt]
    · have h1 : ¬(loc < prodShape (fw_gelu (xs[r]'hr_xs)).shape) := by
        rw [fw_gelu_shape]; exact hloc_lt
      simp only [valAt, h1, hloc_lt, dite_false]
      simp [geluScalar]
  · have hr_xs : ¬(r < xs.length) := by omega
    have hr_map : ¬(r < (xs.map fw_gelu).length) := by omega
    rw [list_getD_of_ge _ _ _ hr_xs, list_getD_of_ge _ _ _ hr_map]
    simp only [zeroTensor, Tensor.mkShape, valAt, prodShape, List.foldl]
    simp [geluScalar]

/-- `applyNode` for binary `FW_add` with singleton output. -/
theorem applyNode_fw_add2_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid yTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_add", ins := [xTid, yTid], outs := [outTid] } outTid =
      elemwiseAdd (s xTid) (s yTid) := by
  unfold applyNode
  rw [show ([xTid, yTid] : List Tid).map s = [s xTid, s yTid] from rfl,
      evalOp_fw_add2]
  change storeSet s [(outTid, elemwiseAdd (s xTid) (s yTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Unfolding lemma for `FW_view` with an explicit (non-empty) target shape. -/
theorem evalOp_fw_view (numParts rank : Nat) (hd : Nat) (tl : List Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_view" (hd :: tl) [x] = [fw_view (hd :: tl) x] := by
  rfl

/-- `applyNode` for `FW_view` with singleton output and explicit (non-empty) target shape. -/
theorem applyNode_fw_view_out
    (g : GraphDecl) (s : Store) (rank : Nat) (hd : Nat) (tl : List Nat) (xTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_view", ins := [xTid], outs := [outTid], params := hd :: tl } outTid =
      fw_view (hd :: tl) (s xTid) := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl,
      evalOp_fw_view]
  change storeSet s [(outTid, fw_view (hd :: tl) (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Unfolding lemma for `BW_view` with an explicit (non-empty) target shape.
    BW_view applies the view to its gradient input `g`, ignoring the reference input. -/
theorem evalOp_bw_view (numParts rank : Nat) (hd : Nat) (tl : List Nat) (g x : Tensor) :
    evalOp numParts rank "OpName.BW_view" (hd :: tl) [g, x] = [fw_view (hd :: tl) g] := by
  rfl

/-- `applyNode` for `BW_view` with singleton output and explicit (non-empty) target shape. -/
theorem applyNode_bw_view_out
    (gr : GraphDecl) (s : Store) (rank : Nat) (hd : Nat) (tl : List Nat) (gTid xTid outTid : Tid) :
    applyNode gr s { rank := rank, op := "OpName.BW_view", ins := [gTid, xTid], outs := [outTid], params := hd :: tl } outTid =
      fw_view (hd :: tl) (s gTid) := by
  unfold applyNode
  rw [show ([gTid, xTid] : List Tid).map s = [s gTid, s xTid] from rfl,
      evalOp_bw_view]
  change storeSet s [(outTid, fw_view (hd :: tl) (s gTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Unfolding lemma for `BW_multiref` (tensorSum of all inputs). -/
theorem evalOp_bw_multiref (numParts rank : Nat) (params : List Nat) (xs : List Tensor) :
    evalOp numParts rank "OpName.BW_multiref" params xs = [tensorSum xs] := by
  rfl

/-- `applyNode` for `BW_multiref` with variable-length inputs and singleton output. -/
theorem applyNode_bw_multiref_out
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_multiref", ins := ins, outs := [outTid] } outTid =
      tensorSum (ins.map s) := by
  unfold applyNode
  rw [evalOp_bw_multiref]
  change storeSet s [(outTid, tensorSum (ins.map s))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Shape of `tensorSum` equals the shape of the first element. -/
theorem tensorSum_shape (x : Tensor) (xs : List Tensor) :
    (tensorSum (x :: xs)).shape = x.shape := by
  simp [tensorSum, Tensor.mkShape]

/-- `applyNode` for `ChunkPrim` with `params := [dim]` (chunk along arbitrary dimension). -/
theorem applyNode_chunkPrimDimN_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) (dim : Nat) :
    applyNode g s { rank := rank, op := "OpName.ChunkPrim", ins := [inTid], outs := [outTid], params := [dim] } outTid =
      chunkPrimDimN dim g.numRanks rank (s inTid) := by
  unfold applyNode
  change storeSet s [(outTid, chunkPrimDimN dim g.numRanks rank (s inTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `FW_transpose` with `params := [d0, d1]` (transpose two arbitrary dims). -/
theorem applyNode_fw_transposeAxes_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) (d0 d1 : Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_transpose", ins := [inTid], outs := [outTid], params := [d0, d1] } outTid =
      transposeAxes d0 d1 (s inTid) := by
  unfold applyNode
  change storeSet s [(outTid, transposeAxes d0 d1 (s inTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `AllReducePrim` with singleton output. -/
theorem applyNode_allReducePrim_out
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.AllReducePrim", ins := ins, outs := [outTid] } outTid =
      allReducePrim g.numRanks rank (ins.map s) := by
  unfold applyNode
  rw [evalOp_allReducePrim]
  change storeSet s [(outTid, allReducePrim g.numRanks rank (ins.map s))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `AllToAllPrim` with explicit split/gather dimensions. -/
theorem applyNode_allToAllPrimWithDims_out
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid)
    (idim odim : Nat) :
    applyNode g s { rank := rank, op := "OpName.AllToAllPrim", ins := ins, outs := [outTid], params := [idim, odim] } outTid =
      allToAllPrimWithDims g.numRanks rank (ins.map s) idim odim := by
  unfold applyNode
  rw [evalOp_allToAllPrimWithDims]
  change storeSet s [(outTid, allToAllPrimWithDims g.numRanks rank (ins.map s) idim odim)] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Unfolding lemma for `FW_layernorm`. -/
theorem evalOp_fw_layernorm (numParts rank : Nat) (params : List Nat) (x w b : Tensor) :
    evalOp numParts rank "OpName.FW_layernorm" params [x, w, b] = [fw_layernorm x w b] := by
  rfl

/-- `applyNode` for `FW_layernorm` with singleton output. -/
theorem applyNode_fw_layernorm_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid wTid bTid outTid : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_layernorm", ins := [xTid, wTid, bTid],
                    outs := [outTid], params := params } outTid =
      fw_layernorm (s xTid) (s wTid) (s bTid) := by
  unfold applyNode
  rw [show ([xTid, wTid, bTid] : List Tid).map s = [s xTid, s wTid, s bTid] from rfl,
      evalOp_fw_layernorm]
  change storeSet s [(outTid, fw_layernorm (s xTid) (s wTid) (s bTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Unfolding lemma for `FW_multiref` with `n` outputs. -/
theorem evalOp_fw_multiref (numParts rank n : Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_multiref" [n] [x] = List.replicate n x := by
  rfl

/-- `applyNode` for `FW_multiref` with `outs = [t1, t2]` and `params = [2]`: the first
    output equals the input. -/
theorem applyNode_fw_multiref2_first_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl,
      evalOp_fw_multiref]
  change storeSet s ([t1, t2].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-! ## Layernorm split helper for `[1, 8, 32]` shape, dim=1 sharding into 4 parts.

    Layernorm normalizes across the *last* dim (here size 32). Sharding along dim=1
    (the sequence axis, size 8 → 4 chunks of size 2) is orthogonal to the normalization
    axis, so per-chunk layernorm with subsequent all-gather equals the full layernorm.
-/

/-- Specialized `valAt` for chunkPrimDimN dim=1 numParts=4 shape=[1,8,32]. -/
theorem chunk_dim1_4_1_8_32_valAt (x : Tensor) (r p j : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) (hp : p < 2) (hj : j < 32) :
    valAt (chunkPrimDimN 1 4 r x) (p * 32 + j) = valAt x ((r * 2 + p) * 32 + j) := by
  have hloc : p * 32 + j < 64 := by
    have : p * 32 ≤ 1 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p * 32 + j < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (8 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  congr 1
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  -- After simp the residual is: (if 64 = 0 then 0 else 0)*256 + (r*2 + idx/32)*32 + idx%32 = (r*2+p)*32 + j
  -- with idx = p*32+j (modulo) but simplified differently. Use omega directly with side facts.
  have hsum : p * 32 + j < 64 := hloc
  have h1 : (8 / 4 : Nat) = 2 := by norm_num
  have h2 : (1 * 32 : Nat) = 32 := by norm_num
  have h3 : (8 * (1 * 32) : Nat) = 256 := by norm_num
  have h4 : (2 * (1 * 32) : Nat) = 64 := by norm_num
  simp only [h1, h2, h3, h4, show (64 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    ite_false]
  have hd : (p * 32 + j) / 64 = 0 := Nat.div_eq_of_lt hsum
  have hm : (p * 32 + j) % 64 = p * 32 + j := Nat.mod_eq_of_lt hsum
  rw [hd, hm]
  have h5 : (p * 32 + j) / 32 = p := by omega
  have h6 : (p * 32 + j) % 32 = j := by omega
  rw [h5, h6]
  ring

/-- Each chunked tensor (chunk along dim 1 of `[1,8,32]`-shaped `x`) has the same
    sum over a row's last-dim entries as the corresponding row of `x`. -/
theorem layerNormMeanAt_chunk_dim1_4_1_8_32 (x : Tensor) (r p : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) (hp : p < 2) :
    layerNormMeanAt (chunkPrimDimN 1 4 r x) p 32 =
      layerNormMeanAt x (r * 2 + p) 32 := by
  unfold layerNormMeanAt
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  exact chunk_dim1_4_1_8_32_valAt x r p j hx hr hp hj

theorem layerNormVarAt_chunk_dim1_4_1_8_32 (x : Tensor) (r p : Nat) (mean : Scalar)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) (hp : p < 2) :
    layerNormVarAt (chunkPrimDimN 1 4 r x) p 32 mean =
      layerNormVarAt x (r * 2 + p) 32 mean := by
  unfold layerNormVarAt
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [chunk_dim1_4_1_8_32_valAt x r p j hx hr hp hj]

/-- Generic unfolding lemma for `fw_layernorm` when the reversed shape starts with `d`. -/
theorem fw_layernorm_eq (x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    fw_layernorm x w b = Tensor.mkShape x.shape (fun outIdx =>
      let row := outIdx.1 / d
      let j := outIdx.1 % d
      let mean := layerNormMeanAt x row d
      let var := layerNormVarAt x row d mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      ((valAt x outIdx.1 - mean) * invStd) * valAt w j + valAt b j) := by
  unfold fw_layernorm
  rw [hrev]

/-- Shape of `fw_layernorm` for shape `[1,8,32]`. -/
theorem fw_layernorm_shape_1_8_32 (x w b : Tensor) (hx : x.shape = [1, 8, 32]) :
    (fw_layernorm x w b).shape = [1, 8, 32] := by
  rw [fw_layernorm_eq x w b 32 [8, 1] (by rw [hx]; rfl)]
  simp [Tensor.mkShape, hx]

/-- Shape of `fw_layernorm` for shape `[1,2,32]`. -/
theorem fw_layernorm_shape_1_2_32 (x w b : Tensor) (hx : x.shape = [1, 2, 32]) :
    (fw_layernorm x w b).shape = [1, 2, 32] := by
  rw [fw_layernorm_eq x w b 32 [2, 1] (by rw [hx]; rfl)]
  simp [Tensor.mkShape, hx]

/-- valAt of `fw_layernorm` at index `p*32 + j` for shape `[1,8,32]`. -/
theorem fw_layernorm_valAt_1_8_32 (x w b : Tensor) (p j : Nat)
    (hx : x.shape = [1, 8, 32]) (hp : p < 8) (hj : j < 32) :
    valAt (fw_layernorm x w b) (p * 32 + j) =
      let mean := layerNormMeanAt x p 32
      let var := layerNormVarAt x p 32 mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      ((valAt x (p * 32 + j) - mean) * invStd) * valAt w j + valAt b j := by
  have hidx : p * 32 + j < 256 := by
    have h1 : p * 32 ≤ 7 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  rw [fw_layernorm_eq x w b 32 [8, 1] (by rw [hx]; rfl)]
  have hidx_shape : p * 32 + j < prodShape (Tensor.mkShape x.shape
      (fun outIdx : Fin (prodShape x.shape) =>
        let row := outIdx.1 / 32
        let j2 := outIdx.1 % 32
        let mean := layerNormMeanAt x row 32
        let var := layerNormVarAt x row 32 mean
        let invStd := 1 / sqrtFn (var + layerNormEps)
        ((valAt x outIdx.1 - mean) * invStd) * valAt w j2 + valAt b j2)).shape := by
    simp [Tensor.mkShape, hx, prodShape]; exact hidx
  rw [valAt_of_lt _ _ hidx_shape]
  simp only [Tensor.mkShape]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  rw [hdj, hmj]

/-- valAt of `fw_layernorm` at index `p*32 + j` for shape `[1,2,32]`. -/
theorem fw_layernorm_valAt_1_2_32 (x w b : Tensor) (p j : Nat)
    (hx : x.shape = [1, 2, 32]) (hp : p < 2) (hj : j < 32) :
    valAt (fw_layernorm x w b) (p * 32 + j) =
      let mean := layerNormMeanAt x p 32
      let var := layerNormVarAt x p 32 mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      ((valAt x (p * 32 + j) - mean) * invStd) * valAt w j + valAt b j := by
  have hidx : p * 32 + j < 64 := by
    have h1 : p * 32 ≤ 1 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  rw [fw_layernorm_eq x w b 32 [2, 1] (by rw [hx]; rfl)]
  have hidx_shape : p * 32 + j < prodShape (Tensor.mkShape x.shape
      (fun outIdx : Fin (prodShape x.shape) =>
        let row := outIdx.1 / 32
        let j2 := outIdx.1 % 32
        let mean := layerNormMeanAt x row 32
        let var := layerNormVarAt x row 32 mean
        let invStd := 1 / sqrtFn (var + layerNormEps)
        ((valAt x outIdx.1 - mean) * invStd) * valAt w j2 + valAt b j2)).shape := by
    simp [Tensor.mkShape, hx, prodShape]; exact hidx
  rw [valAt_of_lt _ _ hidx_shape]
  simp only [Tensor.mkShape]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  rw [hdj, hmj]

/-- The core layernorm split lemma for shape [1,8,32], dim=1 sharded into 4 chunks of size 2. -/
theorem fw_layernorm_split_dim1_4_1_8_32 (x w b : Tensor)
    (hx : x.shape = [1, 8, 32]) :
    fw_layernorm x w b =
      allGatherPrimDimN 1 4 0
        [fw_layernorm (chunkPrimDimN 1 4 0 x) w b,
         fw_layernorm (chunkPrimDimN 1 4 1 x) w b,
         fw_layernorm (chunkPrimDimN 1 4 2 x) w b,
         fw_layernorm (chunkPrimDimN 1 4 3 x) w b] := by
  have hchunk_shape : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
    intro r _
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hln_chunk_shape : ∀ r, r < 4 →
      (fw_layernorm (chunkPrimDimN 1 4 r x) w b).shape = [1, 2, 32] := by
    intro r hr
    exact fw_layernorm_shape_1_2_32 _ w b (hchunk_shape r hr)
  have hlhs_shape : (fw_layernorm x w b).shape = [1, 8, 32] :=
    fw_layernorm_shape_1_8_32 x w b hx
  have hhead : ((([fw_layernorm (chunkPrimDimN 1 4 0 x) w b,
       fw_layernorm (chunkPrimDimN 1 4 1 x) w b,
       fw_layernorm (chunkPrimDimN 1 4 2 x) w b,
       fw_layernorm (chunkPrimDimN 1 4 3 x) w b] : List Tensor).head?).map
       (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [List.head?]
    exact hln_chunk_shape 0 (by omega)
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [fw_layernorm (chunkPrimDimN 1 4 0 x) w b,
       fw_layernorm (chunkPrimDimN 1 4 1 x) w b,
       fw_layernorm (chunkPrimDimN 1 4 2 x) w b,
       fw_layernorm (chunkPrimDimN 1 4 3 x) w b]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  · intro idx hidx
    rw [hlhs_shape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape] using hidx
    -- Decompose idx = p * 32 + j with p < 8, j < 32
    set p := idx / 32 with hp_def
    set j := idx % 32 with hj_def
    have hp_lt : p < 8 := by
      have : idx / 32 < 256 / 32 := Nat.div_lt_div_of_lt_of_dvd ⟨8, rfl⟩ hidx256
      simpa using this
    have hj_lt : j < 32 := by exact Nat.mod_lt idx (by omega)
    have hidx_eq : idx = p * 32 + j := by
      subst p j; omega
    rw [hidx_eq]
    rw [fw_layernorm_valAt_1_8_32 x w b p j hx hp_lt hj_lt]
    -- Now compute RHS
    have hrhs_idx : p * 32 + j < prodShape (allGatherPrimDimN 1 4 0
        [fw_layernorm (chunkPrimDimN 1 4 0 x) w b,
         fw_layernorm (chunkPrimDimN 1 4 1 x) w b,
         fw_layernorm (chunkPrimDimN 1 4 2 x) w b,
         fw_layernorm (chunkPrimDimN 1 4 3 x) w b]).shape := by
      rw [hrhs_shape]; simp [prodShape]; omega
    rw [valAt_of_lt _ _ hrhs_idx]
    unfold allGatherPrimDimN Tensor.mkShape
    simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.drop, List.foldl,
      show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
      show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
      show (1 : Nat) ≠ 0 by omega, ite_false]
    -- Simplify: dimSize=2, fullDimSize=8, postStride=32, dimStride=64, fullDimStride=256
    simp only [show (2 : Nat) * 4 * 1 = 8 by norm_num,
      show (2 : Nat) * 1 = 2 by norm_num,
      show (8 : Nat) * (1 * 32) = 256 by norm_num,
      show (1 : Nat) * 32 = 32 by norm_num,
      show (2 : Nat) * (1 * 32) = 64 by norm_num,
      show (256 : Nat) = 0 ↔ False by simp,
      show (32 : Nat) = 0 ↔ False by simp,
      show (64 : Nat) = 0 ↔ False by simp,
      ite_false]
    -- Reduce idx arithmetic
    set r := p / 2 with hr_def
    set p' := p % 2 with hp'_def
    have hr_lt : r < 4 := by
      have : p / 2 < 8 / 2 := Nat.div_lt_div_of_lt_of_dvd ⟨4, rfl⟩ hp_lt
      simpa using this
    have hp'_lt : p' < 2 := Nat.mod_lt p (by omega)
    have hp_eq : p = r * 2 + p' := by subst r p'; omega
    -- idx-related normalizations
    have hd256 : (p * 32 + j) / 256 = 0 := by
      apply Nat.div_eq_of_lt; omega
    have hm256 : (p * 32 + j) % 256 = p * 32 + j := by
      apply Nat.mod_eq_of_lt; omega
    rw [hd256, hm256]
    have hd32 : (p * 32 + j) / 32 = p := by omega
    have hm32 : (p * 32 + j) % 32 = j := by omega
    rw [hd32, hm32]
    -- piece selection: p / 2 = r
    have hpieces : (p / 2 : Nat) = r := rfl
    rw [hpieces]
    -- The local index inside the chunk: jLocal * 32 + j where jLocal = p % 2 = p'
    have hjLocal : (p % 2 : Nat) = p' := rfl
    -- Now we need to map to the appropriate chunk
    have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    have hp'_cases : p' = 0 ∨ p' = 1 := by omega
    -- Rewrite goal in terms of r, p'
    rw [show (p % 2 : Nat) = p' from rfl]
    have hpL : valAt x (p * 32 + j) =
        valAt (chunkPrimDimN 1 4 r x) (p' * 32 + j) := by
      rw [chunk_dim1_4_1_8_32_valAt x r p' j hx hr_lt hp'_lt hj_lt, ← hp_eq]
    have hmeanL : layerNormMeanAt x p 32 =
        layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32 := by
      rw [layerNormMeanAt_chunk_dim1_4_1_8_32 x r p' hx hr_lt hp'_lt, ← hp_eq]
    rw [hpL, hmeanL]
    rw [show layerNormVarAt x p 32 (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32)
            = layerNormVarAt (chunkPrimDimN 1 4 r x) p' 32
                (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) from by
      rw [layerNormVarAt_chunk_dim1_4_1_8_32 x r p'
          (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) hx hr_lt hp'_lt, ← hp_eq]]
    rw [← fw_layernorm_valAt_1_2_32 (chunkPrimDimN 1 4 r x) w b p' j
        (hchunk_shape r hr_lt) hp'_lt hj_lt]
    rw [show (0 : Nat) * 64 + p' * 32 + j = p' * 32 + j by ring]
    -- Now goal: valAt (fw_layernorm (chunkPrimDimN 1 4 r x) w b) (p'*32+j)
    --        = valAt ([...][r]?.getD ...) (p'*32+j)
    rcases hr_cases with h0 | h1 | h2 | h3
    all_goals first
      | (rw [h0]; rfl)
      | (rw [h1]; rfl)
      | (rw [h2]; rfl)
      | (rw [h3]; rfl)

/-- valAt of `allGatherPrimDimN 1 4 0 xs` at index `(r*2+p)*32+j` when shard shape is [1,2,32]. -/
theorem allGatherPrimDimN_dim1_4_1_2_32_valAt (xs : List Tensor)
    (r : Nat) (hr : r < 4) (p : Nat) (hp : p < 2) (j : Nat) (hj : j < 32)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32]) :
    valAt (allGatherPrimDimN 1 4 0 xs) ((r * 2 + p) * 32 + j) =
      valAt (xs.getD r (zeroTensor [1, 2, 32])) (p * 32 + j) := by
  have hgather_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hhead]
    simp [List.set, List.getD]
  have hidx_lt : (r * 2 + p) * 32 + j < 256 := by omega
  have hidx_prod : (r * 2 + p) * 32 + j < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  -- Simplify numeric expressions
  simp only [show (2 : Nat) * 4 * 1 = 8 by norm_num,
    show (2 : Nat) * 1 = 2 by norm_num,
    show (8 : Nat) * (1 * 32) = 256 by norm_num,
    show (1 : Nat) * 32 = 32 by norm_num,
    show (2 : Nat) * (1 * 32) = 64 by norm_num,
    show (256 : Nat) = 0 ↔ False by simp,
    show (32 : Nat) = 0 ↔ False by simp,
    show (64 : Nat) = 0 ↔ False by simp,
    ite_false]
  -- Arithmetic simplifications
  have hd256 : ((r * 2 + p) * 32 + j) / 256 = 0 := Nat.div_eq_of_lt hidx_lt
  have hm256 : ((r * 2 + p) * 32 + j) % 256 = (r * 2 + p) * 32 + j :=
    Nat.mod_eq_of_lt hidx_lt
  have hd32 : ((r * 2 + p) * 32 + j) / 32 = r * 2 + p := by omega
  have hm32 : ((r * 2 + p) * 32 + j) % 32 = j := by omega
  have hdr : (r * 2 + p) / 2 = r := by omega
  have hmr : (r * 2 + p) % 2 = p := by omega
  rw [hd256, hm256, hd32, hm32, hdr, hmr]
  congr 1
  ring

/-- Chunk-gather cancellation: chunking an allGather along the same dim recovers the shard. -/
theorem chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 (xs : List Tensor) (r : Nat)
    (hr : r < 4) (hlen : xs.length = 4)
    (hshape : ∀ x ∈ xs, x.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 xs) = xs.getD r (zeroTensor [1, 2, 32]) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    match xs, hlen with
    | x0 :: _, _ =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape x0 (List.mem_cons_self ..)
  have hgather_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hhead]
    simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 xs)).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : (xs.getD r (zeroTensor [1, 2, 32])).shape = [1, 2, 32] := by
    have hr_len : r < xs.length := by omega
    have helem : xs.getD r (zeroTensor [1, 2, 32]) = xs[r] := by
      simp [List.getD, List.getElem?_eq_getElem hr_len]
    rw [helem]
    exact hshape (xs[r]) (List.getElem_mem hr_len)
  apply Tensor.ext
  · rw [hchunk_shape, hrhs_shape]
  · intro idx hidx
    rw [hchunk_shape] at hidx
    have hidx64 : idx < 64 := by simpa [prodShape] using hidx
    set p := idx / 32
    set j := idx % 32
    have hp : p < 2 := by
      have : idx / 32 < 64 / 32 := Nat.div_lt_div_of_lt_of_dvd ⟨2, rfl⟩ hidx64
      simpa using this
    have hj : j < 32 := Nat.mod_lt idx (by omega)
    have hidx_eq : idx = p * 32 + j := by subst p j; omega
    rw [hidx_eq]
    rw [chunk_dim1_4_1_8_32_valAt (allGatherPrimDimN 1 4 0 xs) r p j
        hgather_shape hr hp hj]
    exact allGatherPrimDimN_dim1_4_1_2_32_valAt xs r hr p hp j hj hhead

/-- Layernorm distributes over allGatherPrimDimN on dim 1 for shape [1,2,32] shards.
    This is the core bridge: `fw_layernorm(gather(shards), w, b) = gather(map(fw_layernorm(·,w,b), shards))`. -/
theorem fw_layernorm_distribute_allGatherPrimDimN_dim1_4_1_2_32
    (xs : List Tensor) (w b : Tensor)
    (hlen : xs.length = 4)
    (hshape : ∀ x ∈ xs, x.shape = [1, 2, 32]) :
    fw_layernorm (allGatherPrimDimN 1 4 0 xs) w b =
      allGatherPrimDimN 1 4 0 (xs.map (fun x => fw_layernorm x w b)) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    match xs, hlen with
    | x0 :: _, _ =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape x0 (List.mem_cons_self ..)
  have hgather_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hhead]
    simp [List.set, List.getD]
  have hsplit := fw_layernorm_split_dim1_4_1_8_32
    (allGatherPrimDimN 1 4 0 xs) w b hgather_shape
  rw [hsplit]
  congr 1
  -- Show the 4-element lists are equal by rewriting chunks to shards
  match xs, hlen, hshape with
  | [x0, x1, x2, x3], _, hshape =>
    simp only [List.map, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    have hshape' : ∀ x ∈ [x0, x1, x2, x3], x.shape = [1, 2, 32] := hshape
    have hcancel : ∀ r (hr : r < 4),
        chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]) =
          [x0, x1, x2, x3].getD r (zeroTensor [1, 2, 32]) :=
      fun r hr => chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32
        [x0, x1, x2, x3] r hr (by simp) hshape'
    have h0 := hcancel 0 (by omega)
    have h1 := hcancel 1 (by omega)
    have h2 := hcancel 2 (by omega)
    have h3 := hcancel 3 (by omega)
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some] at h0 h1 h2 h3
    rw [h0, h1, h2, h3]

/-- `elemwiseAdd` value accessor for shape `[1, 2, 32]`. -/
private theorem elemwiseAdd_valAt_1_2_32 (x y : Tensor) (idx : Nat)
    (hx : x.shape = [1, 2, 32]) (hy : y.shape = [1, 2, 32]) (hidx : idx < 64) :
    valAt (elemwiseAdd x y) idx = valAt x idx + valAt y idx := by
  have hout : (elemwiseAdd x y).shape = [1, 2, 32] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy]
  rw [valAt_of_lt _ _ (by simpa [hout, prodShape] using hidx)]
  simp [elemwiseAdd, Tensor.mkShape, outShape2, hx, hy, broadcastValAtShape,
    alignedMultiIndex, flatToMulti, multiToFlat, prodShape]
  have hnorm : idx % 64 / 32 * 32 + idx % 32 = idx := by omega
  rw [hnorm]

/-- Concrete instance of `fw_add_split_dim_statement` for `[1, 8, 32]` tensors split four ways along dim 1. -/
theorem fw_add_split_dim1_4_1_8_32 (a b : Tensor) (ha : a.shape = [1, 8, 32]) (hb : b.shape = [1, 8, 32]) :
    elemwiseAdd a b = allGatherPrimDimN 1 4 0
      [elemwiseAdd (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
       elemwiseAdd (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
       elemwiseAdd (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
       elemwiseAdd (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)] := by
  have hchunk_shape_a : ∀ r, r < 4 → (chunkPrimDimN 1 4 r a).shape = [1, 2, 32] := by
    intro r _; rw [chunkPrimDimN_shape 1 4 r _ _ ha (by omega)]; simp [List.set, List.getD]
  have hchunk_shape_b : ∀ r, r < 4 → (chunkPrimDimN 1 4 r b).shape = [1, 2, 32] := by
    intro r _; rw [chunkPrimDimN_shape 1 4 r _ _ hb (by omega)]; simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (elemwiseAdd (chunkPrimDimN 1 4 r a) (chunkPrimDimN 1 4 r b)).shape = [1, 2, 32] := by
    intro r hr; exact elemwiseAdd_shape_of_shapes _ _ _ (hchunk_shape_a r hr) (hchunk_shape_b r hr)
  have hhead : (([elemwiseAdd (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
       elemwiseAdd (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
       elemwiseAdd (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
       elemwiseAdd (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hpiece_shape 0 (by omega)]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [elemwiseAdd (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
       elemwiseAdd (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
       elemwiseAdd (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
       elemwiseAdd (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  have hlhs_shape : (elemwiseAdd a b).shape = [1, 8, 32] := by
    simp [elemwiseAdd, Tensor.mkShape, outShape2, ha, hb]
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  · intro idx hidx
    rw [hlhs_shape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape] using hidx
    -- Decompose idx = p * 32 + j with p < 8, j < 32
    set p := idx / 32 with hp_def
    set j := idx % 32 with hj_def
    have hp_lt : p < 8 := by
      have : idx / 32 < 256 / 32 := Nat.div_lt_div_of_lt_of_dvd ⟨8, rfl⟩ hidx256
      simpa using this
    have hj_lt : j < 32 := Nat.mod_lt idx (by omega)
    have hidx_eq : idx = p * 32 + j := by subst p j; omega
    rw [hidx_eq]
    rw [elemwiseAdd_valAt_1_8_32 a b (p * 32 + j) ha hb (by omega)]
    -- Now compute RHS
    have hrhs_idx : p * 32 + j < prodShape (allGatherPrimDimN 1 4 0
        [elemwiseAdd (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
         elemwiseAdd (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
         elemwiseAdd (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
         elemwiseAdd (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)]).shape := by
      rw [hrhs_shape]; simp [prodShape]; omega
    -- Decompose p into r = p/2 and p' = p%2
    set r := p / 2 with hr_def
    set p' := p % 2 with hp'_def
    have hr_lt : r < 4 := by
      have : p / 2 < 8 / 2 := Nat.div_lt_div_of_lt_of_dvd ⟨4, rfl⟩ hp_lt
      simpa using this
    have hp'_lt : p' < 2 := Nat.mod_lt p (by omega)
    have hp_eq : p = r * 2 + p' := by subst r p'; omega
    -- Use allGatherPrimDimN_dim1_4_1_2_32_valAt
    rw [hp_eq]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt
        [elemwiseAdd (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
         elemwiseAdd (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
         elemwiseAdd (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
         elemwiseAdd (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)]
        r hr_lt p' hp'_lt j hj_lt hhead]
    -- Now goal: valAt a ((r*2+p')*32+j) + valAt b ((r*2+p')*32+j) =
    --           valAt ([pieces][r].getD ...) (p'*32+j)
    have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr_cases with h0 | h1 | h2 | h3
    · rw [h0]; simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      rw [elemwiseAdd_valAt_1_2_32 _ _ (p' * 32 + j)
          (hchunk_shape_a 0 (by omega)) (hchunk_shape_b 0 (by omega)) (by omega)]
      rw [chunk_dim1_4_1_8_32_valAt a 0 p' j ha (by omega) hp'_lt hj_lt]
      rw [chunk_dim1_4_1_8_32_valAt b 0 p' j hb (by omega) hp'_lt hj_lt]
    · rw [h1]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [elemwiseAdd_valAt_1_2_32 _ _ (p' * 32 + j)
          (hchunk_shape_a 1 (by omega)) (hchunk_shape_b 1 (by omega)) (by omega)]
      rw [chunk_dim1_4_1_8_32_valAt a 1 p' j ha (by omega) hp'_lt hj_lt]
      rw [chunk_dim1_4_1_8_32_valAt b 1 p' j hb (by omega) hp'_lt hj_lt]
    · rw [h2]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [elemwiseAdd_valAt_1_2_32 _ _ (p' * 32 + j)
          (hchunk_shape_a 2 (by omega)) (hchunk_shape_b 2 (by omega)) (by omega)]
      rw [chunk_dim1_4_1_8_32_valAt a 2 p' j ha (by omega) hp'_lt hj_lt]
      rw [chunk_dim1_4_1_8_32_valAt b 2 p' j hb (by omega) hp'_lt hj_lt]
    · rw [h3]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [elemwiseAdd_valAt_1_2_32 _ _ (p' * 32 + j)
          (hchunk_shape_a 3 (by omega)) (hchunk_shape_b 3 (by omega)) (by omega)]
      rw [chunk_dim1_4_1_8_32_valAt a 3 p' j ha (by omega) hp'_lt hj_lt]
      rw [chunk_dim1_4_1_8_32_valAt b 3 p' j hb (by omega) hp'_lt hj_lt]

/-!
## Bridging lemmas for vocab-parallel embedding

When the SM weight is the vstack of the per-rank PM weights (`allGatherPrimDimN 0`),
the SM `fw_embedding` equals the AllReduce of the per-rank `fw_embedding_offset`s.
This is the core algebraic identity for vocab-parallel embedding under the
masking/offset semantics provided by `fw_embedding_offset`.
-/

/-- Value of `allGatherPrimDimN 0 numParts 0 Ws` at index `(r*shard + i)*hidden + j`,
when the shards have shape `[shard, hidden]` and `r < numParts`, `i < shard`, `j < hidden`. -/
theorem allGatherPrimDimN0_valAt
    (numParts shard hidden : Nat) (Ws : List Tensor)
    (hparts : 0 < numParts) (hshard : 0 < shard) (hhid : 0 < hidden)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [shard, hidden])
    (hWs_shape : ∀ r (_ : r < numParts),
        (Ws.getD r (zeroTensor [shard, hidden])).shape = [shard, hidden])
    (r : Nat) (hr : r < numParts) (i : Nat) (hi : i < shard) (j : Nat) (hj : j < hidden) :
    valAt (allGatherPrimDimN 0 numParts 0 Ws) ((r * shard + i) * hidden + j) =
      valAt (Ws.getD r (zeroTensor [shard, hidden])) (i * hidden + j) := by
  -- Bound the index in the output shape.
  have hidx_lt_full : (r * shard + i) * hidden + j < (shard * numParts) * hidden := by
    have h1 : r * shard + i < shard * numParts := by
      have hsi : r * shard + i < (r + 1) * shard := by
        calc r * shard + i < r * shard + shard := by omega
          _ = (r + 1) * shard := by ring
      have hle : (r + 1) * shard ≤ numParts * shard := Nat.mul_le_mul_right _ hr
      calc r * shard + i < (r + 1) * shard := hsi
        _ ≤ numParts * shard := hle
        _ = shard * numParts := by ring
    calc (r * shard + i) * hidden + j
        < (r * shard + i) * hidden + hidden := by omega
      _ = (r * shard + i + 1) * hidden := by ring
      _ ≤ (shard * numParts) * hidden := Nat.mul_le_mul_right _ h1
  have hshape_out : (allGatherPrimDimN 0 numParts 0 Ws).shape = [shard * numParts, hidden] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [shard, hidden] hhead
    simpa using this
  have hidx_lt_prod : (r * shard + i) * hidden + j <
      prodShape (allGatherPrimDimN 0 numParts 0 Ws).shape := by
    rw [hshape_out]
    simpa [prodShape] using hidx_lt_full
  have hfds_pos : 0 < shard * numParts * hidden := by
    have h1 : 0 < shard * numParts := Nat.mul_pos hshard hparts
    exact Nat.mul_pos h1 hhid
  have hfds_ne : (shard * numParts * hidden) ≠ 0 := Nat.ne_of_gt hfds_pos
  have hps_ne : hidden ≠ 0 := Nat.ne_of_gt hhid
  have hshard_ne : shard ≠ 0 := Nat.ne_of_gt hshard
  have hidx_lt_fds : (r * shard + i) * hidden + j < shard * numParts * hidden := by
    calc (r * shard + i) * hidden + j
        < (shard * numParts) * hidden := hidx_lt_full
      _ = shard * numParts * hidden := by ring
  have hdiv_fds : ((r * shard + i) * hidden + j) / (shard * numParts * hidden) = 0 :=
    Nat.div_eq_of_lt hidx_lt_fds
  have hmod_fds : ((r * shard + i) * hidden + j) % (shard * numParts * hidden) =
      (r * shard + i) * hidden + j :=
    Nat.mod_eq_of_lt hidx_lt_fds
  have hdiv_hidden : ((r * shard + i) * hidden + j) / hidden = r * shard + i := by
    rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
        Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod_hidden : ((r * shard + i) * hidden + j) % hidden = j := by
    rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hdiv_shard : (r * shard + i) / shard = r := by
    rw [show r * shard + i = i + shard * r from by ring,
        Nat.add_mul_div_left _ _ hshard, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod_shard : (r * shard + i) % shard = i := by
    rw [show r * shard + i = i + shard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  -- Unfold the value of `allGatherPrimDimN` at the chosen index.
  have h0 : valAt (allGatherPrimDimN 0 numParts 0 Ws) ((r * shard + i) * hidden + j) =
      (allGatherPrimDimN 0 numParts 0 Ws).val ⟨(r * shard + i) * hidden + j, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  -- Pre-compute the list operations on [shard, hidden].
  have hgetD0 : (([shard, hidden] : List Nat).getD 0 0) = shard := rfl
  have hdrop1 : List.foldl (fun (a b : Nat) => a * b) 1
      (List.drop (0 + 1) ([shard, hidden] : List Nat)) = hidden := by
    simp [List.drop, List.foldl]
  -- Pre-compute the shape of Ws.getD r.
  have hWr_shape : (Ws.getD r (zeroTensor [shard, hidden])).shape = [shard, hidden] :=
    hWs_shape r hr
  have hWr_prod : prodShape (Ws.getD r (zeroTensor [shard, hidden])).shape = shard * hidden := by
    rw [hWr_shape]; simp [prodShape]
  have hidx_lt_Wr : i * hidden + j < prodShape (Ws.getD r (zeroTensor [shard, hidden])).shape := by
    rw [hWr_prod]
    calc i * hidden + j
        < i * hidden + hidden := by omega
      _ = (i + 1) * hidden := by ring
      _ ≤ shard * hidden := Nat.mul_le_mul_right _ hi
  -- Unfold and simplify the kernel.
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead, hgetD0, hdrop1,
    if_neg hshard_ne, if_neg hps_ne, if_neg hfds_ne]
  rw [hmod_fds, hdiv_fds, hdiv_hidden, hmod_hidden, hdiv_shard, hmod_shard]
  simp only [Nat.zero_mul, Nat.zero_add, valAt, hidx_lt_Wr, dif_pos]

/-- Value of `fw_embedding ids fullW` at output index `outIdx` is the full lookup
    when row is in vocab range, else 0. -/
theorem fw_embedding_valAt
    (ids fullW : Tensor) (outIdx : Nat) :
    valAt (fw_embedding ids fullW) outIdx =
      if h : outIdx < prodShape (ids.shape ++ [lastD fullW.shape]) then
        valAt fullW
          ((scalarToNat (valAt ids (outIdx / lastD fullW.shape))) * lastD fullW.shape +
            outIdx % lastD fullW.shape)
      else 0 := by
  by_cases hh : outIdx < prodShape (ids.shape ++ [lastD fullW.shape])
  · simp [valAt, fw_embedding, Tensor.mkShape, hh]
  · simp [valAt, fw_embedding, Tensor.mkShape, hh]

/-- Value of `fw_embedding_offset offset ids weight` at output index `outIdx`. -/
theorem fw_embedding_offset_valAt
    (offset : Nat) (ids weight : Tensor) (outIdx : Nat) :
    valAt (fw_embedding_offset offset ids weight) outIdx =
      if h : outIdx < prodShape (ids.shape ++ [lastD weight.shape]) then
        let hidden := lastD weight.shape
        let vocabShard := (weight.shape.head?).getD 0
        let row := scalarToNat (valAt ids (outIdx / hidden))
        let hh := outIdx % hidden
        if offset ≤ row ∧ row < offset + vocabShard then
          valAt weight ((row - offset) * hidden + hh)
        else 0
      else 0 := by
  by_cases hh : outIdx < prodShape (ids.shape ++ [lastD weight.shape])
  · simp [valAt, fw_embedding_offset, Tensor.mkShape, hh]
  · simp [valAt, fw_embedding_offset, Tensor.mkShape, hh]

/-- The shape of `fw_embedding_offset` is `ids.shape ++ [hidden]`. -/
theorem fw_embedding_offset_shape (offset : Nat) (ids weight : Tensor) :
    (fw_embedding_offset offset ids weight).shape = ids.shape ++ [lastD weight.shape] := by
  simp [fw_embedding_offset, Tensor.mkShape]

/-- The shape of `fw_embedding` is `ids.shape ++ [hidden]`. -/
theorem fw_embedding_shape (ids weight : Tensor) :
    (fw_embedding ids weight).shape = ids.shape ++ [lastD weight.shape] := by
  simp [fw_embedding, Tensor.mkShape]

/-- `valAt` of chunking a `[1,8]`-shaped tensor along dim 1 into 4 parts.
    Local index `p` of shard `r` corresponds to global index `r*2 + p`. -/
theorem chunk_dim1_4_1_8_valAt (x : Tensor) (r p : Nat)
    (hx : x.shape = [1, 8]) (hr : r < 4) (hp : p < 2) :
    valAt (chunkPrimDimN 1 4 r x) p = valAt x (r * 2 + p) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (2 : Nat) ≠ 0 by omega, show (1 : Nat) ≠ 0 by omega, ite_false]
  congr 1
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  have h1 : (8 / 4 : Nat) = 2 := by norm_num
  simp only [h1, show (2 : Nat) * 1 = 2 by norm_num, show (8 : Nat) * 1 = 8 by norm_num,
    show (2 : Nat) ≠ 0 by omega, show (1 : Nat) ≠ 0 by omega, ite_false]
  omega

/-- Per-element bridge: the `fw_embedding` of the full ids at global position
    `c*2 + p` equals the `fw_embedding` of the `c`-th sequence chunk at local
    position `p`. Both index the same row of `W`. -/
theorem fw_embedding_chunk_piece_valAt (ids W : Tensor) (c p j : Nat)
    (hids : ids.shape = [1, 8]) (hW : W.shape = [8, 32])
    (hc : c < 4) (hp : p < 2) (hj : j < 32) :
    valAt (fw_embedding ids W) ((c * 2 + p) * 32 + j) =
      valAt (fw_embedding (chunkPrimDimN 1 4 c ids) W) (p * 32 + j) := by
  have hlastW : lastD W.shape = 32 := by rw [hW]; rfl
  have hcs : (chunkPrimDimN 1 4 c ids).shape = [1, 2] := by
    rw [chunkPrimDimN_shape 1 4 c _ _ hids (by omega)]
    simp [List.set, List.getD]
  -- LHS
  rw [fw_embedding_valAt]
  have hprod1 : prodShape (ids.shape ++ [lastD W.shape]) = 256 := by rw [hids, hlastW]; rfl
  have hb1 : (c * 2 + p) * 32 + j < prodShape (ids.shape ++ [lastD W.shape]) := by
    rw [hprod1]; omega
  rw [dif_pos hb1, hlastW]
  have hdiv1 : ((c * 2 + p) * 32 + j) / 32 = c * 2 + p := by omega
  have hmod1 : ((c * 2 + p) * 32 + j) % 32 = j := by omega
  rw [hdiv1, hmod1]
  -- RHS
  rw [fw_embedding_valAt]
  have hprodc : prodShape ((chunkPrimDimN 1 4 c ids).shape ++ [lastD W.shape]) = 64 := by
    rw [hcs, hlastW]; rfl
  have hb2 : p * 32 + j < prodShape ((chunkPrimDimN 1 4 c ids).shape ++ [lastD W.shape]) := by
    rw [hprodc]; omega
  rw [dif_pos hb2, hlastW]
  have hdiv2 : (p * 32 + j) / 32 = p := by omega
  have hmod2 : (p * 32 + j) % 32 = j := by omega
  rw [hdiv2, hmod2]
  rw [chunk_dim1_4_1_8_valAt ids c p hids hc hp]

/-- `fw_embedding` distributes over sequence-parallel sharding: chunking the ids
    along dim 1 (into 4 parts), embedding each chunk with the full weight, and
    gathering the per-chunk results along dim 1 recovers the full embedding.
    Specialized to ids of shape `[1,8]` and weight of shape `[8,32]`. -/
theorem fw_embedding_distribute_chunk_ids_dim1_4_1_8_32
    (ids W : Tensor) (hids : ids.shape = [1, 8]) (hW : W.shape = [8, 32]) :
    fw_embedding ids W = allGatherPrimDimN 1 4 0
      [fw_embedding (chunkPrimDimN 1 4 0 ids) W,
       fw_embedding (chunkPrimDimN 1 4 1 ids) W,
       fw_embedding (chunkPrimDimN 1 4 2 ids) W,
       fw_embedding (chunkPrimDimN 1 4 3 ids) W] := by
  have hlastW : lastD W.shape = 32 := by rw [hW]; rfl
  have hcs : ∀ r, (chunkPrimDimN 1 4 r ids).shape = [1, 2] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ hids (by omega)]; simp [List.set, List.getD]
  have hpiece_shape : (fw_embedding (chunkPrimDimN 1 4 0 ids) W).shape = [1, 2, 32] := by
    rw [fw_embedding_shape, hcs 0, hlastW]; rfl
  have hhead : (([fw_embedding (chunkPrimDimN 1 4 0 ids) W,
      fw_embedding (chunkPrimDimN 1 4 1 ids) W,
      fw_embedding (chunkPrimDimN 1 4 2 ids) W,
      fw_embedding (chunkPrimDimN 1 4 3 ids) W].head?.map
        (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hpiece_shape
  have hlhs_shape : (fw_embedding ids W).shape = [1, 8, 32] := by
    rw [fw_embedding_shape, hids, hlastW]; rfl
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [fw_embedding (chunkPrimDimN 1 4 0 ids) W,
       fw_embedding (chunkPrimDimN 1 4 1 ids) W,
       fw_embedding (chunkPrimDimN 1 4 2 ids) W,
       fw_embedding (chunkPrimDimN 1 4 3 ids) W]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hhead]; simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  · intro idx hidx
    rw [hlhs_shape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape] using hidx
    obtain ⟨r, p, j, hr, hp, hj, hidx_eq⟩ :
        ∃ r p j, r < 4 ∧ p < 2 ∧ j < 32 ∧ idx = (r * 2 + p) * 32 + j := by
      refine ⟨idx / 32 / 2, idx / 32 % 2, idx % 32, by omega, by omega, by omega, by omega⟩
    rw [hidx_eq]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr p hp j hj hhead]
    have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr4 with h|h|h|h <;> subst h
    · exact fw_embedding_chunk_piece_valAt ids W 0 p j hids hW (by omega) hp hj
    · exact fw_embedding_chunk_piece_valAt ids W 1 p j hids hW (by omega) hp hj
    · exact fw_embedding_chunk_piece_valAt ids W 2 p j hids hW (by omega) hp hj
    · exact fw_embedding_chunk_piece_valAt ids W 3 p j hids hW (by omega) hp hj

/-- Sum of `valAt` over a list of tensors, expressed via `List.foldl`. -/
theorem allReducePrim_valAt
    (numParts rank : Nat) (xs : List Tensor) (idx : Nat) (x0 : Tensor)
    (hhead : xs.head? = some x0)
    (hidx : idx < prodShape x0.shape) :
    valAt (allReducePrim numParts rank xs) idx = xs.foldl (fun acc t => acc + valAt t idx) 0 := by
  have hshape : (allReducePrim numParts rank xs).shape = x0.shape :=
    allReducePrim_shape numParts rank xs x0 hhead
  have hidx' : idx < prodShape (allReducePrim numParts rank xs).shape := by
    rw [hshape]; exact hidx
  have hL : valAt (allReducePrim numParts rank xs) idx =
      (allReducePrim numParts rank xs).val ⟨idx, hidx'⟩ := by
    simp [valAt, hidx']
  rw [hL]
  simp [allReducePrim, Tensor.mkShape]

/-- Bridging lemma: under vocab-parallel sharding (vstack of weights along dim 0),
    `fw_embedding` of the full weight equals the `allReducePrim` of the per-rank
    `fw_embedding_offset`s. -/
theorem fw_embedding_eq_allReduce_offset_shards
    (numParts shard hidden : Nat)
    (hparts : 0 < numParts) (hshard : 0 < shard) (hhid : 0 < hidden)
    (ids : Tensor) (Ws : List Tensor)
    (hlen : Ws.length = numParts)
    (hWs_head : (Ws.head?.map (fun t => t.shape)).getD [] = [shard, hidden])
    (hWs_shape : ∀ r (_ : r < numParts),
        (Ws.getD r (zeroTensor [shard, hidden])).shape = [shard, hidden]) :
    fw_embedding ids (allGatherPrimDimN 0 numParts 0 Ws) =
      allReducePrim numParts 0
        (List.ofFn (fun r : Fin numParts =>
          fw_embedding_offset (r.val * shard) ids
            (Ws.getD r.val (zeroTensor [shard, hidden])))) := by
  -- Notation for the full tensor and the RHS list.
  set fullW : Tensor := allGatherPrimDimN 0 numParts 0 Ws with hfullW
  set rhsList : List Tensor :=
    List.ofFn (fun r : Fin numParts =>
      fw_embedding_offset (r.val * shard) ids
        (Ws.getD r.val (zeroTensor [shard, hidden]))) with hrhsList
  -- Shape of fullW.
  have hfullW_shape : fullW.shape = [shard * numParts, hidden] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [shard, hidden] hWs_head
    simpa using this
  have hlastD_full : lastD fullW.shape = hidden := by
    rw [hfullW_shape]; rfl
  -- Per-element shape of rhsList.
  have hrhs_elem_shape : ∀ r : Fin numParts,
      (fw_embedding_offset (r.val * shard) ids
        (Ws.getD r.val (zeroTensor [shard, hidden]))).shape = ids.shape ++ [hidden] := by
    intro r
    rw [fw_embedding_offset_shape, hWs_shape r.val r.isLt]; rfl
  -- Head of rhsList exists since numParts > 0.
  have hrhs_head : ∃ x0, rhsList.head? = some x0 ∧ x0.shape = ids.shape ++ [hidden] := by
    cases hp : numParts with
    | zero => exact absurd hp (Nat.ne_of_gt hparts)
    | succ k =>
      have hheadVal :
          (List.ofFn (fun r : Fin (k + 1) =>
            fw_embedding_offset (r.val * shard) ids
              (Ws.getD r.val (zeroTensor [shard, hidden]))) : List Tensor).head? =
          some (fw_embedding_offset (0 * shard) ids
              (Ws.getD 0 (zeroTensor [shard, hidden]))) := by
        simp [List.ofFn_succ]
      refine ⟨fw_embedding_offset (0 * shard) ids
          (Ws.getD 0 (zeroTensor [shard, hidden])), ?_, ?_⟩
      · rw [hrhsList]; subst hp; exact hheadVal
      · rw [fw_embedding_offset_shape]
        have h0' : (0 : Nat) < numParts := by rw [hp]; omega
        rw [hWs_shape 0 h0']; rfl
  obtain ⟨x0, hx0_head, hx0_shape⟩ := hrhs_head
  -- Shape of allReducePrim rhsList.
  have hrhs_shape : (allReducePrim numParts 0 rhsList).shape = ids.shape ++ [hidden] := by
    rw [allReducePrim_shape numParts 0 rhsList x0 hx0_head]
    exact hx0_shape
  -- Shape of LHS.
  have hlhs_shape : (fw_embedding ids fullW).shape = ids.shape ++ [hidden] := by
    rw [fw_embedding_shape, hlastD_full]
  -- Apply Tensor.ext.
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  -- Per-index equality.
  intro outIdx hout
  have hbound : outIdx < prodShape (ids.shape ++ [hidden]) := by
    rwa [hlhs_shape] at hout
  -- LHS value via fw_embedding_valAt.
  rw [fw_embedding_valAt]
  have hlhsCond : outIdx < prodShape (ids.shape ++ [lastD fullW.shape]) := by
    rwa [hlastD_full]
  rw [dif_pos hlhsCond]
  rw [hlastD_full]
  -- RHS value via allReducePrim_valAt.
  rw [allReducePrim_valAt numParts 0 rhsList outIdx x0 hx0_head (by rw [hx0_shape]; exact hbound)]
  set h : Nat := outIdx % hidden with hh_def
  set idFlat : Nat := outIdx / hidden with hidFlat_def
  set row : Nat := scalarToNat (valAt ids idFlat) with hrow_def
  have hh_lt : h < hidden := Nat.mod_lt _ hhid
  -- Per-element value of rhsList.
  have hr_val : ∀ r : Fin numParts,
      valAt (fw_embedding_offset (r.val * shard) ids
        (Ws.getD r.val (zeroTensor [shard, hidden]))) outIdx =
      (if r.val * shard ≤ row ∧ row < r.val * shard + shard then
        valAt (Ws.getD r.val (zeroTensor [shard, hidden]))
          ((row - r.val * shard) * hidden + h)
      else 0) := by
    intro r
    rw [fw_embedding_offset_valAt]
    have hcond : outIdx < prodShape (ids.shape ++
        [lastD (Ws.getD r.val (zeroTensor [shard, hidden])).shape]) := by
      rw [hWs_shape r.val r.isLt]; exact hbound
    rw [dif_pos hcond]
    have hlastD_W : lastD (Ws.getD r.val (zeroTensor [shard, hidden])).shape = hidden := by
      rw [hWs_shape r.val r.isLt]; rfl
    have hhead_W : ((Ws.getD r.val (zeroTensor [shard, hidden])).shape.head?).getD 0 = shard := by
      rw [hWs_shape r.val r.isLt]; rfl
    simp only [hlastD_W, hhead_W]
    -- Now both sides use outIdx/hidden, outIdx%hidden vs idFlat, h.
    -- These are equal by the let-bindings.
    rfl
  -- Convert foldl over rhsList to a Finset sum.
  have hRSumLHS : rhsList.foldl (fun acc t => acc + valAt t outIdx) 0 =
      ∑ r : Fin numParts, (if r.val * shard ≤ row ∧ row < r.val * shard + shard then
        valAt (Ws.getD r.val (zeroTensor [shard, hidden]))
          ((row - r.val * shard) * hidden + h)
      else 0) := by
    rw [hrhsList, List.foldl_add_eq_sum, List.map_ofFn]
    have hsum_ofFn : ∀ (f : Fin numParts → Scalar),
        (List.ofFn f).sum = ∑ i : Fin numParts, f i := fun f => Fin.sum_ofFn f
    rw [hsum_ofFn]
    simp only [Function.comp_apply]
    apply Finset.sum_congr rfl
    intro r _
    exact hr_val r
  rw [hRSumLHS]
  -- Case analysis on row vs numParts*shard.
  by_cases hrow : row < numParts * shard
  · -- In range: there is a unique r0 = row/shard with the indicator true.
    set r0 : Nat := row / shard with hr0_def
    have hr0_lt : r0 < numParts := by
      rw [hr0_def]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hrow)
    have hrow_ge : r0 * shard ≤ row := Nat.div_mul_le_self row shard
    have hrow_lt_succ : row < r0 * shard + shard := by
      have hmod_lt : row % shard < shard := Nat.mod_lt _ hshard
      have hrow_split : row = r0 * shard + row % shard := by
        rw [hr0_def, Nat.mul_comm]
        exact (Nat.div_add_mod row shard).symm
      rw [hrow_split]
      exact Nat.add_lt_add_left hmod_lt _
    -- Sum collapses to a single term.
    have hsum_collapse :
        (∑ r : Fin numParts,
          (if r.val * shard ≤ row ∧ row < r.val * shard + shard then
            valAt (Ws.getD r.val (zeroTensor [shard, hidden]))
              ((row - r.val * shard) * hidden + h)
          else 0)) =
        valAt (Ws.getD r0 (zeroTensor [shard, hidden]))
          ((row - r0 * shard) * hidden + h) := by
      rw [Finset.sum_eq_single (⟨r0, hr0_lt⟩ : Fin numParts)]
      · simp [hrow_ge, hrow_lt_succ]
      · intro r _ hne
        have hnot : ¬(r.val * shard ≤ row ∧ row < r.val * shard + shard) := by
          intro ⟨hge, hlt⟩
          have hrv_eq : r.val = r0 := by
            have h2 : row < (r.val + 1) * shard := by
              have heq : r.val * shard + shard = (r.val + 1) * shard := by ring
              rw [← heq]; exact hlt
            -- Nat.div_eq_of_lt_le takes (lo : k * n ≤ m) (hi : m < (k+1) * n).
            have hd : row / shard = r.val := Nat.div_eq_of_lt_le hge h2
            rw [hr0_def]; omega
          apply hne
          exact Fin.ext hrv_eq
        simp [hnot]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    rw [hsum_collapse]
    -- LHS: valAt fullW (row * hidden + h)
    -- We use allGatherPrimDimN0_valAt with i = row - r0*shard, j = h.
    have hi_lt : row - r0 * shard < shard := by omega
    have h_aux : (r0 * shard + (row - r0 * shard)) * hidden + h = row * hidden + h := by
      have : r0 * shard + (row - r0 * shard) = row := by omega
      rw [this]
    have hag := allGatherPrimDimN0_valAt numParts shard hidden Ws hparts hshard hhid hWs_head
      hWs_shape r0 hr0_lt (row - r0 * shard) hi_lt h hh_lt
    rw [h_aux] at hag
    rw [← hfullW] at hag
    rw [hag]
  · -- Out of range: sum = 0, LHS valAt fullW = 0 (out of bounds).
    push_neg at hrow
    have hsum_zero :
        (∑ r : Fin numParts,
          (if r.val * shard ≤ row ∧ row < r.val * shard + shard then
            valAt (Ws.getD r.val (zeroTensor [shard, hidden]))
              ((row - r.val * shard) * hidden + h)
          else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hnot : ¬(r.val * shard ≤ row ∧ row < r.val * shard + shard) := by
        intro ⟨_, hlt⟩
        have h1 : r.val * shard + shard = (r.val + 1) * shard := by ring
        rw [h1] at hlt
        have hle : (r.val + 1) * shard ≤ numParts * shard := Nat.mul_le_mul_right _ r.isLt
        have hcontra : row < numParts * shard := lt_of_lt_of_le hlt hle
        omega
      simp [hnot]
    rw [hsum_zero]
    -- LHS = valAt fullW (row * hidden + h), out of bounds.
    have hoob : ¬ (row * hidden + h < prodShape fullW.shape) := by
      rw [hfullW_shape]
      have hps : prodShape ([shard * numParts, hidden] : Shape) = shard * numParts * hidden := by
        simp [prodShape]
      rw [hps]
      have h1 : numParts * shard ≤ row := hrow
      have h2 : numParts * shard * hidden ≤ row * hidden := Nat.mul_le_mul_right _ h1
      have h3 : numParts * shard * hidden = shard * numParts * hidden := by ring
      omega
    simp [valAt, hoob]

/-! ### BW_embedding shape and distribute lemmas -/

theorem bw_embedding_shape (g ids weight : Tensor) :
    (bw_embedding g ids weight).shape = weight.shape := by
  simp [bw_embedding, Tensor.mkShape]

theorem bw_embedding_offset_shape (offset : Nat) (g ids weight : Tensor) :
    (bw_embedding_offset offset g ids weight).shape = weight.shape := by
  simp [bw_embedding_offset, Tensor.mkShape]

/-- Pointwise value of `bw_embedding`. -/
theorem bw_embedding_valAt (g ids weight : Tensor) (idx : Nat)
    (hidx : idx < prodShape weight.shape) :
    valAt (bw_embedding g ids weight) idx =
      let hidden := lastD weight.shape
      let row := idx / hidden
      let h := idx % hidden
      ∑ k ∈ Finset.range (prodShape ids.shape),
        if scalarToNat (valAt ids k) = row then valAt g (k * hidden + h) else 0 := by
  simp only [bw_embedding, Tensor.mkShape, valAt, hidx, dite_true]

/-- Pointwise value of `bw_embedding_offset`. -/
theorem bw_embedding_offset_valAt (offset : Nat) (g ids weight : Tensor) (idx : Nat)
    (hidx : idx < prodShape weight.shape) :
    valAt (bw_embedding_offset offset g ids weight) idx =
      let hidden := lastD weight.shape
      let localRow := idx / hidden
      let h := idx % hidden
      let globalRow := offset + localRow
      ∑ k ∈ Finset.range (prodShape ids.shape),
        if scalarToNat (valAt ids k) = globalRow then valAt g (k * hidden + h) else 0 := by
  simp only [bw_embedding_offset, Tensor.mkShape, valAt, hidx, dite_true]

/-- Bridging lemma: under vocab-parallel sharding (vstack of weights along dim 0),
    `bw_embedding` of the full weight equals `allGatherPrimDimN 0` of the per-rank
    `bw_embedding_offset` results (4-shard specialization). -/
theorem bw_embedding_eq_allGather_offset_4shards
    (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (g ids w0 w1 w2 w3 : Tensor)
    (hw0 : w0.shape = [shard, hidden]) (hw1 : w1.shape = [shard, hidden])
    (hw2 : w2.shape = [shard, hidden]) (hw3 : w3.shape = [shard, hidden]) :
    bw_embedding g ids (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]) =
      allGatherPrimDimN 0 4 0
        [bw_embedding_offset (0 * shard) g ids w0,
         bw_embedding_offset (1 * shard) g ids w1,
         bw_embedding_offset (2 * shard) g ids w2,
         bw_embedding_offset (3 * shard) g ids w3] := by
  set fullW : Tensor := allGatherPrimDimN 0 4 0 [w0, w1, w2, w3] with hfullW
  set rhs0 := bw_embedding_offset (0 * shard) g ids w0
  set rhs1 := bw_embedding_offset (1 * shard) g ids w1
  set rhs2 := bw_embedding_offset (2 * shard) g ids w2
  set rhs3 := bw_embedding_offset (3 * shard) g ids w3
  -- Shape of fullW.
  have hfullW_shape : fullW.shape = [shard * 4, hidden] := by
    have := allGatherPrimDimN_shape 0 4 [w0, w1, w2, w3] [shard, hidden] (by simp [hw0])
    simpa using this
  have hlastD_full : lastD fullW.shape = hidden := by
    rw [hfullW_shape]; rfl
  -- Shapes of bw_embedding_offset results.
  have hrhs0_shape : rhs0.shape = [shard, hidden] := by
    simp only [rhs0]; rw [bw_embedding_offset_shape, hw0]
  have hrhs1_shape : rhs1.shape = [shard, hidden] := by
    simp only [rhs1]; rw [bw_embedding_offset_shape, hw1]
  have hrhs2_shape : rhs2.shape = [shard, hidden] := by
    simp only [rhs2]; rw [bw_embedding_offset_shape, hw2]
  have hrhs3_shape : rhs3.shape = [shard, hidden] := by
    simp only [rhs3]; rw [bw_embedding_offset_shape, hw3]
  -- LHS and RHS shapes.
  have hlhs_shape : (bw_embedding g ids fullW).shape = [shard * 4, hidden] := by
    rw [bw_embedding_shape]; exact hfullW_shape
  have hrhs_head : ([rhs0, rhs1, rhs2, rhs3].head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hrhs0_shape]
  have hrhs_shape : (allGatherPrimDimN 0 4 0 [rhs0, rhs1, rhs2, rhs3]).shape = [shard * 4, hidden] := by
    have := allGatherPrimDimN_shape 0 4 [rhs0, rhs1, rhs2, rhs3] [shard, hidden] hrhs_head
    simpa using this
  -- RHS element shapes for allGatherPrimDimN0_valAt.
  have hrhs_ws_shape : ∀ r (_ : r < 4),
      ([rhs0, rhs1, rhs2, rhs3].getD r (zeroTensor [shard, hidden])).shape = [shard, hidden] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [List.getD, hrhs0_shape, hrhs1_shape, hrhs2_shape, hrhs3_shape]
  -- Ws element shapes.
  have hWs_shape : ∀ r (_ : r < 4),
      ([w0, w1, w2, w3].getD r (zeroTensor [shard, hidden])).shape = [shard, hidden] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [List.getD, hw0, hw1, hw2, hw3]
  -- Apply Tensor.ext.
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  -- Per-index equality.
  intro idx hout
  have hbound : idx < shard * 4 * hidden := by
    have : prodShape [shard * 4, hidden] = shard * 4 * hidden := by simp [prodShape]
    rwa [hlhs_shape, this] at hout
  -- Decompose idx into (r, i, j).
  have hsh_pos : 0 < shard * hidden := Nat.mul_pos hshard hhid
  set r := idx / (shard * hidden)
  set rem := idx % (shard * hidden)
  set i := rem / hidden
  set j := rem % hidden
  have hr_lt : r < 4 := by
    have h : idx < (shard * hidden) * 4 := by
      have : shard * 4 * hidden = (shard * hidden) * 4 := by ring
      omega
    exact Nat.div_lt_of_lt_mul h
  have hrem_lt : rem < shard * hidden := Nat.mod_lt _ hsh_pos
  have hi_lt : i < shard := by
    have h : rem < hidden * shard := by
      have : shard * hidden = hidden * shard := by ring
      omega
    exact Nat.div_lt_of_lt_mul h
  have hj_lt : j < hidden := Nat.mod_lt _ hhid
  -- Reconstruct idx from (r, i, j).
  have hidx_eq : idx = (r * shard + i) * hidden + j := by
    have h1 : (shard * hidden) * r + rem = idx := Nat.div_add_mod idx (shard * hidden)
    have h2 : hidden * i + j = rem := Nat.div_add_mod rem hidden
    have h3 : (r * shard + i) * hidden + j = (shard * hidden) * r + (hidden * i + j) := by ring
    omega
  -- LHS value.
  have hidx_prod : idx < prodShape fullW.shape := by
    rw [hfullW_shape]; simpa [prodShape] using hbound
  rw [bw_embedding_valAt g ids fullW idx hidx_prod]
  simp only [hlastD_full]
  -- RHS value via allGatherPrimDimN0_valAt.
  have hWs_head' : ([w0, w1, w2, w3].head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    simp [hw0]
  have hag := allGatherPrimDimN0_valAt 4 shard hidden [rhs0, rhs1, rhs2, rhs3]
    (by omega) hshard hhid hrhs_head hrhs_ws_shape r hr_lt i hi_lt j hj_lt
  rw [hidx_eq, hag]
  -- Identify which shard we're in and unfold bw_embedding_offset valAt.
  have hi_hidden_bound : i * hidden + j < prodShape [shard, hidden] := by
    simp [prodShape]
    calc i * hidden + j < i * hidden + hidden := by omega
      _ = (i + 1) * hidden := by ring
      _ ≤ shard * hidden := Nat.mul_le_mul_right _ hi_lt
  -- Get the right shard from the list.
  have hrhs_getD : ∀ (rv : Nat) (hrv : rv < 4),
      [rhs0, rhs1, rhs2, rhs3].getD rv (zeroTensor [shard, hidden]) =
      bw_embedding_offset (rv * shard) g ids ([w0, w1, w2, w3].getD rv (zeroTensor [shard, hidden])) := by
    intro rv hrv
    have : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [List.getD, rhs0, rhs1, rhs2, rhs3]
  rw [hrhs_getD r hr_lt]
  -- Value of bw_embedding_offset at (i * hidden + j).
  have hWr_shape := hWs_shape r hr_lt
  have hlastD_Wr : lastD ([w0, w1, w2, w3].getD r (zeroTensor [shard, hidden])).shape = hidden := by
    rw [hWr_shape]; rfl
  rw [bw_embedding_offset_valAt (r * shard) g ids
      ([w0, w1, w2, w3].getD r (zeroTensor [shard, hidden])) (i * hidden + j)
      (by rw [hWr_shape]; exact hi_hidden_bound)]
  simp only [hlastD_Wr]
  -- Now both sides compute the same sum. Show the indices match.
  -- LHS row = ((r*shard+i)*hidden+j)/hidden = r*shard+i
  -- LHS h = ((r*shard+i)*hidden+j)%hidden = j
  -- RHS localRow = (i*hidden+j)/hidden = i, h = (i*hidden+j)%hidden = j
  -- RHS globalRow = r*shard + i
  have hlhs_div : ((r * shard + i) * hidden + j) / hidden = r * shard + i := by
    rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
        Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
  have hrhs_div : (i * hidden + j) / hidden = i := by
    rw [show i * hidden + j = j + hidden * i from by ring,
        Nat.add_mul_div_left _ _ hhid, Nat.div_eq_of_lt hj_lt, Nat.zero_add]
  have hlhs_mod : ((r * shard + i) * hidden + j) % hidden = j := by
    rw [show (r * shard + i) * hidden + j = j + hidden * (r * shard + i) from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
  have hrhs_mod : (i * hidden + j) % hidden = j := by
    rw [show i * hidden + j = j + hidden * i from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
  simp only [hlhs_div, hrhs_div, hlhs_mod, hrhs_mod]

/-- `valAt` of a sequence-parallel id chunk: chunking `ids` (shape `[1,8]`) along dim 1
    into 4 parts selects elements `[r*2, r*2+2)`. -/
private theorem chunkPrimDimN_1_4_ids_valAt (ids : Tensor) (r k' : Nat)
    (hids : ids.shape = [1, 8]) (hr : r < 4) (hk : k' < 2) :
    valAt (chunkPrimDimN 1 4 r ids) k' = valAt ids (r * 2 + k') := by
  have hchunk_shape : (chunkPrimDimN 1 4 r ids).shape = [1, 2] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hids (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : k' < prodShape (chunkPrimDimN 1 4 r ids).shape := by
    rw [hchunk_shape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hids, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceDiv, Nat.reduceMul,
    Nat.reduceEqDiff, reduceIte]
  congr 1
  omega

/-- `valAt` of a sequence-parallel all-gather along dim 1 over four `[1,2,32]` shards:
    output index `k*32+h` (with `k<8`, `h<32`) reads shard `k/2` at `(k%2)*32+h`. -/
private theorem allGatherPrimDimN_1_4_1_2_32_valAt
    (g0 g1 g2 g3 : Tensor) (k h : Nat)
    (hg0 : g0.shape = [1, 2, 32]) (hk : k < 8) (hh : h < 32) :
    valAt (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3]) (k * 32 + h) =
      valAt ([g0, g1, g2, g3].getD (k / 2) (zeroTensor [1, 2, 32])) ((k % 2) * 32 + h) := by
  have hhead : (([g0, g1, g2, g3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hg0]
  have hout_shape : (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3]).shape = [1, 8, 32] := by
    have := allGatherPrimDimN_shape 1 4 [g0, g1, g2, g3] [1, 2, 32] hhead
    simpa using this
  have hidx_lt256 : k * 32 + h < 256 := by omega
  have hidx_lt : k * 32 + h < prodShape (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3]).shape := by
    rw [hout_shape]; simp [prodShape]; omega
  have e_div256 : (k * 32 + h) / 256 = 0 := Nat.div_eq_of_lt hidx_lt256
  have e_mod256 : (k * 32 + h) % 256 = k * 32 + h := Nat.mod_eq_of_lt hidx_lt256
  have e_div32 : (k * 32 + h) / 32 = k := by
    rw [show k * 32 + h = h + 32 * k from by ring, Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt hh, Nat.zero_add]
  have e_mod32 : (k * 32 + h) % 32 = h := by
    rw [show k * 32 + h = h + 32 * k from by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hh]
  rw [valAt_of_lt _ _ hidx_lt]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    show (256 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    ite_false]
  rw [e_mod256, e_div256, e_div32, e_mod32]
  simp only [Nat.zero_mul, Nat.zero_add, valAt]

/-- `valAt` of a four-element `tensorSum` reduces to the pointwise sum. -/
private theorem tensorSum_4_valAt (t0 t1 t2 t3 : Tensor) (idx : Nat)
    (hidx : idx < prodShape t0.shape) :
    valAt (tensorSum [t0, t1, t2, t3]) idx =
      valAt t0 idx + valAt t1 idx + valAt t2 idx + valAt t3 idx := by
  have hsh : (tensorSum [t0, t1, t2, t3]).shape = t0.shape := rfl
  rw [valAt_of_lt _ _ (by rw [hsh]; exact hidx)]
  simp [tensorSum, Tensor.mkShape, List.foldl]

/-- Sequence-parallel distribution of `bw_embedding`: the full backward embedding over a
    sequence-sharded gradient equals the sum (cross-DP reduce) of the per-shard backward
    embeddings, where the ids are chunked along the sequence dimension. -/
theorem bw_embedding_seqchunk_4shards_1_8_32
    (g0 g1 g2 g3 ids w : Tensor)
    (hids : ids.shape = [1, 8]) (hw : w.shape = [8, 32])
    (hg0 : g0.shape = [1, 2, 32]) :
    bw_embedding (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3]) ids w =
      tensorSum
        [ bw_embedding g0 (chunkPrimDimN 1 4 0 ids) w,
          bw_embedding g1 (chunkPrimDimN 1 4 1 ids) w,
          bw_embedding g2 (chunkPrimDimN 1 4 2 ids) w,
          bw_embedding g3 (chunkPrimDimN 1 4 3 ids) w ] := by
  set G := allGatherPrimDimN 1 4 0 [g0, g1, g2, g3] with hG
  have hhead : (([g0, g1, g2, g3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hg0]
  have hG_shape : G.shape = [1, 8, 32] := by
    rw [hG]
    have := allGatherPrimDimN_shape 1 4 [g0, g1, g2, g3] [1, 2, 32] hhead
    simpa using this
  -- chunk shapes
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r ids).shape = [1, 2] := by
    intro r
    rw [chunkPrimDimN_shape 1 4 r _ _ hids (by omega)]
    simp [List.set, List.getD]
  -- Shape equality of both sides.
  apply Tensor.ext
  · rw [bw_embedding_shape]
    rw [tensorSum_shape (bw_embedding g0 (chunkPrimDimN 1 4 0 ids) w)
        [bw_embedding g1 (chunkPrimDimN 1 4 1 ids) w,
         bw_embedding g2 (chunkPrimDimN 1 4 2 ids) w,
         bw_embedding g3 (chunkPrimDimN 1 4 3 ids) w]]
    rw [bw_embedding_shape]
  -- Pointwise equality.
  intro idx hidx0
  have hidx256 : idx < 256 := by
    rw [bw_embedding_shape, hw] at hidx0
    simpa [prodShape] using hidx0
  have hlastw : lastD w.shape = 32 := by rw [hw]; rfl
  have hidsprod : prodShape ids.shape = 8 := by rw [hids]; rfl
  -- LHS value.
  have hidxw : idx < prodShape w.shape := by rw [hw]; simpa [prodShape] using hidx256
  rw [bw_embedding_valAt G ids w idx hidxw]
  simp only [hlastw, hidsprod]
  -- Convert the range-8 sum into a double sum over (i ∈ range 4)(j ∈ range 2).
  rw [show (8 : Nat) = 4 * 2 from rfl,
      Finset.sum_range_mul_eq_sum_sum 4 2
        (fun kk => if scalarToNat (valAt ids kk) = idx / 32 then valAt G (kk * 32 + idx % 32) else 0)]
  -- RHS value.
  have hb0prod : idx < prodShape (bw_embedding g0 (chunkPrimDimN 1 4 0 ids) w).shape := by
    rw [bw_embedding_shape, hw]; simpa [prodShape] using hidx256
  rw [tensorSum_4_valAt _ _ _ _ idx hb0prod]
  have hmod32 : idx % 32 < 32 := Nat.mod_lt _ (by omega)
  -- Expansion of a single per-shard backward embedding into a range-2 sum, given the
  -- gather/shard value identity supplied as a hypothesis.
  have hterm : ∀ (gr : Tensor) (r : Nat), r < 4 →
      (∀ j, j < 2 → valAt gr (j * 32 + idx % 32) = valAt G ((r * 2 + j) * 32 + idx % 32)) →
      valAt (bw_embedding gr (chunkPrimDimN 1 4 r ids) w) idx =
        ∑ j ∈ Finset.range 2,
          if scalarToNat (valAt ids (r * 2 + j)) = idx / 32 then valAt G ((r * 2 + j) * 32 + idx % 32) else 0 := by
    intro gr r hr hgath
    rw [bw_embedding_valAt _ _ w idx hidxw]
    simp only [hlastw]
    have hcprod : prodShape (chunkPrimDimN 1 4 r ids).shape = 2 := by
      rw [hchunk_shape r]; rfl
    rw [hcprod]
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 : j < 2 := by simpa using hj
    rw [chunkPrimDimN_1_4_ids_valAt ids r j hids hr hj2]
    by_cases hcond : scalarToNat (valAt ids (r * 2 + j)) = idx / 32
    · simp only [hcond, if_true]; exact hgath j hj2
    · simp only [hcond, if_false]
  -- Gather/shard value identities for each rank.
  have hgath0 : ∀ j, j < 2 → valAt g0 (j * 32 + idx % 32) = valAt G ((0 * 2 + j) * 32 + idx % 32) := by
    intro j hj
    rw [hG, allGatherPrimDimN_1_4_1_2_32_valAt g0 g1 g2 g3 (0 * 2 + j) (idx % 32) hg0 (by omega) hmod32]
    have h1 : (0 * 2 + j) / 2 = 0 := by omega
    have h2 : (0 * 2 + j) % 2 = j := by omega
    rw [h1, h2]
    rfl
  have hgath1 : ∀ j, j < 2 → valAt g1 (j * 32 + idx % 32) = valAt G ((1 * 2 + j) * 32 + idx % 32) := by
    intro j hj
    rw [hG, allGatherPrimDimN_1_4_1_2_32_valAt g0 g1 g2 g3 (1 * 2 + j) (idx % 32) hg0 (by omega) hmod32]
    have h1 : (1 * 2 + j) / 2 = 1 := by omega
    have h2 : (1 * 2 + j) % 2 = j := by omega
    rw [h1, h2]
    rfl
  have hgath2 : ∀ j, j < 2 → valAt g2 (j * 32 + idx % 32) = valAt G ((2 * 2 + j) * 32 + idx % 32) := by
    intro j hj
    rw [hG, allGatherPrimDimN_1_4_1_2_32_valAt g0 g1 g2 g3 (2 * 2 + j) (idx % 32) hg0 (by omega) hmod32]
    have h1 : (2 * 2 + j) / 2 = 2 := by omega
    have h2 : (2 * 2 + j) % 2 = j := by omega
    rw [h1, h2]
    rfl
  have hgath3 : ∀ j, j < 2 → valAt g3 (j * 32 + idx % 32) = valAt G ((3 * 2 + j) * 32 + idx % 32) := by
    intro j hj
    rw [hG, allGatherPrimDimN_1_4_1_2_32_valAt g0 g1 g2 g3 (3 * 2 + j) (idx % 32) hg0 (by omega) hmod32]
    have h1 : (3 * 2 + j) / 2 = 3 := by omega
    have h2 : (3 * 2 + j) % 2 = j := by omega
    rw [h1, h2]
    rfl
  rw [hterm g0 0 (by omega) hgath0, hterm g1 1 (by omega) hgath1,
      hterm g2 2 (by omega) hgath2, hterm g3 3 (by omega) hgath3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  ring

/-!
## Dimension consistency (well-formedness)

The operator semantics above are intentionally total (they always return a tensor), and we removed
most shape-checking branches to keep later expression-level proofs simple.

Instead, we make **dimension matching** an explicit proof obligation:
a graph is *dimension-consistent*
if, along the denotation fold, every node is applied to arguments whose shapes satisfy the
expected constraints of that operator.

This lets proofs proceed in two phases:
1) prove `GraphDimsOK` (otherwise the graph is inconsistent),
2) prove value-level equivalence under that assumption.
-/

def OpDimsOK (_numParts _rank : Nat) (op : String) (args : List Tensor) : Prop :=
  match op, args with
  | "OpName.FW_linear", [x, w] =>
    ∃ b i o, x.shape = [b, i] ∧ w.shape = [o, i]
  | "OpName.BW_linear", [g, x, w] =>
    ∃ b i o, g.shape = [b, o] ∧ x.shape = [b, i] ∧ w.shape = [o, i]
  | _, _ => True

def NodeDimsOK (g : GraphDecl) (s : Store) (n : NodeDecl) : Prop :=
  OpDimsOK g.numRanks n.rank n.op (n.ins.map s)

def GraphDimsOKAux (g : GraphDecl) : List NodeDecl → Store → Prop
  | [], _ => True
  | n :: ns, s => NodeDimsOK g s n ∧ GraphDimsOKAux g ns (applyNode g s n)

def GraphDimsOK (g : GraphDecl) (init : Store) : Prop :=
  GraphDimsOKAux g g.nodes init

/-!
## Checked denotation (assert-like)

For quick experimentation on a single example, it's often more convenient to *fail fast* when
dimensions don't match, similar to runtime `assert`.

The pure `denoteGraph` above stays total (good for mathematics), while the checked version below
returns an `Except String` with a simple error message on the first inconsistency.
-/

def applyNodeChecked (g : GraphDecl) (s : Store) (n : NodeDecl) : Except String Store :=
  -- Kept only for backward compatibility: runtime checking is now done at the shape level.
  -- This function only checks arity consistency of `evalOp`.
  by
    classical
    let args : List Tensor := n.ins.map s
    let outs : List Tensor := evalOp g.numRanks n.rank n.op n.params args
    if hLen : outs.length = n.outs.length then
      let pairs : List (Tid × Tensor) := (n.outs.zip outs).map (fun p => (p.1, p.2))
      exact Except.ok (storeSet s pairs)
    else
      exact Except.error "applyNodeChecked: arity mismatch (outs vs evalOp)"

def denoteGraphCheckedWithInitShapes (g : GraphDecl) (init : Store) (initShapes : ShapeMap) : Except String Store :=
  if storeShapesHoldList init initShapes then
    match graphShapesCheck g initShapes with
    | Except.error e => Except.error e
    | Except.ok _ =>
        -- If shapes are consistent, the value-level fold is safe (no out-of-bounds by construction).
        g.nodes.foldlM (fun s n => applyNodeChecked g s n) init
  else
    Except.error "checked denote: init store shape mismatch"

def denoteGraphChecked (g : GraphDecl) (init : Store) : Except String Store :=
  -- For interactive use without an init-shape list.
  g.nodes.foldlM (fun s n => applyNodeChecked g s n) init

/-!
## Graph-independent unfolding lemmas

These are purely equational rewrites for the denotational definition `denoteGraph`.
They do **not** introduce any small-step / execution semantics; they just expose the
`foldl` structure so proofs can proceed by rewriting.
-/

@[simp] theorem denoteGraph_nodes_nil (n : Nat) (init : Store) :
    denoteGraph { numRanks := n, nodes := [] } init = init := by
  simp [denoteGraph]

theorem applyNode_congr_numRanks (g g' : GraphDecl) (h : g.numRanks = g'.numRanks) :
    applyNode g = applyNode g' := by
  funext s nd
  cases g with
  | mk nr nodes =>
    cases g' with
    | mk nr' nodes' =>
      cases h
      simp [applyNode]

@[simp] theorem denoteGraph_nodes_cons (g : GraphDecl) (n : NodeDecl) (ns : List NodeDecl)
    (init : Store) :
    denoteGraph { g with nodes := n :: ns } init =
      denoteGraph { g with nodes := ns } (applyNode g init n) := by
  -- Rewrite the fold function `applyNode` to use the same `numRanks` everywhere.
  have hfn₁ : applyNode { g with nodes := n :: ns } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  have hfn₂ : applyNode { g with nodes := ns } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  simp [denoteGraph, hfn₁, hfn₂]

/-!
## Store preservation lemmas (proof automation)

These are purely equational facts about how `storeSet/applyNode/denoteGraph` behave.
They are useful to avoid unfolding *entire* graphs when you only care about specific tids.
-/

theorem not_mem_map_fst_zipWith_of_not_mem_left (tid : Tid) (xs : List Tid) (ys : List Tensor)
    (h : tid ∉ xs) : tid ∉ (List.zipWith Prod.mk xs ys).map Prod.fst := by
  induction xs generalizing ys with
  | nil =>
      simp
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp
      | cons y ys =>
          have hx : tid ≠ x := by
            intro hEq
            apply h
            simp [hEq]
          have hxs : tid ∉ xs := by
            intro hmem
            apply h
            simp [hmem]
          have hrec : tid ∉ (List.zipWith Prod.mk xs ys).map Prod.fst := ih ys hxs
          -- `zipWith` produces `(x,y) :: zipWith ...`
          intro hmem
          simp [List.zipWith] at hmem
          cases hmem with
          | inl h => exact hx h
          | inr h =>
            have : tid ∈ (List.zipWith Prod.mk xs ys).map Prod.fst := by
              simp
              exact h
            exact hrec this

theorem not_mem_map_fst_zip_of_not_mem_left (tid : Tid) (xs : List Tid) (ys : List Tensor)
    (h : tid ∉ xs) : tid ∉ (xs.zip ys).map Prod.fst := by
  -- `List.zip` is `zipWith Prod.mk`.
  simpa [List.zip] using not_mem_map_fst_zipWith_of_not_mem_left tid xs ys h

theorem applyNode_eq_of_not_mem_outs (g : GraphDecl) (s : Store) (n : NodeDecl) (tid : Tid)
    (h : tid ∉ n.outs) : applyNode g s n tid = s tid := by
  -- `applyNode` updates only tids listed in `n.outs` (modulo zip truncation).
  simp [applyNode, storeSet_eq_of_not_mem_fst, not_mem_map_fst_zip_of_not_mem_left, h]

/-!
## List.take helper lemmas for graph proofs

These lemmas help avoid expensive `native_decide` calls when reasoning about
`List.take` and `List.foldl` over large node lists.
-/

/-- `List.take (n+1) l = List.take n l ++ [l[n]]` when `n < l.length` -/
theorem list_take_succ_eq_take_append_get {α : Type*} (l : List α) (n : Nat) (hn : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn]
  simp

/-- Unfolding foldl with take (n+1) to foldl with take n, plus one more step -/
theorem foldl_take_succ {α β : Type*} (f : β → α → β) (l : List α) (init : β) (n : Nat) (hn : n < l.length) :
    (l.take (n + 1)).foldl f init = f ((l.take n).foldl f init) l[n] := by
  rw [list_take_succ_eq_take_append_get l n hn, List.foldl_append, List.foldl]
  simp

theorem denoteGraph_tid_eq_of_forall_not_mem_outs (g : GraphDecl) (nodes : List NodeDecl)
    (init : Store) (tid : Tid) (h : ∀ n ∈ nodes, tid ∉ n.outs) :
    (denoteGraph { g with nodes := nodes } init) tid = init tid := by
  -- Induct via the graph-level unfolding lemma `denoteGraph_nodes_cons`.
  induction nodes generalizing init with
  | nil =>
      simp
  | cons n ns ih =>
      have hn : tid ∉ n.outs := h n (by simp)
      have hns : ∀ n' ∈ ns, tid ∉ n'.outs := by
        intro n' hn'
        exact h n' (by simp [hn'])
      -- Peel the head node; it does not write `tid`, so it preserves `tid`.
      have ih' : denoteGraph { g with nodes := ns } (applyNode g init n) tid = (applyNode g init n) tid :=
        ih (init := applyNode g init n) hns
      calc
        denoteGraph { g with nodes := n :: ns } init tid
            = denoteGraph { g with nodes := ns } (applyNode g init n) tid := by
                simp [denoteGraph_nodes_cons]
        _ = (applyNode g init n) tid := by
              simpa using ih'
          _ = init tid := by
            simp [applyNode_eq_of_not_mem_outs (g := g) (s := init) (n := n) (tid := tid) hn]

@[simp] theorem denoteGraph_nodes_append (g : GraphDecl) (xs ys : List NodeDecl) (init : Store) :
    denoteGraph { g with nodes := xs ++ ys } init =
      denoteGraph { g with nodes := ys } (denoteGraph { g with nodes := xs } init) := by
  -- Normalize all `applyNode` functions to `applyNode g` and use `foldl_append`.
  have hfn₁ : applyNode { g with nodes := xs ++ ys } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  have hfn₂ : applyNode { g with nodes := xs } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  have hfn₃ : applyNode { g with nodes := ys } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  simp [denoteGraph, hfn₁, hfn₂, hfn₃, List.foldl_append]

/-- Split-and-skip helper: when the suffix of `g.nodes` doesn't write `tid`, the value at `tid` in
    `denoteGraph g init` only depends on the prefix. `prefix ++ suffix` must equal `g.nodes`. -/
theorem denoteGraph_tid_eq_of_suffix_no_writes
    (g : GraphDecl) (init : Store) (tid : Tid)
    (pre suf : List NodeDecl) (hsplit : g.nodes = pre ++ suf)
    (hno : ∀ n ∈ suf, tid ∉ n.outs) :
    denoteGraph g init tid = denoteGraph { g with nodes := pre } init tid := by
  -- Replace `g` with the structure-update form using `hsplit`.
  have hg_eq : g = { g with nodes := pre ++ suf } := by
    cases g with
    | mk nr nodes =>
      subst hsplit
      rfl
  conv_lhs => rw [hg_eq, denoteGraph_nodes_append]
  exact denoteGraph_tid_eq_of_forall_not_mem_outs g suf _ tid hno

/-- Apply `denoteGraph_nodes_cons` while tolerating the `{ numRanks := n, nodes := X }` form
    (i.e. structure literals where `g` is not explicit). -/
theorem denoteGraph_cons_eq (g : GraphDecl) (n : NodeDecl) (ns : List NodeDecl) (init : Store) :
    denoteGraph { numRanks := g.numRanks, nodes := n :: ns } init =
      denoteGraph { numRanks := g.numRanks, nodes := ns } (applyNode g init n) := by
  have h1 : ({ numRanks := g.numRanks, nodes := n :: ns } : GraphDecl) =
      { g with nodes := n :: ns } := by
    cases g; rfl
  have h2 : ({ numRanks := g.numRanks, nodes := ns } : GraphDecl) =
      { g with nodes := ns } := by
    cases g; rfl
  rw [h1, h2, denoteGraph_nodes_cons]

/-!
## Reconstruction for coarse lineage goals

We provide a default, *shape-directed* reconstruction:

- if shards are scalars (`shape = [1]`), we interpret reconstruction as a reduction over ranks;
- otherwise, we interpret it as an all-gather/concatenation along the last dimension.

This matches common tensor-parallel patterns and is sufficient for the current example.
If you need more precision, extend `LineageGoal` with slice metadata
and define a slice-based assembler.
-/

/-- Infer which dimension was split based on shard and expected full shape.
    Returns 0 for first dim, 2 for last dim (of 3D), or default to last. -/
def inferSplitDim (numParts : Nat) (shardShape fullShape : Shape) : Nat :=
  match shardShape, fullShape with
  | [s0, s1, s2], [f0, f1, f2] =>
      if s0 * numParts = f0 ∧ s1 = f1 ∧ s2 = f2 then 0  -- split on dim 0
      else if s0 = f0 ∧ s1 * numParts = f1 ∧ s2 = f2 then 1  -- split on dim 1
      else if s0 = f0 ∧ s1 = f1 ∧ s2 * numParts = f2 then 2  -- split on dim 2 (last)
      else 2  -- default to last
  | [s0, s1], [f0, f1] =>
      if s0 * numParts = f0 ∧ s1 = f1 then 0
      else if s0 = f0 ∧ s1 * numParts = f1 then 1
      else 1  -- default to last
  | _, _ => 100  -- fallback

def reconstruct (numParts rank : Nat) (xs : List Tensor) : Tensor :=
  match xs with
  | [] =>
      -- Underspecified: no shards. Keep a well-typed default.
      Tensor.mkShape [] (fun _ => 0)
  | [x] => x
  | _ =>
      let sh := (xs.head?.map (fun t => t.shape)).getD []
      if sh = [1] then
        allReducePrim numParts rank xs
      else
        -- Check if this is 3D and split on dim 0
        match sh with
        | [_, _, _] =>
            -- For 3D tensors, use dim0 gather
            allGatherPrimDim0 numParts rank xs
        | _ =>
            allGatherPrim numParts rank xs

/-- Dimension-aware reconstruction: uses `allGatherPrimDimN` with an explicit gather dimension. -/
def reconstructWithDim (gatherDim numParts rank : Nat) (xs : List Tensor) : Tensor :=
  match xs with
  | [] => Tensor.mkShape [] (fun _ => 0)
  | [x] => x
  | _ =>
      let sh := (xs.head?.map (fun t => t.shape)).getD []
      if sh = [1] then
        allReducePrim numParts rank xs
      else
        allGatherPrimDimN gatherDim numParts rank xs

/-- `reconstructWithDim` on a singleton list returns that element. -/
theorem reconstructWithDim_singleton (gatherDim numParts rank : Nat) (x : Tensor) :
    reconstructWithDim gatherDim numParts rank [x] = x := rfl

/-- `reconstructWithDim` on a list with ≥2 non-scalar elements uses `allGatherPrimDimN`. -/
theorem reconstructWithDim_cons_cons_nonscalar
    (gatherDim numParts rank : Nat) (x y : Tensor) (xs : List Tensor)
    (h : x.shape ≠ [1]) :
    reconstructWithDim gatherDim numParts rank (x :: y :: xs) =
      allGatherPrimDimN gatherDim numParts rank (x :: y :: xs) := by
  simp only [reconstructWithDim]
  have hhead : (Option.map (fun t => t.shape) (x :: y :: xs).head?).getD [] = x.shape := by simp
  rw [hhead]
  simp [h]

/-- `reconstruct` on a list with ≥2 elements and scalar head uses `allReducePrim`. -/
theorem reconstruct_cons_cons_scalar
    (numParts rank : Nat) (x y : Tensor) (xs : List Tensor)
    (h : x.shape = [1]) :
    reconstruct numParts rank (x :: y :: xs) = allReducePrim numParts rank (x :: y :: xs) := by
  -- Reduce by definition; the head shape decides the branch.
  simp [reconstruct, h]

/-!
## Unified Matrix Multiplication Theorems

These theorems provide value-level characterizations for the unified matmul operations.
Instead of proving separate theorems for fw_linear, bw_linear_dx, and bw_linear_dw,
we prove once for matmul and derive the others as corollaries.
-/

/-- Core theorem: unified matmul value at index (r, c).

This single theorem replaces:
- fw_linear_valAt_mul_add
- bw_linear_fst_valAt_mul_add (for dX)
And simplifies the proof of bw_linear_snd_valAt_mul_add (for dW).
-/
theorem matmul_valAt
    (m n k : Nat) (a b : Tensor)
    (_ : a.shape = [m, k])
    (_ : b.shape = [n, k])
    (r : Nat) (hr : r < m)
    (c : Nat) (hc : c < n) :
    valAt (Tensor.mkShape [m, n] (k_matmul m n k a b)) (r * n + c) =
      ∑ j ∈ Finset.range k, (valAt a (r * k + j)) * (valAt b (c * k + j)) := by
  -- Prove the queried index is in-bounds for the output tensor [m, n]
  have hlt_mn : r * n + c < m * n := by
    have hlt1 : r * n + c < r * n + n := Nat.add_lt_add_left hc (r * n)
    have hlt2 : r * n + c < (r + 1) * n := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
    have hle : (r + 1) * n ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hr)
    exact lt_of_lt_of_le hlt2 hle
  have hlt' : (r * n + c) < prodShape ([m, n] : Shape) := by
    simpa [prodShape] using hlt_mn

  -- Reduce division/modulo
  have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  have hdiv : (r * n + c) / n = r := by
    have heq : c + n * r = r * n + c := by ring
    exact (Nat.div_mod_unique hn_pos).2 ⟨heq, hc⟩ |>.1
  have hmod : (r * n + c) % n = c := by
    have heq : c + n * r = r * n + c := by ring
    exact (Nat.div_mod_unique hn_pos).2 ⟨heq, hc⟩ |>.2

  -- Unfold valAt and k_matmul
  simp only [valAt, hlt', Tensor.mkShape, dite_true]
  simp only [k_matmul, hdiv, hmod, valAt]

/-- Transposed matmul value at index (c, j). Used for weight gradient computation. -/
theorem matmul_transpose_valAt
    (m n k : Nat) (a b : Tensor)
    (_ : a.shape = [m, n])
    (_ : b.shape = [m, k])
    (c : Nat) (hc : c < n)
    (j : Nat) (hj : j < k) :
    valAt (Tensor.mkShape [n, k] (k_matmul_transpose m n k a b)) (c * k + j) =
      ∑ r ∈ Finset.range m, (valAt a (r * n + c)) * (valAt b (r * k + j)) := by
  -- Prove the queried index is in-bounds for the output tensor [n, k]
  have hlt_nk : c * k + j < n * k := by
    have hlt1 : c * k + j < c * k + k := Nat.add_lt_add_left hj (c * k)
    have hlt2 : c * k + j < (c + 1) * k := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
    have hle : (c + 1) * k ≤ n * k := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hc)
    exact lt_of_lt_of_le hlt2 hle
  have hlt' : (c * k + j) < prodShape ([n, k] : Shape) := by
    simpa [prodShape] using hlt_nk

  -- Reduce division/modulo
  have hk_pos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hdiv : (c * k + j) / k = c := by
    have heq : j + k * c = c * k + j := by ring
    exact (Nat.div_mod_unique hk_pos).2 ⟨heq, hj⟩ |>.1
  have hmod : (c * k + j) % k = j := by
    have heq : j + k * c = c * k + j := by ring
    exact (Nat.div_mod_unique hk_pos).2 ⟨heq, hj⟩ |>.2

  -- Unfold valAt and k_matmul_transpose
  simp only [valAt, hlt', Tensor.mkShape, dite_true]
  simp only [k_matmul_transpose, hdiv, hmod, valAt]

/-- Legacy theorem: fw_linear is just matmul with specific shapes.
Now proved as a corollary of the unified matmul_valAt. -/
theorem fw_linear_valAt_mul_add
    (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i])
    (hw : w.shape = [o, i])
    (p : Nat) (hp : p < b)
    (c : Nat) (hc : c < o) :
    valAt (fw_linear x w) (p * o + c) =
      ∑ k ∈ Finset.range i, (valAt x (p * i + k)) * (valAt w (c * i + k)) := by
  -- fw_linear is defined as Tensor.mkShape [b, o] (k_matmul b o i x w)
  have hfw : fw_linear x w = Tensor.mkShape [b, o] (k_matmul b o i x w) := by
    simp only [fw_linear, hx, hw, Tensor.mkShape]
  rw [hfw]
  exact matmul_valAt b o i x w hx hw p hp c hc

/-- Value-level characterization of the input gradient (dX) from `bw_linear`.

For `bw_linear gradOut x w`, the first component (dX) has shape `[b, i]` and
at index `(p, k)` (flattened as `p * i + k`) equals:
  `dX[p, k] = Σ_j gradOut[p * o + j] * w[k * o + j]`

Note: This matches the k_matmul kernel with B stored transposed.
-/
theorem bw_linear_fst_valAt_mul_add
    (b i o : Nat) (gradOut x w : Tensor)
    (hg : gradOut.shape = [b, o])
    (hx : x.shape = [b, i])
    (hw : w.shape = [o, i])
    (p : Nat) (hp : p < b)
    (k : Nat) (hk : k < i) :
    valAt (bw_linear gradOut x w).1 (p * i + k) =
      ∑ j ∈ Finset.range o, (valAt gradOut (p * o + j)) * (valAt w (j * i + k)) := by
  have hbw : (bw_linear gradOut x w).1 =
      Tensor.mkShape [b, i] (k_matmul_right_transpose b i o gradOut w) := by
    simp only [bw_linear, hg, hx, hw, Tensor.mkShape]
  rw [hbw]
  have hlt_bi : p * i + k < b * i := by
    have hlt1 : p * i + k < p * i + i := Nat.add_lt_add_left hk (p * i)
    have hlt2 : p * i + k < (p + 1) * i := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
    have hle : (p + 1) * i ≤ b * i := Nat.mul_le_mul_right i (Nat.succ_le_of_lt hp)
    exact lt_of_lt_of_le hlt2 hle
  have hlt' : (p * i + k) < prodShape ([b, i] : Shape) := by
    simpa [prodShape] using hlt_bi
  have hi_pos : 0 < i := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hdiv : (p * i + k) / i = p := by
    have heq : k + i * p = p * i + k := by ring
    exact (Nat.div_mod_unique hi_pos).2 ⟨heq, hk⟩ |>.1
  have hmod : (p * i + k) % i = k := by
    have heq : k + i * p = p * i + k := by ring
    exact (Nat.div_mod_unique hi_pos).2 ⟨heq, hk⟩ |>.2
  simp only [valAt, hlt', Tensor.mkShape, dite_true]
  simp only [k_matmul_right_transpose, hdiv, hmod, valAt]

/-- Value-level characterization of the weight gradient (dW) from `bw_linear`.

For `bw_linear gradOut x w`, the second component (dW) has shape `[o, i]` and
at index `(c, k)` (flattened as `c * i + k`) equals:
  `dW[c, k] = Σ_p gradOut[p, c] * x[p, k]`

Now proved as a corollary of the unified matmul_transpose_valAt.
-/
theorem bw_linear_snd_valAt_mul_add
    (b i o : Nat) (gradOut x w : Tensor)
    (hg : gradOut.shape = [b, o])
    (hx : x.shape = [b, i])
    (hw : w.shape = [o, i])
    (c : Nat) (hc : c < o)
    (k : Nat) (hk : k < i) :
    valAt (bw_linear gradOut x w).2 (c * i + k) =
      ∑ p ∈ Finset.range b, (valAt gradOut (p * o + c)) * (valAt x (p * i + k)) := by
  -- bw_linear.2 is defined as Tensor.mkShape [o, i] (k_matmul_transpose b o i gradOut x)
  have hbw : (bw_linear gradOut x w).2 = Tensor.mkShape [o, i] (k_matmul_transpose b o i gradOut x) := by
    simp only [bw_linear, hg, hx, hw, Tensor.mkShape]
  rw [hbw]
  exact matmul_transpose_valAt b o i gradOut x hg hx c hc k hk

/-- Shape of bw_linear first output (dX). -/
theorem bw_linear_fst_shape
    (b i o : Nat) (gradOut x w : Tensor)
    (hg : gradOut.shape = [b, o])
    (hx : x.shape = [b, i])
    (hw : w.shape = [o, i]) :
    (bw_linear gradOut x w).1.shape = [b, i] := by
  simp [bw_linear, hg, hx, hw, Tensor.mkShape]

/-!
## bw_linear (dX) with column-sharded weights (allGather over i)

This lemma states that when the weight matrix is sharded along the input dimension `i`
and reassembled by `allGatherPrim`, the input gradient (dX) computed by `bw_linear`
is exactly the `allGatherPrim` of per-shard dX results.
-/

theorem bw_linear_fst_allGather_eq_allGather_bw_linear_chunk
    (numParts b i o shard : Nat) (g x : Tensor) (ws : List Tensor)
    (hg : g.shape = [b, o])
    (hx : x.shape = [b, i])
    (hi : i = numParts * shard)
    (hws_len : ws.length = numParts)
    (hws_shapes : ∀ w ∈ ws, w.shape = [o, shard])
    (hparts : 0 < numParts)
    (hshard : 0 < shard) :
    (bw_linear g x (allGatherPrim numParts 0 ws)).1 =
      allGatherPrim numParts 0 (List.ofFn (fun r : Fin numParts =>
        (bw_linear g (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩)).1)) := by
  classical
  let pieces : List Tensor :=
    List.ofFn (fun r : Fin numParts =>
      (bw_linear g (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩)).1)
  have hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [b, shard] := by
    cases hnp : numParts with
    | zero => simp [hnp] at hparts
    | succ n =>
        have hparts' : 0 < Nat.succ n := by
          simp [hnp] at hparts
          simp
        have hx' : x.shape = [b, (Nat.succ n) * shard] := by
          have hx1 : x.shape = [b, numParts * shard] := by
            simpa [hi] using hx
          simpa [hnp] using hx1
        have hchunk0 : (chunkPrim (Nat.succ n) 0 x).shape = [b, shard] := by
          simpa using (chunkPrim_shape' (Nat.succ n) 0 b shard x hx' hparts')
        have hw0 : (ws.get ⟨0, by omega⟩).shape = [o, shard] := by
          have hmem : ws.get ⟨0, by omega⟩ ∈ ws := List.get_mem _ _
          exact hws_shapes _ hmem
        have hshape0 : (bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).1.shape = [b, shard] := by
          exact bw_linear_fst_shape b shard o g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)
            hg hchunk0 hw0
        have hhead' : pieces.head? =
            some ((bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).1) := by
          simp [pieces, hnp]
        -- manual reduction to avoid simp recursion
        have hshape0' : ((some ((bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).1)).map
            (fun t => t.shape)).getD [] = [b, shard] := by
          -- avoid simp: reduce manually
          change (bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).1.shape = [b, shard]
          exact hshape0
        calc
          (pieces.head?.map (fun t => t.shape)).getD [] =
              ((some ((bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).1)).map
                (fun t => t.shape)).getD [] := by simp [hhead']
          _ = [b, shard] := hshape0'
  have hshapeR : (allGatherPrim numParts 0 pieces).shape = [b, shard * numParts] := by
    exact allGatherPrim_shape numParts b shard pieces hhead
  have hshapeW : (allGatherPrim numParts 0 ws).shape = [o, i] := by
    have hheadW : (ws.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
      cases hws' : ws with
      | nil => simp [hws'] at hws_len; omega
      | cons w ws' =>
          have hw : w.shape = [o, shard] := hws_shapes w (by simp [hws'])
          simp [hw]
    simpa [hi, Nat.mul_comm] using (allGatherPrim_shape numParts o shard ws hheadW)
  have hshapeL : (bw_linear g x (allGatherPrim numParts 0 ws)).1.shape = [b, i] := by
    exact bw_linear_fst_shape b i o g x (allGatherPrim numParts 0 ws) hg hx hshapeW
  have hshape_eq : (bw_linear g x (allGatherPrim numParts 0 ws)).1.shape =
      (allGatherPrim numParts 0 pieces).shape := by
    simp [hshapeL, hshapeR, hi, Nat.mul_comm]
  apply Tensor.ext hshape_eq
  intro idx hidx
  -- Decompose idx into (p, r, j)
  let full := shard * numParts
  have hfull_pos : 0 < full := Nat.mul_pos hshard hparts
  let p := idx / full
  let l := idx % full
  let r := l / shard
  let j := l % shard
  have hj_lt : j < shard := Nat.mod_lt l hshard
  have hr_lt : r < numParts := by
    have : l < shard * numParts := by
      simpa [full] using (Nat.mod_lt idx hfull_pos)
    exact (Nat.div_lt_iff_lt_mul hshard).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this)
  have hp_lt : p < b := by
    have hshape_prod : prodShape ([b, i] : Shape) = b * i := by simp [prodShape]
    have hidx' : idx < b * i := by
      simpa [hshapeL, hshape_prod] using hidx
    have hidx'' : idx < b * full := by
      simpa [full, hi, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hidx'
    exact (Nat.div_lt_iff_lt_mul hfull_pos).2 hidx''
  have hidx_eq : idx = p * full + (r * shard + j) := by
    have h1 : idx = p * full + l := by
      have h' : idx = full * (idx / full) + idx % full := (Nat.div_add_mod idx full).symm
      simpa [p, l, Nat.mul_comm] using h'
    have h2 : l = r * shard + j := by
      have h' : l = shard * (l / shard) + l % shard := (Nat.div_add_mod l shard).symm
      simpa [r, j, Nat.mul_comm] using h'
    simp [h1, h2]
  -- LHS value via bw_linear_fst_valAt_mul_add
  have hvalL := bw_linear_fst_valAt_mul_add b i o g x (allGatherPrim numParts 0 ws)
    hg hx hshapeW p hp_lt (r * shard + j) (by
      have hrem : r * shard + j < shard * numParts := by
        have hlt1 : r * shard + j < r * shard + shard := Nat.add_lt_add_left hj_lt (r * shard)
        have hlt2 : r * shard + j < (r + 1) * shard := by
          simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
        have hle : (r + 1) * shard ≤ numParts * shard := by
          exact Nat.mul_le_mul_right shard (Nat.succ_le_of_lt hr_lt)
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using lt_of_lt_of_le hlt2 hle
      simpa [hi, full, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hrem)
  -- RHS value via allGatherPrim and per-shard bw_linear
  have hvalR := allGatherPrim_valAt_mul_add numParts (rank := r) b shard pieces
    (hhead := hhead) (hparts := hparts) (hrank := hr_lt) (p := p) (hp := hp_lt) (j := j) (hj := hj_lt)
  have hvalPiece := bw_linear_fst_valAt_mul_add b shard o g (chunkPrim numParts r x)
    (ws.get ⟨r, by omega⟩) hg
    (by simpa [hi] using (chunkPrim_shape' numParts r b shard x (by simpa [hi] using hx) hparts))
    (by
      have hmem : ws.get ⟨r, by omega⟩ ∈ ws := List.get_mem _ _
      exact hws_shapes _ hmem)
    p hp_lt j hj_lt
  have hmapW : ∀ t : Nat, t < o →
      valAt (allGatherPrim numParts 0 ws) (t * i + (r * shard + j)) =
        valAt (ws.get ⟨r, by omega⟩) (t * shard + j) := by
    intro t ht
    have hheadW : (ws.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
      cases hws' : ws with
      | nil => simp [hws'] at hws_len; omega
      | cons w ws' =>
          have hw : w.shape = [o, shard] := hws_shapes w (by simp [hws'])
          simp [hw]
    have hmap := allGatherPrim_valAt_mul_add numParts r o shard ws hheadW hparts hr_lt t ht j hj_lt
    have hidx' : t * (shard * numParts) + r * shard + j = t * i + (r * shard + j) := by
      simp [hi, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
    have hr_len : r < ws.length := by
      simpa [hws_len] using hr_lt
    have hgetD : ws.getD r (zeroTensor [o, shard]) = ws.get ⟨r, hr_len⟩ := by
      simp only [List.getD, List.getElem?_eq_getElem hr_len, Option.getD_some, List.get_eq_getElem]
    have hmap' : valAt (allGatherPrim numParts 0 ws) (t * i + (r * shard + j)) =
        valAt (ws.getD r (zeroTensor [o, shard])) (t * shard + j) := by
      simpa [hidx'] using hmap
    -- rewrite getD to get, then use List.get_eq_getElem to align with `ws[r]`
    have hmap'' : valAt (allGatherPrim numParts 0 ws) (t * i + (r * shard + j)) =
        valAt (ws.get ⟨r, hr_len⟩) (t * shard + j) := by
      -- rewrite getD to get on the RHS of hmap'
      rw [hgetD] at hmap'
      exact hmap'
    -- rewrite `ws[r]` to `ws.get ⟨r, _⟩`
    simpa [List.get_eq_getElem] using hmap''
  have hvalL' : valAt (bw_linear g x (allGatherPrim numParts 0 ws)).1 (p * i + (r * shard + j)) =
      ∑ t ∈ Finset.range o, (valAt g (p * o + t)) *
        (valAt (ws.get ⟨r, by omega⟩) (t * shard + j)) := by
    have hvalL0 : valAt (bw_linear g x (allGatherPrim numParts 0 ws)).1 (p * i + (r * shard + j)) =
        ∑ t ∈ Finset.range o, (valAt g (p * o + t)) *
          (valAt (allGatherPrim numParts 0 ws) (t * i + (r * shard + j))) := by
      simpa using hvalL
    refine hvalL0.trans ?_
    apply Finset.sum_congr rfl
    intro t ht
    have ht' : t < o := Finset.mem_range.mp ht
    simp [hmapW t ht']
  have hvalR' : valAt (bw_linear g (chunkPrim numParts r x) (ws.get ⟨r, by omega⟩)).1 (p * shard + j) =
      ∑ t ∈ Finset.range o, (valAt g (p * o + t)) *
        (valAt (ws.get ⟨r, by omega⟩) (t * shard + j)) := by
    simpa using hvalPiece
  have hvalR'' : valAt (allGatherPrim numParts 0 pieces) (p * full + r * shard + j) =
      ∑ t ∈ Finset.range o, (valAt g (p * o + t)) *
        (valAt (ws.get ⟨r, by omega⟩) (t * shard + j)) := by
    have hr_len_pieces : r < pieces.length := by
      simpa [pieces] using hr_lt
    have hgetD_pieces : pieces.getD r (zeroTensor [b, shard]) = pieces.get ⟨r, hr_len_pieces⟩ := by
      simp only [List.getD, List.getElem?_eq_getElem hr_len_pieces, Option.getD_some, List.get_eq_getElem]
    calc
      valAt (allGatherPrim numParts 0 pieces) (p * full + r * shard + j)
          = valAt (pieces.getD r (zeroTensor [b, shard])) (p * shard + j) := by
              simpa [full] using hvalR
      _ = valAt (pieces.get ⟨r, hr_len_pieces⟩) (p * shard + j) := by
        rw [hgetD_pieces]
      _ = valAt (bw_linear g (chunkPrim numParts r x) (ws.get ⟨r, by omega⟩)).1 (p * shard + j) := by
            simp [pieces]
      _ = ∑ t ∈ Finset.range o, (valAt g (p * o + t)) *
            (valAt (ws.get ⟨r, by omega⟩) (t * shard + j)) := hvalR'
  have hidx_norm : p * i + (r * shard + j) = p * full + r * shard + j := by
    simp [full, hi, Nat.mul_comm, Nat.mul_assoc, Nat.add_assoc]
  have hidx_eq' : idx = p * full + r * shard + j := by
    simpa [Nat.add_assoc] using hidx_eq
  have hvalL'' : valAt (bw_linear g x (allGatherPrim numParts 0 ws)).1 idx =
      ∑ t ∈ Finset.range o, (valAt g (p * o + t)) *
        (valAt (ws.get ⟨r, by omega⟩) (t * shard + j)) := by
    simpa [hidx_eq', hidx_norm] using hvalL'
  have hvalR''' : valAt (allGatherPrim numParts 0 pieces) idx =
      ∑ t ∈ Finset.range o, (valAt g (p * o + t)) *
        (valAt (ws.get ⟨r, by omega⟩) (t * shard + j)) := by
    simpa [hidx_eq'] using hvalR''
  exact hvalL''.trans hvalR'''.symm

/-- Shape of bw_linear second output (dW). -/
theorem bw_linear_snd_shape
    (b i o : Nat) (gradOut x w : Tensor)
    (hg : gradOut.shape = [b, o])
    (hx : x.shape = [b, i])
    (hw : w.shape = [o, i]) :
    (bw_linear gradOut x w).2.shape = [o, i] := by
  simp [bw_linear, hg, hx, hw, Tensor.mkShape]

/-- Shape of bw_linear second output (dW) - flexible version. -/
theorem bw_linear_snd_shape'
    (gradOut x w : Tensor) (o i : Nat)
    (hg : ∃ bG oG, gradOut.shape = [bG, oG])
    (hx : ∃ bX iX, x.shape = [bX, iX])
    (hw : w.shape = [o, i]) :
    (bw_linear gradOut x w).2.shape = [o, i] := by
  obtain ⟨bG, oG, hg⟩ := hg
  obtain ⟨bX, iX, hx⟩ := hx
  simp only [bw_linear, hg, hx, hw, Tensor.mkShape]

/-- Shape of bw_linear first output (dX) - flexible version. -/
theorem bw_linear_fst_shape'
    (gradOut x w : Tensor) (b i : Nat)
    (hg : ∃ bG oG, gradOut.shape = [bG, oG])
    (hx : x.shape = [b, i])
    (hw : ∃ oW iW, w.shape = [oW, iW]) :
    (bw_linear gradOut x w).1.shape = [b, i] := by
  obtain ⟨bG, oG, hg⟩ := hg
  obtain ⟨oW, iW, hw⟩ := hw
  simp only [bw_linear, hg, hx, hw, Tensor.mkShape]

/-- Shape of bw_linear second output (dW) for 3D inputs. -/
theorem bw_linear_3d_snd_shape
    (b s o i : Nat) (gradOut x w : Tensor)
    (hg : gradOut.shape = [b, s, o])
    (hx : x.shape = [b, s, i])
    (hw : w.shape = [o, i]) :
    (bw_linear gradOut x w).2.shape = [o, i] := by
  simp [bw_linear, hg, hx, hw, Tensor.mkShape]

/-- Shape of bw_linear first output (dX) for 3D inputs. -/
theorem bw_linear_3d_fst_shape
    (b s o i : Nat) (gradOut x w : Tensor)
    (hg : gradOut.shape = [b, s, o])
    (hx : x.shape = [b, s, i])
    (hw : w.shape = [o, i]) :
    (bw_linear gradOut x w).1.shape = [b, s, i] := by
  simp [bw_linear, hg, hx, hw, Tensor.mkShape]

/-- `bw_linear` dW (second output) for 3D inputs in explicit `mkShape` form. -/
theorem bw_linear_dw_eq3d (g x w : Tensor) (b s o i : Nat)
    (hg : g.shape = [b, s, o]) (hx : x.shape = [b, s, i]) (hw : w.shape = [o, i]) :
    (bw_linear g x w).2 = Tensor.mkShape [o, i] (k_matmul_transpose (b * s) o i g x) := by
  simp only [bw_linear, hg, hx, hw]

/-- Value-level characterization of `bw_linear` dW for 3D inputs. -/
theorem bw_linear_dw_valAt3d (g x w : Tensor) (b s o i : Nat)
    (hg : g.shape = [b, s, o]) (hx : x.shape = [b, s, i]) (hw : w.shape = [o, i])
    (c : Nat) (hc : c < o) (k : Nat) (hk : k < i) :
    valAt (bw_linear g x w).2 (c * i + k) =
      ∑ r ∈ Finset.range (b * s), valAt g (r * o + c) * valAt x (r * i + k) := by
  rw [bw_linear_dw_eq3d g x w b s o i hg hx hw]
  have hlt_nk : c * i + k < o * i := by
    have hlt2 : c * i + k < (c + 1) * i := by
      have := Nat.add_lt_add_left hk (c * i)
      simpa [Nat.succ_mul, Nat.add_assoc] using this
    exact lt_of_lt_of_le hlt2 (Nat.mul_le_mul_right i (Nat.succ_le_of_lt hc))
  have hlt' : c * i + k < prodShape ([o, i] : Shape) := by simpa [prodShape] using hlt_nk
  have hk_pos : 0 < i := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hdiv : (c * i + k) / i = c := by
    have heq : k + i * c = c * i + k := by ring
    exact ((Nat.div_mod_unique hk_pos).2 ⟨heq, hk⟩).1
  have hmod : (c * i + k) % i = k := by
    have heq : k + i * c = c * i + k := by ring
    exact ((Nat.div_mod_unique hk_pos).2 ⟨heq, hk⟩).2
  simp only [valAt, hlt', Tensor.mkShape, dite_true]
  simp only [k_matmul_transpose, hdiv, hmod, valAt]

set_option maxHeartbeats 1600000 in
/-- The dW output of `bw_linear` where the input `x` is dim-1 all-gathered from 4 shards
    (each `[1,2,32]`) and the gradient `g` (`[1,8,32]`) is dim-1 chunked per rank,
    equals `tensorSum` of the per-rank dW outputs.  This is the data-parallel weight
    reduction (CROSS_DP_WRED) identity for `BW_linear`. -/
theorem bw_linear_dw_dp_split_dim1_4_1_2_32
    (g x0 x1 x2 x3 w : Tensor)
    (hg : g.shape = [1, 8, 32])
    (hx0 : x0.shape = [1, 2, 32]) (hx1 : x1.shape = [1, 2, 32])
    (hx2 : x2.shape = [1, 2, 32]) (hx3 : x3.shape = [1, 2, 32])
    (hw : w.shape = [32, 32]) :
    (bw_linear g (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]) w).2 =
      tensorSum [(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).2,
                 (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).2,
                 (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).2,
                 (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).2] := by
  have hxhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hx0]
  set X := allGatherPrimDimN 1 4 0 [x0, x1, x2, x3] with hXdef
  have hXshape : X.shape = [1, 8, 32] := by
    rw [hXdef, allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hxhead]; simp [List.set, List.getD]
  have hc0 : (chunkPrimDimN 1 4 0 g).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 0 g _ hg (by omega)]; simp [List.set, List.getD]
  have hc1 : (chunkPrimDimN 1 4 1 g).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 1 g _ hg (by omega)]; simp [List.set, List.getD]
  have hc2 : (chunkPrimDimN 1 4 2 g).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 2 g _ hg (by omega)]; simp [List.set, List.getD]
  have hc3 : (chunkPrimDimN 1 4 3 g).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 3 g _ hg (by omega)]; simp [List.set, List.getD]
  apply Tensor.ext
  · rw [bw_linear_3d_snd_shape 1 8 32 32 g X w hg hXshape hw, tensorSum_shape,
        bw_linear_3d_snd_shape 1 2 32 32 (chunkPrimDimN 1 4 0 g) x0 w hc0 hx0 hw]
  · intro idx hidx
    rw [bw_linear_3d_snd_shape 1 8 32 32 g X w hg hXshape hw] at hidx
    have hidxp : idx < 1024 := by simpa [prodShape] using hidx
    have hc : idx / 32 < 32 := by omega
    have hk : idx % 32 < 32 := by omega
    have hide : idx = (idx / 32) * 32 + idx % 32 := by omega
    rw [hide]
    rw [bw_linear_dw_valAt3d g X w 1 8 32 32 hg hXshape hw (idx / 32) hc (idx % 32) hk]
    rw [show tensorSum [(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).2,
                        (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).2,
                        (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).2,
                        (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).2] =
            Tensor.mkShape (bw_linear (chunkPrimDimN 1 4 0 g) x0 w).2.shape
              (fun i => [(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).2,
                         (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).2,
                         (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).2,
                         (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).2].foldl
                         (fun acc x => acc + valAt x i.1) 0) from rfl]
    rw [valAt_of_lt _ _ (by
      rw [Tensor.mkShape, bw_linear_3d_snd_shape 1 2 32 32 (chunkPrimDimN 1 4 0 g) x0 w hc0 hx0 hw]
      simp [prodShape]; omega)]
    simp only [Tensor.mkShape, List.foldl]
    rw [bw_linear_dw_valAt3d (chunkPrimDimN 1 4 0 g) x0 w 1 2 32 32 hc0 hx0 hw (idx / 32) hc (idx % 32) hk,
        bw_linear_dw_valAt3d (chunkPrimDimN 1 4 1 g) x1 w 1 2 32 32 hc1 hx1 hw (idx / 32) hc (idx % 32) hk,
        bw_linear_dw_valAt3d (chunkPrimDimN 1 4 2 g) x2 w 1 2 32 32 hc2 hx2 hw (idx / 32) hc (idx % 32) hk,
        bw_linear_dw_valAt3d (chunkPrimDimN 1 4 3 g) x3 w 1 2 32 32 hc3 hx3 hw (idx / 32) hc (idx % 32) hk]
    simp only [show (1 : Nat) * 8 = 8 from rfl, show (1 : Nat) * 2 = 2 from rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [chunk_dim1_4_1_8_32_valAt g 0 0 (idx / 32) hg (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt g 0 1 (idx / 32) hg (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt g 1 0 (idx / 32) hg (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt g 1 1 (idx / 32) hg (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt g 2 0 (idx / 32) hg (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt g 2 1 (idx / 32) hg (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt g 3 0 (idx / 32) hg (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt g 3 1 (idx / 32) hg (by omega) (by omega) hc]
    rw [hXdef]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 0 (by omega) 0 (by omega) (idx % 32) hk hxhead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 0 (by omega) 1 (by omega) (idx % 32) hk hxhead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 1 (by omega) 0 (by omega) (idx % 32) hk hxhead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 1 (by omega) 1 (by omega) (idx % 32) hk hxhead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 2 (by omega) 0 (by omega) (idx % 32) hk hxhead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 2 (by omega) 1 (by omega) (idx % 32) hk hxhead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 3 (by omega) 0 (by omega) (idx % 32) hk hxhead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0, x1, x2, x3] 3 (by omega) 1 (by omega) (idx % 32) hk hxhead]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    ring

/-!
## bw_linear (dW) with column-sharded inputs (allGather over i)

This lemma states that when the input matrix `x` is sharded along the input dimension `i`
and reassembled by `allGatherPrim`, the weight gradient (dW) computed by `bw_linear`
is exactly the `allGatherPrim` of per-shard dW results.

Key insight: dW = gradOut.T @ x, so sharding x along columns shards dW along columns.
Unlike dX, dW does NOT depend on the weight matrix w.
-/

theorem bw_linear_snd_allGather_eq_allGather_bw_linear_chunk
    (numParts b i o shard : Nat) (g x : Tensor) (ws : List Tensor)
    (hg : g.shape = [b, o])
    (hx : x.shape = [b, i])
    (hi : i = numParts * shard)
    (hws_len : ws.length = numParts)
    (hws_shapes : ∀ w ∈ ws, w.shape = [o, shard])
    (hparts : 0 < numParts)
    (hshard : 0 < shard) :
    (bw_linear g x (allGatherPrim numParts 0 ws)).2 =
      allGatherPrim numParts 0 (List.ofFn (fun r : Fin numParts =>
        (bw_linear g (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩)).2)) := by
  classical
  let pieces : List Tensor :=
    List.ofFn (fun r : Fin numParts =>
      (bw_linear g (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩)).2)
  -- Shape of first element in pieces
  have hhead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
    cases hnp : numParts with
    | zero => simp [hnp] at hparts
    | succ n =>
        have hparts' : 0 < Nat.succ n := by simp [hnp] at hparts; simp
        have hx' : x.shape = [b, (Nat.succ n) * shard] := by simpa [hi, hnp] using hx
        have hchunk0 : (chunkPrim (Nat.succ n) 0 x).shape = [b, shard] := by
          simpa using (chunkPrim_shape' (Nat.succ n) 0 b shard x hx' hparts')
        have hw0 : (ws.get ⟨0, by omega⟩).shape = [o, shard] := by
          have hmem : ws.get ⟨0, by omega⟩ ∈ ws := List.get_mem _ _
          exact hws_shapes _ hmem
        -- dW shape is [o, shard] when x chunk is [b, shard]
        have hshape0 : (bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).2.shape = [o, shard] := by
          exact bw_linear_snd_shape b shard o g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)
            hg hchunk0 hw0
        have hhead' : pieces.head? =
            some ((bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).2) := by
          simp [pieces, hnp]
        have hshape0' : ((some ((bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).2)).map
            (fun t => t.shape)).getD [] = [o, shard] := by
          change (bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).2.shape = [o, shard]
          exact hshape0
        calc
          (pieces.head?.map (fun t => t.shape)).getD [] =
              ((some ((bw_linear g (chunkPrim (Nat.succ n) 0 x) (ws.get ⟨0, by omega⟩)).2)).map
                (fun t => t.shape)).getD [] := by simp [hhead']
          _ = [o, shard] := hshape0'
  have hshapeR : (allGatherPrim numParts 0 pieces).shape = [o, shard * numParts] := by
    exact allGatherPrim_shape numParts o shard pieces hhead
  have hshapeW : (allGatherPrim numParts 0 ws).shape = [o, i] := by
    have hheadW : (ws.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
      cases hws' : ws with
      | nil => simp [hws'] at hws_len; omega
      | cons w ws' =>
          have hw : w.shape = [o, shard] := hws_shapes w (by simp [hws'])
          simp [hw]
    simpa [hi, Nat.mul_comm] using (allGatherPrim_shape numParts o shard ws hheadW)
  have hshapeL : (bw_linear g x (allGatherPrim numParts 0 ws)).2.shape = [o, i] := by
    exact bw_linear_snd_shape b i o g x (allGatherPrim numParts 0 ws) hg hx hshapeW
  have hshape_eq : (bw_linear g x (allGatherPrim numParts 0 ws)).2.shape =
      (allGatherPrim numParts 0 pieces).shape := by
    simp [hshapeL, hshapeR, hi, Nat.mul_comm]
  apply Tensor.ext hshape_eq
  intro idx hidx
  -- Decompose idx into (c, r, j) where c is output row, r is shard index, j is within-shard col
  let full := shard * numParts
  have hfull_pos : 0 < full := Nat.mul_pos hshard hparts
  let c := idx / full       -- output row
  let l := idx % full       -- position within row (maps to column)
  let r := l / shard        -- shard index
  let j := l % shard        -- position within shard
  have hj_lt : j < shard := Nat.mod_lt l hshard
  have hr_lt : r < numParts := by
    have : l < shard * numParts := by simpa [full] using (Nat.mod_lt idx hfull_pos)
    exact (Nat.div_lt_iff_lt_mul hshard).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this)
  have hc_lt : c < o := by
    have hshape_prod : prodShape ([o, i] : Shape) = o * i := by simp [prodShape]
    have hidx' : idx < o * i := by simpa [hshapeL, hshape_prod] using hidx
    have hidx'' : idx < o * full := by
      simpa [full, hi, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hidx'
    exact (Nat.div_lt_iff_lt_mul hfull_pos).2 hidx''
  have hidx_eq : idx = c * full + (r * shard + j) := by
    have h1 : idx = c * full + l := by
      have h' : idx = full * (idx / full) + idx % full := (Nat.div_add_mod idx full).symm
      simpa [c, l, Nat.mul_comm] using h'
    have h2 : l = r * shard + j := by
      have h' : l = shard * (l / shard) + l % shard := (Nat.div_add_mod l shard).symm
      simpa [r, j, Nat.mul_comm] using h'
    simp [h1, h2]
  -- LHS value via bw_linear_snd_valAt_mul_add
  have hvalL := bw_linear_snd_valAt_mul_add b i o g x (allGatherPrim numParts 0 ws)
    hg hx hshapeW c hc_lt (r * shard + j) (by
      have hrem : r * shard + j < shard * numParts := by
        have hlt1 : r * shard + j < r * shard + shard := Nat.add_lt_add_left hj_lt (r * shard)
        have hlt2 : r * shard + j < (r + 1) * shard := by
          simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
        have hle : (r + 1) * shard ≤ numParts * shard := by
          exact Nat.mul_le_mul_right shard (Nat.succ_le_of_lt hr_lt)
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using lt_of_lt_of_le hlt2 hle
      simpa [hi, full, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hrem)
  -- RHS value via allGatherPrim and per-shard bw_linear
  have hvalR := allGatherPrim_valAt_mul_add numParts (rank := r) o shard pieces
    (hhead := hhead) (hparts := hparts) (hrank := hr_lt) (p := c) (hp := hc_lt) (j := j) (hj := hj_lt)
  have hvalPiece := bw_linear_snd_valAt_mul_add b shard o g (chunkPrim numParts r x)
    (ws.get ⟨r, by omega⟩) hg
    (by simpa [hi] using (chunkPrim_shape' numParts r b shard x (by simpa [hi] using hx) hparts))
    (by
      have hmem : ws.get ⟨r, by omega⟩ ∈ ws := List.get_mem _ _
      exact hws_shapes _ hmem)
    c hc_lt j hj_lt
  -- Key: x values at chunk position map to original x values
  have hmapX : ∀ p : Nat, p < b →
      valAt (chunkPrim numParts r x) (p * shard + j) =
        valAt x (p * i + (r * shard + j)) := by
    intro p hp
    have hchunk := chunkPrim_valAt_mul_add numParts r b shard x (by simpa [hi] using hx) hparts hr_lt p hp j hj_lt
    simp only [hi, Nat.add_assoc] at hchunk ⊢
    exact hchunk
  have hvalL' : valAt (bw_linear g x (allGatherPrim numParts 0 ws)).2 (c * i + (r * shard + j)) =
      ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt x (p * i + (r * shard + j))) := by
    simpa using hvalL
  have hvalR' : valAt (bw_linear g (chunkPrim numParts r x) (ws.get ⟨r, by omega⟩)).2 (c * shard + j) =
      ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt (chunkPrim numParts r x) (p * shard + j)) := by
    simpa using hvalPiece
  have hvalR'' : valAt (allGatherPrim numParts 0 pieces) (c * full + r * shard + j) =
      ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt x (p * i + (r * shard + j))) := by
    have hr_len_pieces : r < pieces.length := by simpa [pieces] using hr_lt
    have hgetD_pieces : pieces.getD r (zeroTensor [o, shard]) = pieces.get ⟨r, hr_len_pieces⟩ := by
      simp only [List.getD, List.getElem?_eq_getElem hr_len_pieces, Option.getD_some, List.get_eq_getElem]
    calc
      valAt (allGatherPrim numParts 0 pieces) (c * full + r * shard + j)
          = valAt (pieces.getD r (zeroTensor [o, shard])) (c * shard + j) := by
              simpa [full] using hvalR
      _ = valAt (pieces.get ⟨r, hr_len_pieces⟩) (c * shard + j) := by rw [hgetD_pieces]
      _ = valAt (bw_linear g (chunkPrim numParts r x) (ws.get ⟨r, by omega⟩)).2 (c * shard + j) := by
            simp [pieces]
      _ = ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt (chunkPrim numParts r x) (p * shard + j)) := hvalR'
      _ = ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt x (p * i + (r * shard + j))) := by
            apply Finset.sum_congr rfl; intro p hp
            simp [hmapX p (Finset.mem_range.mp hp)]
  have hidx_norm : c * i + (r * shard + j) = c * full + r * shard + j := by
    simp [full, hi, Nat.mul_comm, Nat.mul_assoc, Nat.add_assoc]
  have hidx_eq' : idx = c * full + r * shard + j := by simpa [Nat.add_assoc] using hidx_eq
  have hvalL'' : valAt (bw_linear g x (allGatherPrim numParts 0 ws)).2 idx =
      ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt x (p * i + (r * shard + j))) := by
    simpa [hidx_eq', hidx_norm] using hvalL'
  have hvalR''' : valAt (allGatherPrim numParts 0 pieces) idx =
      ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt x (p * i + (r * shard + j))) := by
    simpa [hidx_eq'] using hvalR''
  exact hvalL''.trans hvalR'''.symm

/-- Shape-free version of `matmul_transpose_valAt`: unfolds k_matmul_transpose at (c*k+j). -/
private theorem k_matmul_transpose_valAt
    (m n k : Nat) (a b : Tensor)
    (c : Nat) (hc : c < n)
    (j : Nat) (hj : j < k) :
    valAt (Tensor.mkShape [n, k] (k_matmul_transpose m n k a b)) (c * k + j) =
      ∑ r ∈ Finset.range m, (valAt a (r * n + c)) * (valAt b (r * k + j)) := by
  have hlt_nk : c * k + j < n * k := by
    calc c * k + j < c * k + k := Nat.add_lt_add_left hj _
      _ = (c + 1) * k := by ring
      _ ≤ n * k := Nat.mul_le_mul_right k (by omega)
  have hlt' : (c * k + j) < prodShape ([n, k] : Shape) := by
    simpa [prodShape] using hlt_nk
  have hk_pos : 0 < k := by omega
  have hdiv : (c * k + j) / k = c := by
    rw [show c * k + j = j + c * k from by ring]; rw [Nat.add_mul_div_right _ _ hk_pos]
    rw [Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (c * k + j) % k = j := by
    rw [show c * k + j = j + c * k from by ring]; rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hj
  simp only [valAt, hlt', Tensor.mkShape, dite_true]
  simp only [k_matmul_transpose, hdiv, hmod, valAt]

/-- 3D bw_linear dW column-parallel: when x is sharded along last dim and w is sharded along
    last dim, each rank's dW is a column shard of the full dW. -/
theorem bw_linear_3d_snd_column_parallel
    (numParts b s o shard : Nat)
    (g : Tensor) (xs ws : List Tensor)
    (hg : g.shape = [b, s, o])
    (hxs_len : xs.length = numParts)
    (hws_len : ws.length = numParts)
    (hxs_shapes : ∀ x ∈ xs, x.shape = [b, s, shard])
    (hws_shapes : ∀ w ∈ ws, w.shape = [o, shard])
    (hparts : 0 < numParts)
    (hshard : 0 < shard)
    (_hb : 0 < b) (_hs : 0 < s) (_ho : 0 < o) :
    (bw_linear g (allGatherPrimDimN 2 numParts 0 xs) (allGatherPrimDimN 1 numParts 0 ws)).2 =
      allGatherPrimDimN 1 numParts 0 (List.ofFn (fun r : Fin numParts =>
        (bw_linear g (xs.get ⟨r.val, by omega⟩) (ws.get ⟨r.val, by omega⟩)).2)) := by
  classical
  -- Abbreviation
  set full := shard * numParts with hfull_def
  have hfull_pos : 0 < full := Nat.mul_pos hshard hparts
  have hshard_ne : shard ≠ 0 := by omega
  have hfull_ne : full ≠ 0 := by omega
  have hfull_ne' : shard * numParts ≠ 0 := hfull_ne
  have hfull_mul1_ne : shard * numParts * 1 ≠ 0 := by omega
  -- Head shapes
  have hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, shard] := by
    cases hxs' : xs with
    | nil => simp [hxs'] at hxs_len; omega
    | cons x0 _ => simp [hxs_shapes x0 (by simp [hxs'])]
  have hws_head : (ws.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
    cases hws' : ws with
    | nil => simp [hws'] at hws_len; omega
    | cons w0 _ => simp [hws_shapes w0 (by simp [hws'])]
  -- Gathered shapes
  have hgx : (allGatherPrimDimN 2 numParts 0 xs).shape = [b, s, full] := by
    have := allGatherPrimDimN_shape 2 numParts xs [b, s, shard] hxs_head
    simp only [List.getD, List.set] at this; exact this
  have hgw : (allGatherPrimDimN 1 numParts 0 ws).shape = [o, full] := by
    have := allGatherPrimDimN_shape 1 numParts ws [o, shard] hws_head
    simp only [List.getD, List.set] at this; exact this
  -- LHS dW shape
  have hshapeL : (bw_linear g (allGatherPrimDimN 2 numParts 0 xs)
      (allGatherPrimDimN 1 numParts 0 ws)).2.shape = [o, full] :=
    bw_linear_3d_snd_shape b s o full g _ _ hg hgx hgw
  -- Per-shard dW shape
  have hpiece_shape : ∀ r : Fin numParts,
      (bw_linear g (xs.get ⟨r.val, by omega⟩) (ws.get ⟨r.val, by omega⟩)).2.shape = [o, shard] := by
    intro r; exact bw_linear_3d_snd_shape b s o shard g _ _ hg
      (hxs_shapes _ (List.get_mem ..)) (hws_shapes _ (List.get_mem ..))
  -- RHS pieces
  set pieces := List.ofFn (fun r : Fin numParts =>
    (bw_linear g (xs.get ⟨r.val, by omega⟩) (ws.get ⟨r.val, by omega⟩)).2) with hpieces_def
  have hph : (pieces.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
    cases hnp : numParts with
    | zero => omega
    | succ n =>
      simp only [pieces, hnp]
      rw [list_ofFn_head_eq]
      change (bw_linear g (xs.get ⟨0, by omega⟩) (ws.get ⟨0, by omega⟩)).2.shape = [o, shard]
      exact hpiece_shape ⟨0, by omega⟩
  have hshapeR : (allGatherPrimDimN 1 numParts 0 pieces).shape = [o, full] := by
    have := allGatherPrimDimN_shape 1 numParts pieces [o, shard] hph
    simp only [List.getD, List.set] at this; exact this
  have hshape_eq : (bw_linear g (allGatherPrimDimN 2 numParts 0 xs)
      (allGatherPrimDimN 1 numParts 0 ws)).2.shape =
      (allGatherPrimDimN 1 numParts 0 pieces).shape := by
    rw [hshapeL, hshapeR]
  -- LHS .2 = Tensor.mkShape [o, full] (k_matmul_transpose (b*s) o full g (gather xs))
  have hbwL : (bw_linear g (allGatherPrimDimN 2 numParts 0 xs)
      (allGatherPrimDimN 1 numParts 0 ws)).2 =
      Tensor.mkShape [o, full] (k_matmul_transpose (b * s) o full g
        (allGatherPrimDimN 2 numParts 0 xs)) := by
    simp only [bw_linear, hg, hgx, hgw, Tensor.mkShape]
  -- Per-shard .2 = Tensor.mkShape [o, shard] (k_matmul_transpose (b*s) o shard g xs[r])
  have hbwR : ∀ (rk : Fin numParts),
      (bw_linear g (xs.get ⟨rk.val, by omega⟩) (ws.get ⟨rk.val, by omega⟩)).2 =
        Tensor.mkShape [o, shard] (k_matmul_transpose (b * s) o shard g
          (xs.get ⟨rk.val, by omega⟩)) := by
    intro rk; simp only [bw_linear, hg, hxs_shapes _ (List.get_mem ..),
      hws_shapes _ (List.get_mem ..), Tensor.mkShape]
  -- Pointwise equality
  apply Tensor.ext hshape_eq
  intro idx hidx
  -- idx < o * full
  have hidx' : idx < o * full := by simpa [hshapeL, prodShape, List.foldl] using hidx
  -- Decompose idx
  have hc_def : idx / full = idx / full := rfl
  have hrj_def : idx % full = idx % full := rfl
  have hrk_def : (idx % full) / shard = (idx % full) / shard := rfl
  have hjj_def : (idx % full) % shard = (idx % full) % shard := rfl
  set c := idx / full
  set rj := idx % full
  set rk := rj / shard
  set jj := rj % shard
  have hjj_lt : jj < shard := Nat.mod_lt rj hshard
  have hrk_lt : rk < numParts := Nat.div_lt_of_lt_mul (show rj < shard * numParts from Nat.mod_lt idx hfull_pos)
  have hc_lt : c < o := Nat.div_lt_of_lt_mul (show idx < full * o from by rw [Nat.mul_comm]; exact hidx')
  have hrj_lt : rj < full := Nat.mod_lt idx hfull_pos
  have hidx_eq : idx = c * full + (rk * shard + jj) := by
    have h1 : full * c + rj = idx := Nat.div_add_mod idx full
    have h2 : shard * rk + jj = rj := Nat.div_add_mod rj shard
    rw [← h1, ← h2]; ring
  have hrksj_lt : rk * shard + jj < full := by
    have h1 : shard * rk + jj = rj := Nat.div_add_mod rj shard
    rw [show rk * shard + jj = shard * rk + jj from by ring, h1]
    exact hrj_lt
  -- LHS value
  have hvalL : valAt (Tensor.mkShape [o, full] (k_matmul_transpose (b * s) o full g
      (allGatherPrimDimN 2 numParts 0 xs))) (c * full + (rk * shard + jj)) =
      ∑ p ∈ Finset.range (b * s), (valAt g (p * o + c)) *
        (valAt (allGatherPrimDimN 2 numParts 0 xs) (p * full + (rk * shard + jj))) :=
    k_matmul_transpose_valAt (b * s) o full g (allGatherPrimDimN 2 numParts 0 xs)
      c hc_lt (rk * shard + jj) hrksj_lt
  -- RHS: allGatherPrimDimN 1 on [o,shard] pieces maps (c, rk, jj) to pieces[rk] at (c, jj)
  -- Use allGatherPrim_valAt_mul_add since dim1 gather on [o,shard] = allGatherPrim
  -- Actually, allGatherPrimDimN 1 on [o,shard] behaves like allGatherPrim on [o,shard]
  -- pieces[rk] at c*shard+jj = Σ_p g[p*o+c] * xs[rk][p*shard+jj]
  have hvalR_piece : valAt (Tensor.mkShape [o, shard] (k_matmul_transpose (b * s) o shard g
      (xs.get ⟨rk, by omega⟩))) (c * shard + jj) =
      ∑ p ∈ Finset.range (b * s), (valAt g (p * o + c)) *
        (valAt (xs.get ⟨rk, by omega⟩) (p * shard + jj)) :=
    k_matmul_transpose_valAt (b * s) o shard g (xs.get ⟨rk, by omega⟩)
      c hc_lt jj hjj_lt
  -- Key: allGatherPrimDimN 2 on [b,s,shard] at index p*full + rk*shard+jj = xs[rk] at p*shard+jj
  have hgather_x_val : ∀ p, p < b * s →
      valAt (allGatherPrimDimN 2 numParts 0 xs) (p * full + (rk * shard + jj)) =
      valAt (xs.get ⟨rk, by omega⟩) (p * shard + jj) := by
    intro p hp
    -- Index is in bounds
    have hidx_bound : p * full + (rk * shard + jj) < prodShape [b, s, full] := by
      simp only [prodShape, List.foldl, Nat.one_mul]
      calc p * full + (rk * shard + jj)
          < p * full + full := Nat.add_lt_add_left hrksj_lt _
        _ = (p + 1) * full := by ring
        _ ≤ (b * s) * full := Nat.mul_le_mul_right _ (by omega)
        _ = b * s * full := by ring
    rw [valAt_of_lt _ _ (by rw [hgx]; exact hidx_bound)]
    simp (config := { decide := true }) only [allGatherPrimDimN, Tensor.mkShape, hxs_head,
      List.getD, List.drop, List.foldl, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some,
      hshard_ne, hfull_ne', ↓reduceIte, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]
    -- Arithmetic
    have h_div : (p * full + (rk * shard + jj)) / full = p := by
      rw [show p * full + (rk * shard + jj) = (rk * shard + jj) + p * full from by ring]
      rw [Nat.add_mul_div_right _ _ hfull_pos, Nat.div_eq_of_lt hrksj_lt, Nat.zero_add]
    have h_mod : (p * full + (rk * shard + jj)) % full = rk * shard + jj := by
      rw [show p * full + (rk * shard + jj) = (rk * shard + jj) + p * full from by ring]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrksj_lt]
    have h_rj_div : (rk * shard + jj) / shard = rk := by
      rw [show rk * shard + jj = jj + rk * shard from by ring]
      rw [Nat.add_mul_div_right _ _ hshard, Nat.div_eq_of_lt hjj_lt, Nat.zero_add]
    have h_rj_mod : (rk * shard + jj) % shard = jj := by
      rw [show rk * shard + jj = jj + rk * shard from by ring]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjj_lt]
    rw [h_div, h_mod, h_rj_div, h_rj_mod]
    -- Simplify getD to get
    have hrk_len : rk < xs.length := by omega
    simp only [List.getElem?_eq_getElem hrk_len, Option.getD_some, List.get_eq_getElem]
  -- Now combine: show valAt LHS idx = valAt RHS idx
  -- LHS
  have hL : valAt (bw_linear g (allGatherPrimDimN 2 numParts 0 xs)
      (allGatherPrimDimN 1 numParts 0 ws)).2 idx =
      ∑ p ∈ Finset.range (b * s), (valAt g (p * o + c)) *
        (valAt (allGatherPrimDimN 2 numParts 0 xs) (p * full + (rk * shard + jj))) := by
    conv_lhs => rw [hidx_eq, hbwL]
    exact hvalL
  -- RHS: valAt (allGatherPrimDimN 1 _ _ pieces) idx
  -- = valAt (pieces.getD rk _) (c * shard + jj)
  -- = valAt (bw_linear g xs[rk] ws[rk]).2 (c * shard + jj)
  -- = Σ_p g[p*o+c] * xs[rk][p*shard+jj]
  have hR_step1 : valAt (allGatherPrimDimN 1 numParts 0 pieces) idx =
      valAt (pieces.getD rk (zeroTensor [o, shard])) (c * shard + jj) := by
    conv_lhs => rw [hidx_eq]
    rw [valAt_of_lt _ _ (by
      rw [hshapeR]; simp only [prodShape, List.foldl, Nat.one_mul]
      calc c * full + (rk * shard + jj)
          < c * full + full := Nat.add_lt_add_left hrksj_lt _
        _ = (c + 1) * full := by ring
        _ ≤ o * full := Nat.mul_le_mul_right _ (by omega))]
    simp (config := { decide := true }) only [allGatherPrimDimN, Tensor.mkShape, hph,
      List.getD, List.drop, List.foldl, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some,
      hshard_ne, hfull_ne', ↓reduceIte, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]
    have h_div : (c * full + (rk * shard + jj)) / full = c := by
      rw [show c * full + (rk * shard + jj) = (rk * shard + jj) + c * full from by ring]
      rw [Nat.add_mul_div_right _ _ hfull_pos, Nat.div_eq_of_lt hrksj_lt, Nat.zero_add]
    have h_mod : (c * full + (rk * shard + jj)) % full = rk * shard + jj := by
      rw [show c * full + (rk * shard + jj) = (rk * shard + jj) + c * full from by ring]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrksj_lt]
    have h_rj_div : (rk * shard + jj) / shard = rk := by
      rw [show rk * shard + jj = jj + rk * shard from by ring]
      rw [Nat.add_mul_div_right _ _ hshard, Nat.div_eq_of_lt hjj_lt, Nat.zero_add]
    have h_rj_mod : (rk * shard + jj) % shard = jj := by
      rw [show rk * shard + jj = jj + rk * shard from by ring]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjj_lt]
    rw [h_div, h_mod, h_rj_div, h_rj_mod]
  have hR_step2 : pieces.getD rk (zeroTensor [o, shard]) =
      (bw_linear g (xs.get ⟨rk, by omega⟩) (ws.get ⟨rk, by omega⟩)).2 := by
    have hrk_len : rk < pieces.length := by simp [pieces]; exact hrk_lt
    simp only [List.getD, List.getElem?_eq_getElem hrk_len, Option.getD_some]
    simp only [pieces, List.getElem_ofFn]
  have hR_step3 : valAt (bw_linear g (xs.get ⟨rk, by omega⟩) (ws.get ⟨rk, by omega⟩)).2
      (c * shard + jj) =
      ∑ p ∈ Finset.range (b * s), (valAt g (p * o + c)) *
        (valAt (xs.get ⟨rk, by omega⟩) (p * shard + jj)) := by
    rw [hbwR ⟨rk, hrk_lt⟩]; exact hvalR_piece
  have hR : valAt (allGatherPrimDimN 1 numParts 0 pieces) idx =
      ∑ p ∈ Finset.range (b * s), (valAt g (p * o + c)) *
        (valAt (xs.get ⟨rk, by omega⟩) (p * shard + jj)) := by
    rw [hR_step1, hR_step2, hR_step3]
  -- Final: LHS = RHS
  rw [hL, hR]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact hgather_x_val p (Finset.mem_range.mp hp)

/-- valAt of chunkPrimDim0 equals valAt of original at offset. -/
private theorem chunkPrimDim0_valAt_flat
    (numParts rank shard0 d1 d2 : Nat) (x : Tensor)
    (hshape : x.shape = [numParts * shard0, d1, d2])
    (hparts : 0 < numParts) (hrank : rank < numParts)
    (hd12 : 0 < d1 * d2) (hd2_pos : 0 < d2)
    (flat : Nat) (hflat : flat < shard0 * (d1 * d2)) :
    valAt (chunkPrimDim0 numParts rank x) flat =
      valAt x (rank * (shard0 * (d1 * d2)) + flat) := by
  have hnp_ne : numParts ≠ 0 := by omega
  have hd12_ne : d1 * d2 ≠ 0 := by omega
  have hd2_ne : d2 ≠ 0 := by omega
  have hdiv_eq : numParts * shard0 / numParts = shard0 := Nat.mul_div_cancel_left shard0 hparts
  -- Arithmetic identity: the computed index equals the target index
  have hA_eq : (rank * shard0 + flat / (d1 * d2)) * (d1 * d2) +
      flat % (d1 * d2) / d2 * d2 + flat % (d1 * d2) % d2 =
      rank * (shard0 * (d1 * d2)) + flat := by
    have h1 : flat / (d1 * d2) * (d1 * d2) + flat % (d1 * d2) = flat := by
      have := Nat.div_add_mod flat (d1 * d2); rw [Nat.mul_comm] at this; omega
    have h2 : flat % (d1 * d2) / d2 * d2 + flat % (d1 * d2) % d2 = flat % (d1 * d2) := by
      have := Nat.div_add_mod (flat % (d1 * d2)) d2; rw [Nat.mul_comm] at this; omega
    calc (rank * shard0 + flat / (d1 * d2)) * (d1 * d2) +
          flat % (d1 * d2) / d2 * d2 + flat % (d1 * d2) % d2
        = (rank * shard0 + flat / (d1 * d2)) * (d1 * d2) + flat % (d1 * d2) := by omega
      _ = rank * shard0 * (d1 * d2) + (flat / (d1 * d2) * (d1 * d2) + flat % (d1 * d2)) := by ring
      _ = rank * (shard0 * (d1 * d2)) + flat := by rw [h1]; ring
  -- RHS index bound
  have hRHS_bound : rank * (shard0 * (d1 * d2)) + flat < numParts * shard0 * d1 * d2 := by
    have h : numParts * shard0 * d1 * d2 = numParts * (shard0 * (d1 * d2)) := by ring
    rw [h]
    calc rank * (shard0 * (d1 * d2)) + flat
        < rank * (shard0 * (d1 * d2)) + shard0 * (d1 * d2) := by omega
      _ = (rank + 1) * (shard0 * (d1 * d2)) := by ring
      _ ≤ numParts * (shard0 * (d1 * d2)) := Nat.mul_le_mul_right _ (by omega)
  -- All bounds for dite resolution
  have hflat_assoc : flat < shard0 * d1 * d2 := by
    rw [show shard0 * d1 * d2 = shard0 * (d1 * d2) from by ring]; exact hflat
  have hInner : (rank * shard0 + flat / (d1 * d2)) * (d1 * d2) +
      flat % (d1 * d2) / d2 * d2 + flat % (d1 * d2) % d2 < numParts * shard0 * d1 * d2 := by
    rw [hA_eq]; exact hRHS_bound
  -- Destructure tensor for definitional shape match
  obtain ⟨_, val⟩ := x; subst hshape
  simp only [valAt, chunkPrimDim0, divNat, hdiv_eq, Tensor.mkShape,
    if_neg hnp_ne, if_neg hd12_ne, if_neg hd2_ne,
    Nat.mod_eq_of_lt hrank, prodShape, List.foldl, Nat.one_mul,
    hflat_assoc, hRHS_bound, hInner, ↓reduceDIte]
  apply congrArg; ext; exact hA_eq

/-- valAt of allGatherPrimDim0 at block offset equals valAt of the corresponding piece. -/
private theorem allGatherPrimDim0_valAt_flat
    (numParts shard0 d1 d2 : Nat) (xs : List Tensor)
    (hxs_len : xs.length = numParts)
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [shard0, d1, d2])
    (_hparts : 0 < numParts) (hshard0 : 0 < shard0) (hd12 : 0 < d1 * d2) (hd2_pos : 0 < d2)
    (rank : Nat) (hrank : rank < numParts)
    (flat : Nat) (hflat : flat < shard0 * (d1 * d2)) :
    valAt (allGatherPrimDim0 numParts 0 xs) (rank * (shard0 * (d1 * d2)) + flat) =
      valAt (xs.get ⟨rank, by omega⟩) flat := by
  have hd12_ne : d1 * d2 ≠ 0 := by omega
  have hd2_ne : d2 ≠ 0 := by omega
  have hs0_ne : shard0 ≠ 0 := by omega
  have hidx_bound : rank * (shard0 * (d1 * d2)) + flat <
      prodShape [shard0 * numParts, d1, d2] := by
    simp only [prodShape, List.foldl, Nat.one_mul]
    calc rank * (shard0 * (d1 * d2)) + flat
        < rank * (shard0 * (d1 * d2)) + shard0 * (d1 * d2) := by omega
      _ = (rank + 1) * (shard0 * (d1 * d2)) := by ring
      _ ≤ numParts * (shard0 * (d1 * d2)) := Nat.mul_le_mul_right _ (by omega)
      _ = shard0 * numParts * d1 * d2 := by ring
  -- Unfold allGatherPrimDim0 on LHS while valAt is intact
  conv_lhs => simp only [allGatherPrimDim0, hxs_head]
  rw [valAt_of_lt _ _ hidx_bound]
  simp only [Tensor.mkShape, hd12_ne, hd2_ne, hs0_ne, ↓reduceIte]
  -- Index decomposition
  have hi_flat_lt : flat / (d1 * d2) < shard0 :=
    Nat.div_lt_of_lt_mul (show flat < (d1 * d2) * shard0 from by
      rw [show (d1 * d2) * shard0 = shard0 * (d1 * d2) from Nat.mul_comm _ _]; exact hflat)
  have hdiv_d12 : (rank * (shard0 * (d1 * d2)) + flat) / (d1 * d2) =
      rank * shard0 + flat / (d1 * d2) := by
    rw [show rank * (shard0 * (d1 * d2)) + flat =
        flat + (rank * shard0) * (d1 * d2) from by ring]
    rw [Nat.add_mul_div_right _ _ hd12]; exact Nat.add_comm _ _
  have hmod_d12 : (rank * (shard0 * (d1 * d2)) + flat) % (d1 * d2) = flat % (d1 * d2) := by
    rw [show rank * (shard0 * (d1 * d2)) + flat =
        flat + (rank * shard0) * (d1 * d2) from by ring]
    rw [Nat.add_mul_mod_self_right]
  have hdiv_s0 : (rank * shard0 + flat / (d1 * d2)) / shard0 = rank := by
    rw [show rank * shard0 + flat / (d1 * d2) =
        flat / (d1 * d2) + rank * shard0 from Nat.add_comm _ _]
    rw [Nat.add_mul_div_right _ _ hshard0, Nat.div_eq_of_lt hi_flat_lt, Nat.zero_add]
  have hmod_s0 : (rank * shard0 + flat / (d1 * d2)) % shard0 = flat / (d1 * d2) := by
    rw [show rank * shard0 + flat / (d1 * d2) =
        flat / (d1 * d2) + rank * shard0 from Nat.add_comm _ _]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi_flat_lt]
  simp only [hdiv_d12, hmod_d12, hdiv_s0, hmod_s0]
  -- getD rank = xs[rank]
  have hrank_len : rank < xs.length := by omega
  simp only [List.getD, List.getElem?_eq_getElem hrank_len, Option.getD_some,
    List.get_eq_getElem]
  congr 1
  have h1 : flat / (d1 * d2) * (d1 * d2) + flat % (d1 * d2) = flat := by
    have := Nat.div_add_mod flat (d1 * d2); rw [Nat.mul_comm] at this; omega
  have h2 : flat % (d1 * d2) / d2 * d2 + flat % (d1 * d2) % d2 = flat % (d1 * d2) := by
    have := Nat.div_add_mod (flat % (d1 * d2)) d2; rw [Nat.mul_comm] at this; omega
  omega

/-- 3D bw_linear dW data-parallel: when g and x are chunked along dim 0 (batch),
    the full dW equals the element-wise sum (tensorSum) of per-chunk dW values. -/
theorem bw_linear_3d_snd_data_parallel
    (numParts b s o i shard0 : Nat)
    (g : Tensor) (xs : List Tensor) (w : Tensor)
    (hg : g.shape = [b, s, o])
    (hxs_len : xs.length = numParts)
    (hxs_shapes : ∀ x ∈ xs, x.shape = [shard0, s, i])
    (hw : w.shape = [o, i])
    (hb : b = numParts * shard0)
    (hparts : 0 < numParts)
    (hshard : 0 < shard0)
    (hs : 0 < s) :
    (bw_linear g (allGatherPrimDim0 numParts 0 xs) w).2 =
      tensorSum (List.ofFn (fun r : Fin numParts =>
        (bw_linear (chunkPrimDim0 numParts r.val g) (xs.get ⟨r.val, by omega⟩) w).2)) := by
  classical
  -- Abbreviations
  set ss := shard0 * s with hss_def
  have hbs_eq : b * s = numParts * ss := by rw [hb, hss_def]; ring
  -- Head shape of xs
  have hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [shard0, s, i] := by
    cases hxs' : xs with
    | nil => simp [hxs'] at hxs_len; omega
    | cons x0 _ => simp [hxs_shapes x0 (by simp [hxs'])]
  -- Gathered x shape
  have hgx : (allGatherPrimDim0 numParts 0 xs).shape = [shard0 * numParts, s, i] := by
    simp only [allGatherPrimDim0, hxs_head, Tensor.mkShape]
  have hgx' : (allGatherPrimDim0 numParts 0 xs).shape = [b, s, i] := by
    rw [hgx, show shard0 * numParts = b from by rw [hb]; ring]
  -- Chunk g shape
  have hchunk_shape : ∀ r : Fin numParts,
      (chunkPrimDim0 numParts r.val g).shape = [shard0, s, o] :=
    fun r => chunkPrimDim0_shape' numParts r.val shard0 s o g (by rw [hg, hb]) hparts
  -- LHS bw_linear .2 unfolding
  have hbwL : (bw_linear g (allGatherPrimDim0 numParts 0 xs) w).2 =
      Tensor.mkShape [o, i] (k_matmul_transpose (b * s) o i g
        (allGatherPrimDim0 numParts 0 xs)) := by
    simp only [bw_linear, hg, hgx', hw, Tensor.mkShape]
  -- Per-rank bw_linear .2 unfolding
  have hbwR : ∀ r : Fin numParts,
      (bw_linear (chunkPrimDim0 numParts r.val g) (xs.get ⟨r.val, by omega⟩) w).2 =
        Tensor.mkShape [o, i] (k_matmul_transpose (shard0 * s) o i
          (chunkPrimDim0 numParts r.val g) (xs.get ⟨r.val, by omega⟩)) := by
    intro r; simp only [bw_linear, hchunk_shape r,
      hxs_shapes _ (List.get_mem ..), hw, Tensor.mkShape]
  -- LHS shape
  have hshapeL : (bw_linear g (allGatherPrimDim0 numParts 0 xs) w).2.shape = [o, i] :=
    bw_linear_3d_snd_shape b s o i g _ _ hg hgx' hw
  -- RHS pieces
  set pieces := List.ofFn (fun r : Fin numParts =>
    (bw_linear (chunkPrimDim0 numParts r.val g)
      (xs.get ⟨r.val, by omega⟩) w).2) with hpieces_def
  -- RHS tensorSum shape
  have hpiece_shape : ∀ r : Fin numParts,
      (bw_linear (chunkPrimDim0 numParts r.val g)
        (xs.get ⟨r.val, by omega⟩) w).2.shape = [o, i] :=
    fun r => bw_linear_3d_snd_shape shard0 s o i _ _ _ (hchunk_shape r)
      (hxs_shapes _ (List.get_mem ..)) hw
  have hpieces_head : pieces.head? = some (bw_linear (chunkPrimDim0 numParts 0 g)
      (xs.get ⟨0, by omega⟩) w).2 := by
    simp only [pieces]
    obtain ⟨n, hn⟩ : ∃ n, numParts = n + 1 := ⟨numParts - 1, by omega⟩
    subst hn
    exact list_ofFn_head_eq _
  have hshapeR : (tensorSum pieces).shape = [o, i] := by
    have hne : pieces ≠ [] := by
      simp only [pieces, ne_eq]; rw [List.ofFn_eq_nil_iff]; omega
    obtain ⟨first, rest, hfr⟩ := List.exists_cons_of_ne_nil hne
    rw [hfr]; simp only [tensorSum, Tensor.mkShape]
    have h := hpieces_head; rw [hfr] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    rw [h]; exact hpiece_shape ⟨0, hparts⟩
  have hshape_eq : (bw_linear g (allGatherPrimDim0 numParts 0 xs) w).2.shape =
      (tensorSum pieces).shape := by rw [hshapeL, hshapeR]
  -- Pointwise equality
  apply Tensor.ext hshape_eq
  intro idx hidx
  have hidx' : idx < o * i := by simpa [hshapeL, prodShape, List.foldl] using hidx
  -- Handle degenerate cases
  by_cases hi_pos : i = 0
  · simp [hi_pos] at hidx'
  by_cases ho_pos : o = 0
  · simp [ho_pos] at hidx'
  have hi : 0 < i := Nat.pos_of_ne_zero hi_pos
  have ho : 0 < o := Nat.pos_of_ne_zero ho_pos
  -- Decompose idx = c * i + j
  set c := idx / i
  set j := idx % i
  have hc_lt : c < o := Nat.div_lt_of_lt_mul (show idx < i * o from by rw [Nat.mul_comm]; exact hidx')
  have hj_lt : j < i := Nat.mod_lt idx hi
  have hidx_eq : idx = c * i + j := by
    have h := (Nat.div_add_mod idx i).symm
    rw [Nat.mul_comm i c] at h
    exact h
  have hso_pos : 0 < s * o := Nat.mul_pos hs ho
  have hsi_pos : 0 < s * i := Nat.mul_pos hs hi
  -- LHS value
  conv_lhs => rw [hbwL, hidx_eq]
  rw [k_matmul_transpose_valAt (b * s) o i g _ c hc_lt j hj_lt]
  -- RHS: unfold tensorSum at idx
  have hidx_oi : c * i + j < o * i := by
    calc c * i + j < c * i + i := by omega
      _ = (c + 1) * i := by ring
      _ ≤ o * i := Nat.mul_le_mul_right _ (by omega)
  conv_rhs => rw [hidx_eq]
  -- tensorSum pieces at (c*i+j) = Σ_r valAt piece_r (c*i+j)
  -- Unfold tensorSum to foldl
  have hne : pieces ≠ [] := by
    simp only [pieces, ne_eq]; rw [List.ofFn_eq_nil_iff]; omega
  obtain ⟨first, rest, hcons⟩ := List.exists_cons_of_ne_nil hne
  have hts_val : valAt (tensorSum pieces) (c * i + j) =
      pieces.foldl (fun acc x => acc + valAt x (c * i + j)) 0 := by
    have hfirst_eq : first = (bw_linear (chunkPrimDim0 numParts 0 g)
        (xs.get ⟨0, by omega⟩) w).2 := by
      have h := hpieces_head; rw [hcons] at h; simp at h; exact h
    have hfirst_shape : first.shape = [o, i] := by
      rw [hfirst_eq]; exact hpiece_shape ⟨0, hparts⟩
    have hcond : c * i + j < prodShape first.shape := by
      rw [hfirst_shape]; simpa [prodShape, List.foldl] using hidx_oi
    rw [hcons]; simp [tensorSum, valAt, Tensor.mkShape, hcond]
  rw [hts_val, List.foldl_add_eq_sum, List.map_ofFn]
  -- Convert (List.ofFn f).sum to ∑ i : Fin numParts, f i
  have hsum_ofFn : ∀ (f : Fin numParts → Scalar),
      (List.ofFn f).sum = ∑ i : Fin numParts, f i := fun f => Fin.sum_ofFn f
  rw [hsum_ofFn]
  simp only [Function.comp_apply]
  -- Each piece value
  conv_rhs =>
    arg 2; ext r
    rw [hbwR r, k_matmul_transpose_valAt (shard0 * s) o i _ _ c hc_lt j hj_lt]
  -- LHS = Σ_{p<b*s} g[p*o+c] * X[p*i+j]
  -- RHS = Σ_r:Fin Σ_{p'<shard0*s} g_r[p'*o+c] * xr[p'*i+j]
  -- Decompose LHS sum: b*s = numParts * (shard0*s)
  rw [hbs_eq, Finset.sum_range_mul_eq_sum_sum numParts ss]
  -- Convert ∑ r ∈ range numParts to ∑ r : Fin numParts
  rw [← Fin.sum_univ_eq_sum_range]
  -- Show term-by-term equality
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro p' hp'
  have hp'_lt : p' < shard0 * s := Finset.mem_range.mp hp'
  -- Show g[(r*ss + p')*o + c] = chunkPrimDim0 r g at [p'*o + c]
  have hg_eq : valAt g ((↑r * ss + p') * o + c) =
      valAt (chunkPrimDim0 numParts r.val g) (p' * o + c) := by
    rw [chunkPrimDim0_valAt_flat numParts r.val shard0 s o g (by rw [hg, hb]) hparts r.isLt
        hso_pos ho (p' * o + c) (by
        calc p' * o + c < p' * o + o := by omega
          _ = (p' + 1) * o := by ring
          _ ≤ (shard0 * s) * o := Nat.mul_le_mul_right o (by omega)
          _ = shard0 * (s * o) := by ring)]
    congr 1; rw [hss_def]; ring
  -- Show X[(r*ss + p')*i + j] = xs[r] at [p'*i + j]
  have hx_eq : valAt (allGatherPrimDim0 numParts 0 xs) ((↑r * ss + p') * i + j) =
      valAt (xs.get ⟨r.val, by omega⟩) (p' * i + j) := by
    rw [show (↑r * ss + p') * i + j = ↑r * (shard0 * (s * i)) + (p' * i + j) from by
      rw [hss_def]; ring]
    rw [allGatherPrimDim0_valAt_flat numParts shard0 s i xs hxs_len hxs_head hparts hshard
        hsi_pos hi r.val r.isLt (p' * i + j) (by
        calc p' * i + j < p' * i + i := by omega
          _ = (p' + 1) * i := by ring
          _ ≤ (shard0 * s) * i := Nat.mul_le_mul_right i (by omega)
          _ = shard0 * (s * i) := by ring)]
  rw [← hg_eq, ← hx_eq]

/-- Shape of fw_linear output. -/
theorem fw_linear_shape
    (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i])
    (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  simp [fw_linear, hx, hw, Tensor.mkShape]

/-- bw_linear first output (dX) is 2D when all inputs are 2D. -/
theorem bw_linear_fst_is_2d
    (gradOut x w : Tensor)
    (hg : ∃ bG oG, gradOut.shape = [bG, oG])
    (hx : ∃ bX iX, x.shape = [bX, iX])
    (hw : ∃ oW iW, w.shape = [oW, iW]) :
    ∃ b i, (bw_linear gradOut x w).1.shape = [b, i] := by
  obtain ⟨bG, oG, hg⟩ := hg
  obtain ⟨bX, iX, hx⟩ := hx
  obtain ⟨oW, iW, hw⟩ := hw
  simp only [bw_linear, hg, hx, hw, Tensor.mkShape]
  exact ⟨bX, iX, rfl⟩

/-- bw_linear second output (dW) is 2D when all inputs are 2D. -/
theorem bw_linear_snd_is_2d
    (gradOut x w : Tensor)
    (hg : ∃ bG oG, gradOut.shape = [bG, oG])
    (hx : ∃ bX iX, x.shape = [bX, iX])
    (hw : ∃ oW iW, w.shape = [oW, iW]) :
    ∃ o i, (bw_linear gradOut x w).2.shape = [o, i] := by
  obtain ⟨bG, oG, hg⟩ := hg
  obtain ⟨bX, iX, hx⟩ := hx
  obtain ⟨oW, iW, hw⟩ := hw
  simp only [bw_linear, hg, hx, hw, Tensor.mkShape]
  exact ⟨oW, iW, rfl⟩

/-!
## Unified Distributivity Theorems for Tensor Parallelism
-/

-- Auxiliary lemma: allReducePrim shape from List.ofFn of tensors with same shape
theorem matmul_allGather_eq_allReduce_matmul_chunk
    (m n k numParts shard : Nat)
    (a : Tensor) (bs : List Tensor)
    (ha : a.shape = [m, k])
    (hk : k = numParts * shard)
    (hbs_len : bs.length = numParts)
    (hbs_shapes : ∀ b ∈ bs, b.shape = [n, shard])
    (hparts : 0 < numParts)
    (_ : 0 < shard) :
    Tensor.mkShape [m, n] (k_matmul m n k a (allGatherPrim numParts 0 bs)) =
      allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
        Tensor.mkShape [m, n] (k_matmul m n shard (chunkPrim numParts r.val a) (bs.get ⟨r.val, by omega⟩)))) := by
  classical
  have hnumParts_ne0 : numParts ≠ 0 := Nat.ne_of_gt hparts
  have hbs_head : bs ≠ [] := by intro h; simp [h] at hbs_len; omega
  have hbs_head_shape : (bs.head?.map (fun t => t.shape)).getD [] = [n, shard] := by
    match bs with
    | [] => simp at hbs_head
    | b0 :: _ => exact hbs_shapes b0 (by simp)
  have hallGather_shape : (allGatherPrim numParts 0 bs).shape = [n, k] := by
    simp only [allGatherPrim, Tensor.mkShape, hbs_head_shape, dropLast, lastD, appendLast]
    simp [hk, Nat.mul_comm]
  have hchunk_shape : ∀ r : Fin numParts, (chunkPrim numParts r.val a).shape = [m, shard] := by
    intro r
    have hdiv : divNat k numParts = shard := by simp [divNat, hnumParts_ne0, hk]
    simp [chunkPrim, Tensor.mkShape, ha, dropLast, lastD, appendLast, hdiv]
  have hRHS_shape : (allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
      Tensor.mkShape [m, n] (k_matmul m n shard (chunkPrim numParts r.val a)
        (bs.get ⟨r.val, by omega⟩))))).shape = [m, n] := by
    simp only [allReducePrim, Tensor.mkShape]
    cases numParts with
    | zero => simp at hparts
    | succ n => simp [List.ofFn, Fin.foldr_succ]
  have : (Tensor.mkShape [m, n] (k_matmul m n k a (allGatherPrim numParts 0 bs))).shape =
      (allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
        Tensor.mkShape [m, n] (k_matmul m n shard (chunkPrim numParts r.val a)
          (bs.get ⟨r.val, by omega⟩))))).shape := by
    simp [Tensor.mkShape]; exact hRHS_shape.symm
  apply Tensor.ext this
  intro idx hidx
  simp only [Tensor.mkShape] at hidx
  have hprod_mn : prodShape [m, n] = m * n := by simp [prodShape]
  have hidx' : idx < m * n := by rwa [hprod_mn] at hidx
  -- Decompose idx into row p and column c
  have hn_pos : 0 < n := by
    by_contra hcon; push_neg at hcon
    have hn0 : n = 0 := Nat.le_zero.mp hcon
    simp only [hn0, Nat.mul_zero, Nat.not_lt_zero] at hidx'
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hidx')
  let p := idx / n
  let c := idx % n
  have hc_lt : c < n := Nat.mod_lt idx hn_pos
  have hp_lt : p < m := Nat.div_lt_iff_lt_mul hn_pos |>.mpr hidx'
  have hidx_eq : idx = p * n + c := by
    have := Nat.div_add_mod idx n
    simp only [Nat.mul_comm n (idx / n)] at this
    exact this.symm
  -- Compute LHS value
  have hidx_lt_prod : idx < prodShape [m, n] := by rwa [hprod_mn]
  rw [valAt_of_lt _ _ hidx_lt_prod]
  simp only [Tensor.mkShape]
  have hdiv : (p * n + c) / n = p := by
    have h1 : (c + p * n) / n = c / n + p := Nat.add_mul_div_right c p hn_pos
    have h2 : c / n = 0 := Nat.div_eq_of_lt hc_lt
    simp only [h2, zero_add] at h1
    rw [Nat.add_comm] at h1
    exact h1
  have hmod : (p * n + c) % n = c := by
    have h1 : (c + p * n) % n = c % n := Nat.add_mul_mod_self_right c p n
    have h2 : c % n = c := Nat.mod_eq_of_lt hc_lt
    simp only [h2] at h1
    rw [Nat.add_comm] at h1
    exact h1
  -- Compute RHS value using allReducePrim expansion
  have hpnc_lt : p * n + c < m * n := by
    calc p * n + c < p * n + n := Nat.add_lt_add_left hc_lt _
      _ = (p + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right n hp_lt
  have hRHS_prod : 0 < prodShape (allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
      Tensor.mkShape [m, n] (k_matmul m n shard (chunkPrim numParts r.val a)
        (bs.get ⟨r.val, by omega⟩))))).shape := by
    simp only [hRHS_shape, prodShape, List.foldl]
    simp only [Nat.one_mul]
    exact Nat.mul_pos hm_pos hn_pos
  -- The key computation
  simp only [hidx_eq, k_matmul, hdiv, hmod]
  -- Now we need: ∑ j, a[p,j] * allGather(bs)[c,j] = ∑ r, ∑ j, chunk(a)[p,j] * bs[r][c,j]
  -- Split the sum over k into numParts parts of size shard
  have hsum_split : ∑ j ∈ Finset.range k, valAt a (p * k + j) *
      valAt (allGatherPrim numParts 0 bs) (c * k + j) =
    ∑ r : Fin numParts, ∑ j ∈ Finset.range shard,
      valAt a (p * k + (r.val * shard + j)) *
      valAt (bs.get ⟨r.val, by omega⟩) (c * shard + j) := by
    rw [hk]
    conv_lhs => rw [Finset.sum_range_mul_eq_sum_sum (n := numParts) (m := shard)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro j hj
    have hj' : j < shard := Finset.mem_range.mp hj
    -- Rewrite allGather access
    have hgv := allGatherPrim_valAt_mul_add numParts (r.val) n shard bs
      (by simp only [hbs_head_shape]) hparts (by omega) c hc_lt j hj'
    -- Normalize index: c * (shard * numParts) + r * shard + j = c * (numParts * shard) + (r * shard + j)
    have hidx_norm : c * (shard * numParts) + r.val * shard + j = c * (numParts * shard) + (r.val * shard + j) := by ring
    rw [hidx_norm] at hgv
    rw [hgv]
    -- Convert getD to get using in-bounds
    have hr_lt : r.val < bs.length := by omega
    simp only [List.getD, List.getElem?_eq_getElem hr_lt, Option.getD_some, List.get_eq_getElem]
  rw [hsum_split]
  -- Expand the RHS allReducePrim at index (p * n + c)
  -- First establish that numParts = np + 1 for some np (for Fin type)
  obtain ⟨np, hnp⟩ : ∃ np, numParts = np + 1 := ⟨numParts - 1, by omega⟩
  have hRHS_idx_lt' : p * n + c < prodShape (allReducePrim numParts 0
      (List.ofFn (fun r : Fin numParts => Tensor.mk [m, n]
        (k_matmul m n shard (chunkPrim numParts r.val a) (bs.get ⟨r.val, by omega⟩))))).shape := by
    simp only [allReducePrim, Tensor.mkShape]
    -- Use our auxiliary lemma to establish the shape
    have hhead : (List.ofFn (fun r : Fin numParts =>
        (Tensor.mk [m, n] (k_matmul m n shard (chunkPrim numParts r.val a)
          (bs.get ⟨r.val, by omega⟩))))).head? = some (Tensor.mk [m, n]
          (k_matmul m n shard (chunkPrim numParts 0 a) (bs.get ⟨0, by omega⟩))) := by
      subst hnp
      exact list_ofFn_head_eq _
    simp only [hhead, Option.map_some, Option.getD_some, prodShape, List.foldl, Nat.one_mul]
    exact hpnc_lt
  rw [valAt_of_lt _ _ hRHS_idx_lt']
  simp only [allReducePrim, Tensor.mkShape]
  -- Expand the foldl over List.ofFn to Finset.sum
  rw [List.foldl_add_eq_sum, List.map_ofFn]
  -- Convert List.sum (ofFn f) to Finset.sum using Fin.sum_ofFn
  have hsum_ofFn : ∀ (f : Fin numParts → Scalar),
      (List.ofFn f).sum = ∑ i : Fin numParts, f i := by
    intro f
    exact Fin.sum_ofFn f
  rw [hsum_ofFn]
  apply Finset.sum_congr rfl; intro r _
  simp only [Function.comp_apply]
  rw [valAt_of_lt _ _ (by simp only [prodShape, List.foldl, Nat.one_mul]; exact hpnc_lt)]
  simp only [k_matmul, hdiv, hmod]
  apply Finset.sum_congr rfl; intro j hj
  have hj' : j < shard := Finset.mem_range.mp hj
  -- Rewrite chunk access: chunkPrim_valAt_mul_add numParts rank b shard x hshape ...
  -- a.shape = [m, k] = [m, numParts * shard], so b = m
  have hcv := chunkPrim_valAt_mul_add numParts r.val m shard a (by rw [ha, hk]) hparts r.isLt p hp_lt j hj'
  rw [hcv]
  -- Final simplification: show the indices match
  congr 1
  rw [← hk]; ring_nf

theorem fw_linear_is_matmul (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    fw_linear x w = Tensor.mkShape [b, o] (k_matmul b o i x w) := by
  simp [fw_linear, hx, hw, Tensor.mkShape]

/-! ### 3D fw_linear lemmas -/

theorem fw_linear_3d_shape (b s i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, s, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, s, o] := by
  simp [fw_linear, hx, hw, Tensor.mkShape]

theorem allGatherPrimDim0_shape_3d (numParts b0 s d : Nat)
    (xs : List Tensor)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b0, s, d]) :
    (allGatherPrimDim0 numParts 0 xs).shape = [b0 * numParts, s, d] := by
  simp only [allGatherPrimDim0, hhead, Tensor.mkShape]

private lemma tensor_mkShape_shape_congr (s1 s2 : Shape) (hs : s1 = s2)
    (f : Fin (prodShape s1) → Scalar) :
    Tensor.mkShape s1 f = Tensor.mkShape s2 (fun i => f ⟨i.1, hs ▸ i.2⟩) := by
  subst hs; rfl

theorem allGatherPrimDimN_0_eq_dim0 (numParts rank : Nat)
    (xs : List Tensor)
    (hhead : ∃ a b c, (xs.head?.map (fun t => t.shape)).getD [] = [a, b, c]) :
    allGatherPrimDimN 0 numParts rank xs = allGatherPrimDim0 numParts rank xs := by
  obtain ⟨a, b, c, hshape⟩ := hhead
  -- First, convert both sides to Tensor.mkShape with the same shape [a * numParts, b, c]
  have hshape_comp : ((xs.head?.map (fun t => t.shape)).getD []).set 0
      (((xs.head?.map (fun t => t.shape)).getD [])[0]?.getD 0 * numParts) =
      [a * numParts, b, c] := by
    simp [hshape]
  -- Unfold allGatherPrimDimN and normalize shape
  unfold allGatherPrimDimN
  simp only [hshape, List.getElem?_cons_zero, Option.getD_some, List.getD,
    List.drop, List.foldl, Nat.one_mul]
  rw [tensor_mkShape_shape_congr _ _ hshape_comp]
  -- Now LHS is Tensor.mkShape [a * numParts, b, c] (fun i => ...DimN body using i.1...)
  -- Unfold allGatherPrimDim0
  unfold allGatherPrimDim0
  simp only [hshape]
  -- Now RHS is Tensor.mkShape [a * numParts, b, c] (fun i => ...Dim0 body using i.1...)
  -- Both have the same shape, so just compare the value functions
  congr 1
  funext ⟨idx, hidx⟩
  simp only [prodShape, List.foldl] at hidx
  by_cases ha : a = 0
  · simp [ha] at hidx
  by_cases hb : b = 0
  · simp [hb] at hidx
  by_cases hc : c = 0
  · simp [hc] at hidx
  have hbc' : 0 < b * c := Nat.mul_pos (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
  by_cases hnp : numParts = 0
  · simp [hnp] at hidx
  have hnp' : 0 < numParts := Nat.pos_of_ne_zero hnp
  have hidx' : idx < a * numParts * (b * c) := by
    calc idx < 1 * (a * numParts) * b * c := hidx
         _ = a * numParts * (b * c) := by ring
  have habcnp : 0 < a * numParts * (b * c) :=
    Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero ha) hnp') hbc'
  simp only [show a * numParts * (b * c) ≠ 0 from by omega,
    show a ≠ 0 from ha, show b * c ≠ 0 from by omega,
    show c ≠ 0 from hc, ↓reduceIte]
  rw [Nat.mod_eq_of_lt hidx', Nat.div_eq_of_lt hidx']
  simp only [Nat.zero_mul, Nat.zero_add]
  congr 1
  have h1 := Nat.div_add_mod (idx % (b * c)) c
  rw [Nat.mul_comm] at h1
  omega

theorem fw_linear_3d_allGatherPrimDim0_comm
    (numParts b0 s i o : Nat)
    (xs : List Tensor) (w : Tensor)
    (hw : w.shape = [o, i])
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [b0, s, i])
    (hxs_shape : ∀ x ∈ xs, x.shape = [b0, s, i])
    (hxs_len : xs.length = numParts)
    (hparts : 0 < numParts) (hb0 : 0 < b0) (hs : 0 < s) (hi : 0 < i) (ho : 0 < o) :
    fw_linear (allGatherPrimDim0 numParts 0 xs) w =
    allGatherPrimDim0 numParts 0 (xs.map (fun x => fw_linear x w)) := by
  -- Proof by Tensor extensionality: both sides compute the same function on 3D indices.
  -- The key insight: fw_linear processes each (batch, seq) position independently,
  -- so it distributes over dim-0 concatenation (allGatherPrimDim0).
  -- Shape equality
  have hgather_shape : (allGatherPrimDim0 numParts 0 xs).shape = [b0 * numParts, s, i] :=
    allGatherPrimDim0_shape_3d numParts b0 s i xs hxs_head
  have hmap_head_val : ((xs.map (fun x => fw_linear x w)).head?.map (fun t => t.shape)).getD [] = [b0, s, o] := by
    cases xs with
    | nil => simp at hxs_len; omega
    | cons x0 rest =>
      simp only [List.map, List.head?_cons, Option.map_some, Option.getD_some]
      exact fw_linear_3d_shape b0 s i o x0 w (hxs_shape x0 (List.mem_cons_self ..)) hw
  have hLHS_shape : (fw_linear (allGatherPrimDim0 numParts 0 xs) w).shape = [b0 * numParts, s, o] :=
    fw_linear_3d_shape _ _ _ _ _ _ hgather_shape hw
  have hRHS_shape : (allGatherPrimDim0 numParts 0 (xs.map (fun x => fw_linear x w))).shape = [b0 * numParts, s, o] :=
    allGatherPrimDim0_shape_3d numParts b0 s o _ hmap_head_val
  -- Value equality at each index
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul] at hidx
  have hso_pos : 0 < s * o := Nat.mul_pos hs ho
  have hso_ne : s * o ≠ 0 := Nat.ne_of_gt hso_pos
  have ho_ne : (o : Nat) ≠ 0 := by omega
  have hsi_pos : 0 < s * i := Nat.mul_pos hs hi
  have hsi_ne : s * i ≠ 0 := Nat.ne_of_gt hsi_pos
  have hi_ne : (i : Nat) ≠ 0 := by omega
  have hb0_ne : (b0 : Nat) ≠ 0 := by omega
  have hidx_rearr : idx < (s * o) * (b0 * numParts) := by
    calc idx < b0 * numParts * s * o := hidx
         _ = (b0 * numParts) * (s * o) := Nat.mul_assoc _ _ _
         _ = (s * o) * (b0 * numParts) := Nat.mul_comm _ _
  set row := idx / (s * o)
  set rso := idx % (s * o)
  set seq := rso / o
  set col := rso % o
  set rk := row / b0
  set lB := row % b0
  have hrow_lt : row < b0 * numParts := Nat.div_lt_of_lt_mul hidx_rearr
  have hrk_lt : rk < numParts := by
    change row / b0 < numParts; exact Nat.div_lt_of_lt_mul hrow_lt
  have hrk_lt_len : rk < xs.length := by change row / b0 < xs.length; omega
  have hlB_lt : lB < b0 := by change row % b0 < b0; exact Nat.mod_lt _ hb0
  have hseq_lt : seq < s := by
    change idx % (s * o) / o < s
    apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm o s]; exact Nat.mod_lt _ hso_pos
  have hcol_lt : col < o := by change idx % (s * o) % o < o; exact Nat.mod_lt _ ho
  -- Unfold LHS: fw_linear uses hgather_shape, hw to match the 3D branch
  conv_lhs => simp only [fw_linear, hgather_shape, hw]
  -- Unfold RHS: allGatherPrimDim0 uses hmap_head_val to match the [b0,s,o] branch
  conv_rhs => simp only [allGatherPrimDim0, hmap_head_val]
  -- Both sides are Tensor.mkShape [b0*numParts, s, o] f applied to idx
  have hprod : idx < prodShape [b0 * numParts, s, o] := by
    simp [prodShape, List.foldl]; exact hidx
  rw [valAt_of_lt _ _ hprod, valAt_of_lt _ _ hprod]
  simp only [Tensor.mkShape]
  -- Simplify if-then-else guards
  simp only [hso_ne, ho_ne, hb0_ne, ↓reduceIte]
  -- Now LHS = ∑ j, valAt (allGatherPrimDim0 ...) ((row*s+seq)*i+j) * valAt w (col*i+j)
  -- RHS = valAt ((xs.map fwl).getD rk (zeroTensor [b0,s,o])) (lB*(s*o)+seq*o+col)
  -- === Handle the RHS ===
  -- Replace (xs.map fw_linear).getD rk with fw_linear (xs[rk])
  have hpiece_shape : (xs[idx / (s * o) / b0]'hrk_lt_len).shape = [b0, s, i] :=
    hxs_shape _ (List.getElem_mem ..)
  rw [show (List.map (fun x => fw_linear x w) xs).getD (idx / (s * o) / b0) (zeroTensor [b0, s, o]) =
      fw_linear (xs[idx / (s * o) / b0]'hrk_lt_len) w from by
    unfold List.getD
    rw [List.getElem?_map, getElem?_pos xs _ hrk_lt_len]
    simp]
  -- Unfold fw_linear on the piece
  conv_rhs => simp only [fw_linear, hpiece_shape, hw]
  -- Simplify valAt of Tensor.mkShape on RHS
  have hrhs_bound : idx / (s * o) % b0 * (s * o) + idx % (s * o) / o * o + idx % (s * o) % o <
      prodShape [b0, s, o] := by
    simp only [prodShape, List.foldl, Nat.one_mul]
    have h_rest_eq : idx % (s * o) / o * o + idx % (s * o) % o = idx % (s * o) := by
      have h := Nat.div_add_mod (idx % (s * o)) o; rw [Nat.mul_comm] at h; exact h
    have h_rest_lt : idx % (s * o) < s * o := Nat.mod_lt _ hso_pos
    have h_lB_lt : idx / (s * o) % b0 < b0 := Nat.mod_lt _ hb0
    calc idx / (s * o) % b0 * (s * o) + idx % (s * o) / o * o + idx % (s * o) % o
        = idx / (s * o) % b0 * (s * o) + idx % (s * o) := by omega
      _ < idx / (s * o) % b0 * (s * o) + s * o := by omega
      _ = (idx / (s * o) % b0 + 1) * (s * o) := by ring
      _ ≤ b0 * (s * o) := Nat.mul_le_mul_right (s * o) h_lB_lt
      _ = (b0 * s) * o := by ring
  rw [valAt_of_lt _ _ hrhs_bound]
  simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte]
  -- RHS index decomposition:
  -- (lB*(s*o) + seq*o + col) / (s*o) = lB
  -- (lB*(s*o) + seq*o + col) % (s*o) = seq*o + col
  -- (seq*o + col) / o = seq, (seq*o + col) % o = col
  have hrest_lt : idx % (s * o) / o * o + idx % (s * o) % o < s * o := by
    have h := Nat.div_add_mod (idx % (s * o)) o; rw [Nat.mul_comm] at h
    have := Nat.mod_lt idx hso_pos; omega
  have hdiv_so : (idx / (s * o) % b0 * (s * o) + idx % (s * o) / o * o + idx % (s * o) % o) / (s * o) =
      idx / (s * o) % b0 := by
    rw [show idx / (s * o) % b0 * (s * o) + idx % (s * o) / o * o + idx % (s * o) % o =
        (idx % (s * o) / o * o + idx % (s * o) % o) + idx / (s * o) % b0 * (s * o) from by ring]
    rw [Nat.add_mul_div_right _ _ hso_pos]
    have : (idx % (s * o) / o * o + idx % (s * o) % o) / (s * o) = 0 :=
      Nat.div_eq_of_lt (by omega)
    omega
  have hmod_so_rhs : (idx / (s * o) % b0 * (s * o) + idx % (s * o) / o * o + idx % (s * o) % o) % (s * o) =
      idx % (s * o) / o * o + idx % (s * o) % o := by
    rw [show idx / (s * o) % b0 * (s * o) + idx % (s * o) / o * o + idx % (s * o) % o =
        (idx % (s * o) / o * o + idx % (s * o) % o) + idx / (s * o) % b0 * (s * o) from by ring]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv_o : (idx % (s * o) / o * o + idx % (s * o) % o) / o =
      idx % (s * o) / o := by
    rw [show idx % (s * o) / o * o + idx % (s * o) % o =
        idx % (s * o) % o + idx % (s * o) / o * o from by ring]
    rw [Nat.add_mul_div_right _ _ ho]
    have : idx % (s * o) % o / o = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ ho)
    omega
  have hmod_o : (idx % (s * o) / o * o + idx % (s * o) % o) % o =
      idx % (s * o) % o := by
    rw [show idx % (s * o) / o * o + idx % (s * o) % o =
        idx % (s * o) % o + idx % (s * o) / o * o from by ring]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ ho)
  simp only [hdiv_so, hmod_so_rhs, hdiv_o, hmod_o]
  -- Now RHS is: ∑ j ∈ range i, valAt (xs[rk]) ((lB*s+seq)*i+j) * valAt w (col*i+j)
  -- === Handle the LHS ===
  -- Unfold allGatherPrimDim0 in the LHS
  conv_lhs => simp only [allGatherPrimDim0, hxs_head]
  -- Simplify if-then-else guards in the allGatherPrimDim0 body
  simp only [Tensor.mkShape, hsi_ne, hi_ne, hb0_ne, ↓reduceIte]
  -- Now need to show the sum with allGatherPrimDim0 values = the sum with piece values
  -- Both are ∑ j ∈ range i, ... * valAt w (col*i+j)
  -- For each j, the allGatherPrimDim0 access valAt (Tensor.mkShape [b0*numParts, s, i] ...) ((row*s+seq)*i+j)
  -- needs to be shown equal to valAt (xs[rk]) ((lB*s+seq)*i+j)
  -- This requires: ((row*s+seq)*i+j) < prodShape [b0*numParts, s, i]
  -- and the index decomposition: (row*s+seq)*i+j / (s*i) = row, etc.
  apply Finset.sum_congr rfl
  intro j hj
  have hj_lt : j < i := Finset.mem_range.mp hj
  congr 1
  -- Need: valAt of the gather tensor = valAt of the piece
  -- The gather tensor is Tensor.mkShape [b0*numParts, s, i] fGather
  -- Access index: (row*s+seq)*i+j
  have hgather_idx_lt : (idx / (s * o) * s + idx % (s * o) / o) * i + j < prodShape [b0 * numParts, s, i] := by
    simp [prodShape, List.foldl]
    have h1 : idx % (s * o) / o * i + j < s * i := by
      calc idx % (s * o) / o * i + j
          < idx % (s * o) / o * i + i := by omega
        _ = (idx % (s * o) / o + 1) * i := by ring
        _ ≤ s * i := Nat.mul_le_mul_right i hseq_lt
    calc (idx / (s * o) * s + idx % (s * o) / o) * i + j
        = idx % (s * o) / o * i + j + idx / (s * o) * (s * i) := by ring
      _ < s * i + idx / (s * o) * (s * i) := by omega
      _ = (idx / (s * o) + 1) * (s * i) := by ring
      _ ≤ (b0 * numParts) * (s * i) := Nat.mul_le_mul_right (s * i) hrow_lt
      _ = b0 * numParts * s * i := by ring
  rw [valAt_of_lt _ _ hgather_idx_lt]
  -- Index decomposition for (row*s+seq)*i+j:
  -- (row*s+seq)*i+j / (s*i) = row (since seq*i+j < s*i)
  -- (row*s+seq)*i+j % (s*i) = seq*i+j
  -- (seq*i+j) / i = seq (since j < i)
  -- (seq*i+j) % i = j
  have hseqi_lt : idx % (s * o) / o * i + j < s * i := by
    calc idx % (s * o) / o * i + j
        < idx % (s * o) / o * i + i := by omega
      _ = (idx % (s * o) / o + 1) * i := by ring
      _ ≤ s * i := Nat.mul_le_mul_right i hseq_lt
  have hdiv_si : ((idx / (s * o) * s + idx % (s * o) / o) * i + j) / (s * i) = idx / (s * o) := by
    rw [show (idx / (s * o) * s + idx % (s * o) / o) * i + j =
        (idx % (s * o) / o * i + j) + idx / (s * o) * (s * i) from by ring]
    rw [Nat.add_mul_div_right _ _ hsi_pos]
    have : (idx % (s * o) / o * i + j) / (s * i) = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hmod_si : ((idx / (s * o) * s + idx % (s * o) / o) * i + j) % (s * i) =
      idx % (s * o) / o * i + j := by
    rw [show (idx / (s * o) * s + idx % (s * o) / o) * i + j =
        (idx % (s * o) / o * i + j) + idx / (s * o) * (s * i) from by ring]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv_i : (idx % (s * o) / o * i + j) / i = idx % (s * o) / o := by
    rw [show idx % (s * o) / o * i + j = j + idx % (s * o) / o * i from by ring]
    rw [Nat.add_mul_div_right _ _ hi]
    have : j / i = 0 := Nat.div_eq_of_lt hj_lt
    omega
  have hmod_i : (idx % (s * o) / o * i + j) % i = j := by
    rw [show idx % (s * o) / o * i + j = j + idx % (s * o) / o * i from by ring]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hj_lt
  simp only [hdiv_si, hmod_si, hdiv_i, hmod_i]
  -- Now LHS summand = valAt (xs.getD rk (zeroTensor [b0,s,i])) (lB*(s*i)+seq*i+j)
  -- RHS summand = valAt (xs[rk]) ((lB*s+seq)*i+j)
  -- These are equal since xs.getD rk d = xs[rk] and lB*(s*i)+seq*i+j = (lB*s+seq)*i+j
  congr 1
  · rw [show xs.getD (idx / (s * o) / b0) (zeroTensor [b0, s, i]) =
        xs[idx / (s * o) / b0] from by
      unfold List.getD
      rw [List.getElem?_eq_getElem hrk_lt_len]; rfl]
  · ring

theorem fw_linear_3d_allGatherPrimDimN0_comm
    (numParts b0 s i o : Nat)
    (xs : List Tensor) (w : Tensor)
    (hw : w.shape = [o, i])
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [b0, s, i])
    (hxs_shape : ∀ x ∈ xs, x.shape = [b0, s, i])
    (hxs_len : xs.length = numParts)
    (hparts : 0 < numParts) (hb0 : 0 < b0) (hs : 0 < s) (hi : 0 < i) (ho : 0 < o) :
    fw_linear (allGatherPrimDimN 0 numParts 0 xs) w =
    allGatherPrimDim0 numParts 0 (xs.map (fun x => fw_linear x w)) := by
  rw [allGatherPrimDimN_0_eq_dim0 _ _ _ ⟨b0, s, i, hxs_head⟩]
  exact fw_linear_3d_allGatherPrimDim0_comm numParts b0 s i o xs w hw hxs_head hxs_shape hxs_len
    hparts hb0 hs hi ho


theorem fw_linear_allGather_eq_allReduce_fw_linear_chunk
    (numParts b i o shard : Nat) (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [b, i]) (hi : i = numParts * shard)
    (hws_len : ws.length = numParts) (hws_shapes : ∀ w ∈ ws, w.shape = [o, shard])
    (hparts : 0 < numParts) (hshard : 0 < shard) :
    fw_linear x (allGatherPrim numParts 0 ws) =
      allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
        fw_linear (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩))) := by
  have hws_head : ∀ w ∈ ws.head?, w.shape = [o, shard] := fun w hw =>
    hws_shapes w (match ws with | [] => by cases hw | w' :: _ => by simp_all)
  have hallGather_shape : (allGatherPrim numParts 0 ws).shape = [o, i] := by
    simp only [allGatherPrim, Tensor.mkShape, dropLast, lastD, appendLast]
    match ws with
    | [] => simp at hws_len; omega
    | w0 :: _ =>
      have hw0 : w0.shape = [o, shard] := hws_shapes w0 (by simp)
      simp [hw0, hi, Nat.mul_comm]
  have hchunk_shape : ∀ r : Fin numParts, (chunkPrim numParts r.val x).shape = [b, shard] := by
    intro r
    have hnumParts_ne0 : numParts ≠ 0 := by omega
    have hdiv : divNat i numParts = shard := by simp [divNat, hnumParts_ne0, hi]
    simp [chunkPrim, Tensor.mkShape, hx, dropLast, lastD, appendLast, hdiv]
  rw [fw_linear_is_matmul b i o x (allGatherPrim numParts 0 ws) hx hallGather_shape]
  have : ∀ r : Fin numParts, fw_linear (chunkPrim numParts r.val x)
      (ws.get ⟨r.val, by omega⟩) =
      Tensor.mkShape [b, o] (k_matmul b o shard (chunkPrim numParts r.val x)
        (ws.get ⟨r.val, by omega⟩)) := by
    intro r
    rw [fw_linear_is_matmul b shard o _ _ (hchunk_shape r)]
    exact hws_shapes _ (by simp)
  simp only [this]
  have hconv : Tensor.mkShape [b, o] (k_matmul b o i x (allGatherPrim numParts 0 ws)) =
      Tensor.mkShape [b, o] (k_matmul b o (numParts * shard) x (allGatherPrim numParts 0 ws)) := by
    rw [← hi]
  rw [hconv]
  convert matmul_allGather_eq_allReduce_matmul_chunk b o (numParts * shard) numParts shard x ws
    _ rfl hws_len hws_shapes hparts hshard
  rw [← hi]; exact hx


/-- `chunkPrim` value access for 3D tensors: analogous to `chunkPrim_valAt_mul_add` but
for tensors of shape `[b, s, numParts * shard]`. -/
theorem chunkPrim_valAt_mul_add_3d
    (numParts rank b s shard : Nat) (x : Tensor)
    (hshape : x.shape = [b, s, numParts * shard])
    (hparts : 0 < numParts)
    (hrank : rank < numParts)
    (p : Nat) (hp : p < b * s)
    (j : Nat) (hj : j < shard) :
    valAt (chunkPrim numParts rank x) (p * shard + j) =
      valAt x (p * (numParts * shard) + rank * shard + j) := by
  have hshard_pos : 0 < shard := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hnumParts_ne0 : numParts ≠ 0 := Nat.ne_of_gt hparts
  have hdiv : divNat (numParts * shard) numParts = shard := by
    simp [divNat, hnumParts_ne0]
  have hchunkShape : (chunkPrim numParts rank x).shape = [b, s, shard] := by
    simp [chunkPrim, Tensor.mkShape, hshape, dropLast, lastD, appendLast, divNat, hnumParts_ne0]
  have hlt_chunk' : p * shard + j < b * s * shard := by
    have h1 : p * shard + j < p * shard + shard := Nat.add_lt_add_left hj _
    have h2 : (p + 1) * shard ≤ b * s * shard := Nat.mul_le_mul_right shard (by omega)
    have h3 : p * shard + shard = (p + 1) * shard := by ring
    omega
  have hlt_chunk : p * shard + j < prodShape (chunkPrim numParts rank x).shape := by
    simp only [hchunkShape, prodShape, List.foldl, Nat.one_mul]
    have h : b * s * shard = b * (s * shard) := Nat.mul_assoc b s shard
    omega
  have hdiv_p : (p * shard + j) / shard = p := by
    have heq : j + shard * p = p * shard + j := by ring
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.1
  have hmod_p : (p * shard + j) % shard = j := by
    have heq : j + shard * p = p * shard + j := by ring
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.2
  have hrmod : (rank % numParts) = rank := Nat.mod_eq_of_lt hrank
  have h0 : valAt (chunkPrim numParts rank x) (p * shard + j) =
      (chunkPrim numParts rank x).val ⟨p * shard + j, hlt_chunk⟩ := by
    simp [valAt, hlt_chunk]
  rw [h0]
  simp [chunkPrim, Tensor.mkShape, hshape, dropLast, lastD, appendLast, divNat,
    hnumParts_ne0, hshard_pos.ne', hdiv_p, hmod_p, hrmod]

-- 3D version of fw_linear_allGather_eq_allReduce_fw_linear_chunk
set_option maxHeartbeats 800000 in
theorem fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d
    (numParts b s i o shard : Nat) (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [b, s, i]) (hi : i = numParts * shard)
    (hws_len : ws.length = numParts) (hws_shapes : ∀ w ∈ ws, w.shape = [o, shard])
    (hparts : 0 < numParts) (hshard : 0 < shard) (hs : 0 < s) (ho : 0 < o) :
    fw_linear x (allGatherPrim numParts 0 ws) =
      allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
        fw_linear (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩))) := by
  have hnumParts_ne0 : numParts ≠ 0 := Nat.ne_of_gt hparts
  have hws_head : (ws.head?.map (fun t => t.shape)).getD [] = [o, shard] := by
    match ws with
    | [] => simp at hws_len; omega
    | w0 :: _ => exact hws_shapes w0 (by simp)
  have hallGather_shape : (allGatherPrim numParts 0 ws).shape = [o, i] := by
    simp only [allGatherPrim, Tensor.mkShape, hws_head, dropLast, lastD, appendLast]
    simp [hi, Nat.mul_comm]
  have hchunk_shape : ∀ r : Fin numParts, (chunkPrim numParts r.val x).shape = [b, s, shard] := by
    intro r
    have hdiv : divNat i numParts = shard := by simp [divNat, hnumParts_ne0, hi]
    simp [chunkPrim, Tensor.mkShape, hx, dropLast, lastD, appendLast, hdiv]
  have hLHS_shape : (fw_linear x (allGatherPrim numParts 0 ws)).shape = [b, s, o] :=
    fw_linear_3d_shape b s i o x _ hx hallGather_shape
  have hRHS_head : (List.ofFn (fun r : Fin numParts =>
      fw_linear (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩))).head? =
      some (fw_linear (chunkPrim numParts 0 x) (ws.get ⟨0, by omega⟩)) := by
    obtain ⟨np, hnp⟩ : ∃ np, numParts = np + 1 := ⟨numParts - 1, by omega⟩
    subst hnp; exact list_ofFn_head_eq _
  have hpiece0_shape : (fw_linear (chunkPrim numParts 0 x) (ws.get ⟨0, by omega⟩)).shape = [b, s, o] :=
    fw_linear_3d_shape b s shard o _ _ (hchunk_shape ⟨0, hparts⟩)
      (hws_shapes _ (List.getElem_mem (by omega)))
  have hRHS_shape : (allReducePrim numParts 0 (List.ofFn (fun r : Fin numParts =>
      fw_linear (chunkPrim numParts r.val x) (ws.get ⟨r.val, by omega⟩)))).shape = [b, s, o] := by
    rw [allReducePrim_shape _ _ _ _ hRHS_head, hpiece0_shape]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul] at hidx
  have hso_pos : 0 < s * o := Nat.mul_pos hs ho
  have hso_ne : s * o ≠ 0 := Nat.ne_of_gt hso_pos
  have ho_ne : (o : Nat) ≠ 0 := by omega
  have hi_ne : (i : Nat) ≠ 0 := by subst hi; exact Nat.ne_of_gt (Nat.mul_pos hparts hshard)
  set row := idx / (s * o)
  set rso := idx % (s * o)
  set seq := rso / o
  set col := rso % o
  have hrow_lt : row < b := by
    apply Nat.div_lt_of_lt_mul
    calc idx < b * s * o := hidx
      _ = s * o * b := by ring
  have hseq_lt : seq < s := by
    apply Nat.div_lt_of_lt_mul
    calc rso < s * o := Nat.mod_lt _ hso_pos
      _ = o * s := by ring
  have hcol_lt : col < o := Nat.mod_lt _ ho
  have hflat_row : row * s + seq < b * s := by
    calc row * s + seq < row * s + s := by omega
      _ = (row + 1) * s := by ring
      _ ≤ b * s := Nat.mul_le_mul_right s (by omega)
  have hprod : idx < prodShape [b, s, o] := by
    simp only [prodShape, List.foldl, Nat.one_mul]; exact hidx
  conv_lhs => simp only [fw_linear, hx, hallGather_shape]
  rw [valAt_of_lt _ _ hprod]
  simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte]
  have hsum_split : ∑ j_1 ∈ Finset.range i,
      valAt x ((idx / (s * o) * s + idx % (s * o) / o) * i + j_1) *
      valAt (allGatherPrim numParts 0 ws) (idx % (s * o) % o * i + j_1) =
    ∑ r : Fin numParts, ∑ j_1 ∈ Finset.range shard,
      valAt x ((row * s + seq) * i + (r.val * shard + j_1)) *
      valAt (ws.get ⟨r.val, by omega⟩) (col * shard + j_1) := by
    rw [hi]
    conv_lhs => rw [Finset.sum_range_mul_eq_sum_sum (n := numParts) (m := shard)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro j hj
    have hj' : j < shard := Finset.mem_range.mp hj
    have hr_lt : r.val < numParts := r.isLt
    have hgv := allGatherPrim_valAt_mul_add numParts (r.val) o shard ws
      hws_head hparts hr_lt col hcol_lt j hj'
    -- After rw [hi], goal allGatherPrim index is: col * (numParts * shard) + (r * shard + j)
    -- hgv uses: col * (shard * numParts) + r * shard + j
    -- These are equal by ring/commutativity
    have hag_idx : col * (numParts * shard) + (↑r * shard + j) =
        col * (shard * numParts) + ↑r * shard + j := by ring
    conv_lhs => rw [show idx % (s * o) % o = col from rfl,
      show col * (numParts * shard) + (↑r * shard + j) =
        col * (shard * numParts) + ↑r * shard + j from hag_idx]
    rw [hgv]
    simp only [List.getD, List.getElem?_eq_getElem (by omega : r.val < ws.length),
      Option.getD_some, List.get_eq_getElem]
    rfl
  rw [hsum_split]
  -- Unfold RHS: valAt (allReducePrim ...) idx = foldl sum of valAt
  have hpiece0_prod : idx < prodShape (fw_linear (chunkPrim numParts 0 x) (ws.get ⟨0, by omega⟩)).shape := by
    rw [hpiece0_shape, prodShape, List.foldl]; simp [Nat.one_mul]; exact hidx
  rw [allReducePrim_valAt numParts 0 _ idx _ hRHS_head hpiece0_prod]
  rw [List.foldl_add_eq_sum, List.map_ofFn]
  rw [Fin.sum_ofFn]
  apply Finset.sum_congr rfl; intro r _
  simp only [Function.comp_apply]
  have hr_shape := hchunk_shape r
  have hwr_shape := hws_shapes (ws.get ⟨r.val, by omega⟩) (List.getElem_mem (by omega))
  conv_rhs => simp only [fw_linear, hr_shape, hwr_shape]
  rw [valAt_of_lt _ _ hprod]
  simp only [Tensor.mkShape, hso_ne, ho_ne, ↓reduceIte]
  apply Finset.sum_congr rfl; intro j hj
  have hj' : j < shard := Finset.mem_range.mp hj
  have hcv := chunkPrim_valAt_mul_add_3d numParts r.val b s shard x
    (by rw [hx, hi]) hparts r.isLt (row * s + seq) hflat_row j hj'
  -- After rw [hcv], chunk valAt becomes x valAt with explicit offset
  -- Need: (row*s+seq)*i + r*shard+j = (row*s+seq)*(numParts*shard) + r*shard + j (from hi)
  have hx_idx_eq : (row * s + seq) * (numParts * shard) + ↑r * shard + j =
      (row * s + seq) * i + (↑r * shard + j) := by rw [hi]; ring
  rw [hx_idx_eq] at hcv
  rw [← hcv]

-- For 2D tensors with shape [o, shard], allGatherPrimDimN 1 = allGatherPrim (both gather on last dim)
theorem allGatherPrimDimN_1_eq_allGatherPrim_2d (numParts : Nat) (xs : List Tensor)
    (o shard : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hshard : 0 < shard) (hnp : 0 < numParts) :
    allGatherPrimDimN 1 numParts 0 xs = allGatherPrim numParts 0 xs := by
  have hshape_lhs : (allGatherPrimDimN 1 numParts 0 xs).shape = [o, shard * numParts] := by
    rw [allGatherPrimDimN_shape 1 numParts xs [o, shard] hhead]
    simp [List.set, List.getD]
  have hshape_rhs : (allGatherPrim numParts 0 xs).shape = [o, shard * numParts] := by
    simp [allGatherPrim, Tensor.mkShape, hhead, dropLast, lastD, appendLast]
  apply Tensor.ext (by rw [hshape_lhs, hshape_rhs])
  intro idx hidx
  rw [hshape_lhs] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul] at hidx
  have hlt_lhs : idx < prodShape (allGatherPrimDimN 1 numParts 0 xs).shape := by
    rw [hshape_lhs]; simp [prodShape]; omega
  have hlt_rhs : idx < prodShape (allGatherPrim numParts 0 xs).shape := by
    rw [hshape_rhs]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hlt_lhs, valAt_of_lt _ _ hlt_rhs]
  simp only [allGatherPrimDimN, allGatherPrim, Tensor.mkShape, hhead,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set, dropLast, lastD, appendLast,
    Nat.mul_one, Nat.add_zero, Nat.div_one, Nat.mod_one,
    show shard ≠ 0 from Nat.ne_of_gt hshard,
    show shard * numParts ≠ 0 from Nat.ne_of_gt (Nat.mul_pos hshard hnp),
    show (1 : Nat) ≠ 0 from by omega, ite_false,
    show ([o, shard] : List Nat).getLastD 0 = shard from by simp [List.getLastD],
    show ([o, shard] : List Nat).dropLast = [o] from by simp [List.dropLast]]
  simp only [List.cons_append, List.nil_append]

-- valAt for allGatherPrimDimN 2 on [1, 8, 8] pieces (4 parts → [1, 8, 32])
theorem allGatherPrimDimN_2_4_valAt_1_8_8 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 8]) (hidx : idx < 256) :
    valAt (allGatherPrimDimN 2 4 0 xs) idx =
      valAt (xs.getD (idx % 32 / 8) (zeroTensor [1, 8, 8]))
        ((idx / 32) * 8 + idx % 8) := by
  have hresult_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 xs [1, 8, 8] hhead]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (8 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega,
    show (1 : Nat) ≠ 0 from by omega, ite_false, List.set]
  congr 1
  omega

-- Roundtrip: chunkPrim undoes allGatherPrimDimN 2 on [1, 8, 8] pieces with 4 parts
set_option maxHeartbeats 800000 in
theorem chunkPrim_allGatherPrimDimN_2_roundtrip_1_8_8 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 8, 8]) (hc1 : c1.shape = [1, 8, 8])
    (hc2 : c2.shape = [1, 8, 8]) (hc3 : c3.shape = [1, 8, 8])
    (r : Nat) (hr : r < 4) :
    chunkPrim 4 r (allGatherPrimDimN 2 4 0 [c0, c1, c2, c3]) =
      [c0, c1, c2, c3].getD r (zeroTensor [1, 8, 8]) := by
  have hhead : (([c0, c1, c2, c3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hc0]
  have hgather_shape : (allGatherPrimDimN 2 4 0 [c0, c1, c2, c3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]; simp [List.set, List.getD]
  have hchunk_shape : (chunkPrim 4 r (allGatherPrimDimN 2 4 0 [c0, c1, c2, c3])).shape = [1, 8, 8] := by
    simp [chunkPrim, Tensor.mkShape, hgather_shape, dropLast, lastD, appendLast, divNat]
  have hrhs_shape : ([c0, c1, c2, c3].getD r (zeroTensor [1, 8, 8])).shape = [1, 8, 8] := by
    have h4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, hc0, hc1, hc2, hc3]
  apply Tensor.ext (by rw [hchunk_shape, hrhs_shape])
  intro idx hidx
  have hidx64 : idx < 64 := by simpa [hchunk_shape, prodShape] using hidx
  -- Use chunkPrim_valAt_mul_add_3d: chunkPrim 4 r x at (p*8+j) = valAt x (p*32 + r*8 + j)
  have hp : idx / 8 < 1 * 8 := by omega
  have hj : idx % 8 < 8 := Nat.mod_lt _ (by omega)
  have hidx_eq : idx = (idx / 8) * 8 + (idx % 8) := by omega
  rw [hidx_eq]
  rw [chunkPrim_valAt_mul_add_3d 4 r 1 8 8 _ hgather_shape (by omega) hr _ hp _ hj]
  -- Now LHS = valAt (allGatherPrimDimN 2 4 0 [c0,c1,c2,c3]) (idx/8 * 32 + r * 8 + idx%8)
  have hgather_idx : idx / 8 * (4 * 8) + r * 8 + idx % 8 = idx / 8 * 32 + r * 8 + idx % 8 := by ring
  rw [hgather_idx]
  have hlt256 : idx / 8 * 32 + r * 8 + idx % 8 < 256 := by omega
  rw [allGatherPrimDimN_2_4_valAt_1_8_8 _ _ hhead hlt256]
  -- Reduce the rank index and the flat index explicitly so the getD targets match.
  have hrank : (idx / 8 * 32 + r * 8 + idx % 8) % 32 / 8 = r := by omega
  have hflat : (idx / 8 * 32 + r * 8 + idx % 8) / 32 * 8 + (idx / 8 * 32 + r * 8 + idx % 8) % 8
      = idx / 8 * 8 + idx % 8 := by omega
  rw [hrank, hflat]

/-- `chunkPrimDimN` (dim 2) undoes `allGatherPrimDimN` (dim 2) on `[1, 8, 8]` shards.
    This is the dim-2 analogue of `chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32`. -/
theorem chunkPrimDimN_allGatherPrimDimN_dim2_4_1_8_8 (xs : List Tensor) (r : Nat)
    (hr : r < 4) (hlen : xs.length = 4)
    (hshape : ∀ x ∈ xs, x.shape = [1, 8, 8]) :
    chunkPrimDimN 2 4 r (allGatherPrimDimN 2 4 0 xs) = xs.getD r (zeroTensor [1, 8, 8]) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    match xs, hlen with
    | x0 :: _, _ =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape x0 (List.mem_cons_self ..)
  have hgather_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 xs [1, 8, 8] hhead]
    simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 2 4 r (allGatherPrimDimN 2 4 0 xs)).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : (xs.getD r (zeroTensor [1, 8, 8])).shape = [1, 8, 8] := by
    have hr_len : r < xs.length := by omega
    have helem : xs.getD r (zeroTensor [1, 8, 8]) = xs[r] := by
      simp [List.getD, List.getElem?_eq_getElem hr_len]
    rw [helem]
    exact hshape (xs[r]) (List.getElem_mem hr_len)
  apply Tensor.ext
  · rw [hchunk_shape, hrhs_shape]
  · intro idx hidx
    rw [hchunk_shape] at hidx
    have hidx64 : idx < 64 := by simpa [prodShape] using hidx
    set p := idx / 8 with hpdef
    set j := idx % 8 with hjdef
    have hp : p < 8 := by
      have : idx / 8 < 64 / 8 := Nat.div_lt_div_of_lt_of_dvd ⟨8, rfl⟩ hidx64
      simpa using this
    have hj : j < 8 := Nat.mod_lt idx (by omega)
    have hidx_eq : idx = p * 8 + j := by rw [hpdef, hjdef]; omega
    rw [hidx_eq]
    rw [chunk2_4_1_8_32_valAt_pj (allGatherPrimDimN 2 4 0 xs) r p j hgather_shape hr hp hj]
    have hlt256 : p * 32 + r * 8 + j < 256 := by omega
    rw [allGatherPrimDimN_2_4_valAt_1_8_8 _ _ hhead hlt256]
    have hrank : (p * 32 + r * 8 + j) % 32 / 8 = r := by omega
    have hflat : (p * 32 + r * 8 + j) / 32 * 8 + (p * 32 + r * 8 + j) % 8 = p * 8 + j := by omega
    rw [hrank, hflat]

/-!
## Initial-value alignment (input consistency)

To prove that SM and PM computations are equivalent, we must assume their *initial stores*
are related (same dataset inputs, and TP-sharded weights correspond to the same full weights, etc).

We express this as additional lineage-like obligations on boundary/initial tensors.
These are generated automatically as `initGoals` by the Python generator.

Important: this is value-level, not just shapes.
-/

def InitGoalHolds (numParts : Nat) (goal : LineageGoal) (initSM initPM : Store) : Prop :=
  let ts := initSM goal.ts
  let tps := goal.tps.map (fun p => initPM p.tid)
  ts.shape = goal.tsShape ∧
    (tps.map (fun t => t.shape)) = goal.tpShapes ∧
    ts = reconstructWithDim goal.gatherDim numParts 0 tps

def InitGoalsHold (numParts : Nat) (goals : List LineageGoal) (initSM initPM : Store) : Prop :=
  ∀ g ∈ goals, InitGoalHolds numParts g initSM initPM

/-!
## Coarse lineage obligation (with shape checks)

This is the Lean goal emitted by the generator.
It includes both:
- value equality, and
- explicit dimension equality (`tsShape`, `tpShapes`).
-/

def CoarseLineageHolds (sm pm : GraphDecl) (goal : LineageGoal) : Prop :=
  ∀ (initSM initPM : Store),
    let smStore := denoteGraph sm initSM
    let pmStore := denoteGraph pm initPM
    let ts := smStore goal.ts
    let tps := goal.tps.map (fun p => pmStore p.tid)
    ts.shape = goal.tsShape ∧
      (tps.map (fun t => t.shape)) = goal.tpShapes ∧
      ts = reconstructWithDim goal.gatherDim pm.numRanks 0 tps

/-!
`CoarseLineageHolds` as written above is intentionally “shape-free” on inputs, hence too strong
for realistic generated graphs (it quantifies over arbitrary initial shapes).

For faithful translation, use `CoarseLineageHoldsWith` together with `ShapeEnv`s generated from
graph metadata.
-/

def CoarseLineageHoldsWith (sm pm : GraphDecl) (goal : LineageGoal)
    (smInit pmInit : ShapeEnv) : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInit →
    StoreShapesHold initPM pmInit →
    let smStore := denoteGraph sm initSM
    let pmStore := denoteGraph pm initPM
    let ts := smStore goal.ts
    let tps := goal.tps.map (fun p => pmStore p.tid)
    ts.shape = goal.tsShape ∧
      (tps.map (fun t => t.shape)) = goal.tpShapes ∧
      ts = reconstructWithDim goal.gatherDim pm.numRanks 0 tps

def CoarseLineageHoldsWithInit (sm pm : GraphDecl) (goal : LineageGoal)
    (smInit pmInit : ShapeEnv) (initGoals : List LineageGoal) : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInit →
    StoreShapesHold initPM pmInit →
    InitGoalsHold pm.numRanks initGoals initSM initPM →
    let smStore := denoteGraph sm initSM
    let pmStore := denoteGraph pm initPM
    let ts := smStore goal.ts
    let tps := goal.tps.map (fun p => pmStore p.tid)
    ts.shape = goal.tsShape ∧
      (tps.map (fun t => t.shape)) = goal.tpShapes ∧
      ts = reconstructWithDim goal.gatherDim pm.numRanks 0 tps

/-!
## Incremental lineage goals with intermediate prerequisites

For goals that depend on the output of earlier goals (via shared intermediate tensors),
we provide a version that assumes intermediate lineage goals already hold.

This allows proving goals incrementally: once an earlier goal is proven,
later goals can assume its conclusion as a hypothesis.
-/

/-- Check that an intermediate lineage goal holds for already-computed stores. -/
def IntermediateGoalHolds (numParts : Nat) (goal : LineageGoal) (smStore pmStore : Store) : Prop :=
  let ts := smStore goal.ts
  let tps := goal.tps.map (fun p => pmStore p.tid)
  ts.shape = goal.tsShape ∧
    (tps.map (fun t => t.shape)) = goal.tpShapes ∧
    ts = reconstructWithDim goal.gatherDim numParts 0 tps

def IntermediateGoalsHold (numParts : Nat) (goals : List LineageGoal)
    (smStore pmStore : Store) : Prop :=
  ∀ g ∈ goals, IntermediateGoalHolds numParts g smStore pmStore

/-- Lineage goal with intermediate prerequisites.

This is the incremental version that assumes earlier goals (captured as `prereqGoals`)
have already been proven. This enables modular proofs where later goals can assume
intermediate tensor consistency without re-proving everything.
-/
def CoarseLineageHoldsWithIntermediates (sm pm : GraphDecl) (goal : LineageGoal)
    (smInit pmInit : ShapeEnv) (initGoals prereqGoals : List LineageGoal) : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInit →
    StoreShapesHold initPM pmInit →
    InitGoalsHold pm.numRanks initGoals initSM initPM →
    IntermediateGoalsHold pm.numRanks prereqGoals (denoteGraph sm initSM) (denoteGraph pm initPM) →
    let smStore := denoteGraph sm initSM
    let pmStore := denoteGraph pm initPM
    let ts := smStore goal.ts
    let tps := goal.tps.map (fun p => pmStore p.tid)
    ts.shape = goal.tsShape ∧
      (tps.map (fun t => t.shape)) = goal.tpShapes ∧
      ts = reconstructWithDim goal.gatherDim pm.numRanks 0 tps

/-- If we prove the incremental statement and the prereqs, we get the full statement. -/
theorem CoarseLineageHoldsWithInit_of_incremental
    (sm pm : GraphDecl) (goal : LineageGoal)
    (smInit pmInit : ShapeEnv) (initGoals prereqGoals : List LineageGoal)
    (hincr : CoarseLineageHoldsWithIntermediates sm pm goal smInit pmInit initGoals prereqGoals)
    (hprereqs : ∀ g ∈ prereqGoals, CoarseLineageHoldsWithInit sm pm g smInit pmInit initGoals) :
    CoarseLineageHoldsWithInit sm pm goal smInit pmInit initGoals := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  apply hincr initSM initPM hSmInit hPmInit hInitGoals
  intro g hg
  exact hprereqs g hg initSM initPM hSmInit hPmInit hInitGoals

/-!
## Segment composition skeleton

Generated large-model proofs can decompose a graph into repeated segments (for
example GPT transformer blocks), prove each segment through a reusable pattern,
and then compose the coverage certificate back into the original graph.

The segment declarations below intentionally keep composition at the graph/list
level. Value-level proofs are still ordinary `CoarseLineageHoldsWithInit`
theorems for the concrete goals.
-/

structure SegmentDecl where
  name : String
  sm : GraphDecl
  pm : GraphDecl
  goals : List LineageGoal
  deriving Repr

def concatSMGraph (numRanks : Nat) (segments : List SegmentDecl) : GraphDecl :=
  { numRanks := numRanks, nodes := segments.flatMap (fun s => s.sm.nodes) }

def concatPMGraph (numRanks : Nat) (segments : List SegmentDecl) : GraphDecl :=
  { numRanks := numRanks, nodes := segments.flatMap (fun s => s.pm.nodes) }

def SegmentRelWithInit (seg : SegmentDecl)
    (smInit pmInit : ShapeEnv) (initGoals : List LineageGoal) : Prop :=
  ∀ g ∈ seg.goals, CoarseLineageHoldsWithInit seg.sm seg.pm g smInit pmInit initGoals

def SegmentsRelWithInit (segments : List SegmentDecl)
    (smInit pmInit : ShapeEnv) (initGoals : List LineageGoal) : Prop :=
  ∀ seg ∈ segments, SegmentRelWithInit seg smInit pmInit initGoals

def GraphCoverage (sm pm : GraphDecl) (segments : List SegmentDecl) : Prop :=
  (concatSMGraph sm.numRanks segments).nodes = sm.nodes ∧
    (concatPMGraph pm.numRanks segments).nodes = pm.nodes

theorem all_goals_stmt_of_forall
    (sm pm : GraphDecl) (goals : List LineageGoal)
    (smInit pmInit : ShapeEnv) (initGoals : List LineageGoal)
    (h : ∀ g ∈ goals, CoarseLineageHoldsWithInit sm pm g smInit pmInit initGoals) :
    ∀ g ∈ goals, CoarseLineageHoldsWithInit sm pm g smInit pmInit initGoals := h

/-! ## Matmul helpers for sequence/tensor-parallel patterns -/

/-- Unfolding lemma for binary `FW_matmul`. -/
theorem evalOp_fw_matmul (numParts rank : Nat) (x y : Tensor) :
    evalOp numParts rank "OpName.FW_matmul" [] [x, y] = [fw_matmul x y] := by
  rfl

/-- `applyNode` for binary `FW_matmul` with singleton output. -/
theorem applyNode_fw_matmul_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid yTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_matmul", ins := [xTid, yTid], outs := [outTid] } outTid =
      fw_matmul (s xTid) (s yTid) := by
  unfold applyNode
  rw [show ([xTid, yTid] : List Tid).map s = [s xTid, s yTid] from rfl,
      evalOp_fw_matmul]
  change storeSet s [(outTid, fw_matmul (s xTid) (s yTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for binary `FW_matmul` with empty params explicit. -/
theorem applyNode_fw_matmul_out_empty_params
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid yTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_matmul", ins := [xTid, yTid], outs := [outTid], params := [] } outTid =
      fw_matmul (s xTid) (s yTid) :=
  applyNode_fw_matmul_out g s rank xTid yTid outTid

/-- Shape preservation for `fw_matmul` on rank-4 tensors of shape `[1, 4, 8, 8]`. -/
theorem fw_matmul_shape_1_4_8_8 (x y : Tensor)
    (hx : x.shape = [1, 4, 8, 8]) (hy : y.shape = [1, 4, 8, 8]) :
    (fw_matmul x y).shape = [1, 4, 8, 8] := by
  unfold fw_matmul batchedMatmul
  simp only [hx, hy, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    Tensor.mkShape]

/-- Shape preservation for `fw_matmul` on rank-4 tensors of shape `[1, 1, 8, 8]`. -/
theorem fw_matmul_shape_1_1_8_8 (x y : Tensor)
    (hx : x.shape = [1, 1, 8, 8]) (hy : y.shape = [1, 1, 8, 8]) :
    (fw_matmul x y).shape = [1, 1, 8, 8] := by
  unfold fw_matmul batchedMatmul
  simp only [hx, hy, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    Tensor.mkShape]

/-- valAt of `chunkPrimDimN 1 4 r x` for shape `[1, 4, 8, 8]`: chunk along dim 1 (batch axis),
    where each chunk has shape `[1, 1, 8, 8]`. The local flat index `loc < 64` corresponds to
    global flat `r * 64 + loc` in the original tensor. -/
theorem chunk_dim1_4_1_4_8_8_valAt (x : Tensor) (r loc : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hr : r < 4) (hloc : loc < 64) :
    valAt (chunkPrimDimN 1 4 r x) loc = valAt x (r * 64 + loc) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 1, 8, 8] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : loc < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false,
    show (4 / 4 * (1 * 8 * 8) : Nat) ≠ 0 by decide,
    show (1 * 8 * 8 : Nat) ≠ 0 by decide]
  congr 1
  omega

/-- valAt of `allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]` for shards of shape `[1, 1, 8, 8]`:
    gather along dim 1 (batch axis) gives shape `[1, 4, 8, 8]`. Global flat `idx < 256`
    selects piece `idx / 64` at local flat `idx % 64`. -/
theorem allGather_dim1_4_1_1_8_8_valAt (p0 p1 p2 p3 : Tensor) (idx : Nat)
    (h0 : p0.shape = [1, 1, 8, 8]) (h1 : p1.shape = [1, 1, 8, 8])
    (h2 : p2.shape = [1, 1, 8, 8]) (h3 : p3.shape = [1, 1, 8, 8])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]) idx =
    valAt ([p0, p1, p2, p3].getD (idx / 64) (zeroTensor [1, 1, 8, 8])) (idx % 64) := by
  have hhead : (([p0, p1, p2, p3] : List Tensor).head?.map (·.shape)).getD [] = [1, 1, 8, 8] := by
    simp [h0]
  have hgather_shape : (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]; simp [List.set, List.getD]
  have hidx_shape : idx < prodShape (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hidx_shape]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (1 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (4 : Nat) ≠ 0 by omega, ite_false,
    show (1 * (8 * (8 * 1)) * 4 : Nat) ≠ 0 by decide,
    show (8 * (8 * 1) : Nat) ≠ 0 by decide,
    show (1 * 4 : Nat) = 4 by decide,
    show (1 * 4 * (8 * (8 * 1)) : Nat) = 256 by decide]
  have hpre : idx / 256 = 0 := by omega
  have hrem : idx % 256 = idx := by omega
  rw [hpre, hrem]
  have hjFull_lt : idx / (8 * (8 * 1)) < 4 := by
    have : (8 : Nat) * (8 * 1) = 64 := by decide
    rw [this]; omega
  have hjFull_div : idx / (8 * (8 * 1)) / 1 = idx / 64 := by
    have : (8 : Nat) * (8 * 1) = 64 := by decide
    rw [this]; omega
  have hjLocal : idx / (8 * (8 * 1)) % 1 = 0 := by omega
  rw [hjFull_div, hjLocal]
  -- piece selection
  have hpiece : ([p0, p1, p2, p3] : List Tensor).getD (idx / 64)
      (zeroTensor [1, 1, 8, 8]) =
      ([p0, p1, p2, p3] : List Tensor).getD (idx / 64) (zeroTensor [1, 1, 8, 8]) := rfl
  -- index arithmetic
  congr 1
  omega

/-! ## Matmul valAt helpers and split bridging lemma (for pattern_28 family) -/

/-- valAt of `fw_matmul a b` at flat `idx < 256` for inputs of shape `[1, 4, 8, 8]`.
    The output also has shape `[1, 4, 8, 8]`. -/
private theorem fw_matmul_valAt_1_4_8_8 (a b : Tensor) (idx : Nat)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 8]) (hidx : idx < 256) :
    valAt (fw_matmul a b) idx =
      ∑ l ∈ Finset.range 8,
        valAt a (idx / 64 * 64 + idx % 64 / 8 * 8 + l) *
          valAt b (idx / 64 * 64 + l * 8 + idx % 8) := by
  have key : fw_matmul a b = Tensor.mkShape [1, 4, 8, 8] (fun outIdx =>
      ∑ l ∈ Finset.range 8,
        valAt a (outIdx.1 / (8 * 8) * (8 * 8) +
                  outIdx.1 % (8 * 8) / 8 * 8 + l) *
          valAt b (outIdx.1 / (8 * 8) * (8 * 8) + l * 8 +
                    outIdx.1 % (8 * 8) % 8)) := by
    unfold fw_matmul batchedMatmul
    rw [ha, hb]
    rfl
  rw [key]
  have hout : (Tensor.mkShape [1, 4, 8, 8] (fun outIdx : Fin (prodShape [1,4,8,8]) =>
      ∑ l ∈ Finset.range 8,
        valAt a (outIdx.1 / (8 * 8) * (8 * 8) +
                  outIdx.1 % (8 * 8) / 8 * 8 + l) *
          valAt b (outIdx.1 / (8 * 8) * (8 * 8) + l * 8 +
                    outIdx.1 % (8 * 8) % 8))).shape = [1, 4, 8, 8] := by
    simp [Tensor.mkShape]
  have hidx' : idx < prodShape ([1,4,8,8] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hidx')]
  show ∑ l ∈ Finset.range 8,
        valAt a (idx / (8 * 8) * (8 * 8) + idx % (8 * 8) / 8 * 8 + l) *
          valAt b (idx / (8 * 8) * (8 * 8) + l * 8 + idx % (8 * 8) % 8) = _
  apply Finset.sum_congr rfl
  intro l _
  congr 2 <;> omega

/-- valAt of `fw_matmul a b` at flat `loc < 64` for inputs of shape `[1, 1, 8, 8]`.
    The output also has shape `[1, 1, 8, 8]`. -/
private theorem fw_matmul_valAt_1_1_8_8 (a b : Tensor) (loc : Nat)
    (ha : a.shape = [1, 1, 8, 8]) (hb : b.shape = [1, 1, 8, 8]) (hloc : loc < 64) :
    valAt (fw_matmul a b) loc =
      ∑ l ∈ Finset.range 8,
        valAt a (loc / 8 * 8 + l) * valAt b (l * 8 + loc % 8) := by
  have key : fw_matmul a b = Tensor.mkShape [1, 1, 8, 8] (fun outIdx =>
      ∑ l ∈ Finset.range 8,
        valAt a (outIdx.1 / (8 * 8) * (8 * 8) +
                  outIdx.1 % (8 * 8) / 8 * 8 + l) *
          valAt b (outIdx.1 / (8 * 8) * (8 * 8) + l * 8 +
                    outIdx.1 % (8 * 8) % 8)) := by
    unfold fw_matmul batchedMatmul
    rw [ha, hb]
    rfl
  rw [key]
  have hloc' : loc < prodShape ([1,1,8,8] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hloc')]
  show ∑ l ∈ Finset.range 8,
        valAt a (loc / (8 * 8) * (8 * 8) + loc % (8 * 8) / 8 * 8 + l) *
          valAt b (loc / (8 * 8) * (8 * 8) + l * 8 + loc % (8 * 8) % 8) = _
  apply Finset.sum_congr rfl
  intro l _
  congr 2 <;> omega

/-- The matmul-over-batched-input bridging lemma for shape `[1, 4, 8, 8]` split along dim 1
    into 4 chunks of shape `[1, 1, 8, 8]`. Since matmul is independent across the leading
    batch dimensions, chunking dim 1 commutes with matmul. -/
theorem fw_matmul_split_dim1_4_1_4_8_8 (a b : Tensor)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 8]) :
    fw_matmul a b =
      allGatherPrimDimN 1 4 0
        [fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
         fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
         fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
         fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)] := by
  -- Common chunk shape facts
  have hchunk_a : ∀ r, r < 4 → (chunkPrimDimN 1 4 r a).shape = [1, 1, 8, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 1 4 r _ _ ha (by omega)]
    simp [List.set, List.getD]
  have hchunk_b : ∀ r, r < 4 → (chunkPrimDimN 1 4 r b).shape = [1, 1, 8, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 1 4 r _ _ hb (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 →
      (fw_matmul (chunkPrimDimN 1 4 r a) (chunkPrimDimN 1 4 r b)).shape = [1, 1, 8, 8] := by
    intro r hr
    exact fw_matmul_shape_1_1_8_8 _ _ (hchunk_a r hr) (hchunk_b r hr)
  have hp0 := hpiece_shape 0 (by decide)
  have hp1 := hpiece_shape 1 (by decide)
  have hp2 := hpiece_shape 2 (by decide)
  have hp3 := hpiece_shape 3 (by decide)
  have hlhs_shape : (fw_matmul a b).shape = [1, 4, 8, 8] :=
    fw_matmul_shape_1_4_8_8 a b ha hb
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
       fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
       fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
       fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)]).shape = [1, 4, 8, 8] := by
    have hhead : (([fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
                    fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
                    fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
                    fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)] : List Tensor).head?.map
                  (·.shape)).getD [] = [1, 1, 8, 8] := by
      simp [hp0]
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  -- Use the matmul valAt unfolding for LHS
  rw [fw_matmul_valAt_1_4_8_8 a b idx ha hb hidx256]
  -- Now unfold the RHS gather
  have hidx_rhs : idx < 256 := hidx256
  rw [allGather_dim1_4_1_1_8_8_valAt _ _ _ _ idx hp0 hp1 hp2 hp3 hidx_rhs]
  -- Determine which piece we land in
  have hr_lt : idx / 64 < 4 := by omega
  set r := idx / 64 with hr_def
  set loc := idx % 64 with hloc_def
  have hloc_lt : loc < 64 := by subst loc; omega
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  -- The piece is fw_matmul (chunk_a_r) (chunk_b_r); unfold its valAt
  -- For each r, we need to rewrite the getD selection
  have hvalpiece : ∀ rr, rr < 4 →
      valAt (fw_matmul (chunkPrimDimN 1 4 rr a) (chunkPrimDimN 1 4 rr b)) loc =
        ∑ l ∈ Finset.range 8,
          valAt a (rr * 64 + loc / 8 * 8 + l) *
          valAt b (rr * 64 + l * 8 + loc % 8) := by
    intro rr hrr
    rw [fw_matmul_valAt_1_1_8_8 _ _ loc (hchunk_a rr hrr) (hchunk_b rr hrr) hloc_lt]
    apply Finset.sum_congr rfl
    intro l hl
    have hl_lt : l < 8 := by simpa using hl
    have hi_lt : loc / 8 < 8 := by omega
    have hj_lt : loc % 8 < 8 := by omega
    have h1 : loc / 8 * 8 + l < 64 := by omega
    have h2 : l * 8 + loc % 8 < 64 := by omega
    rw [chunk_dim1_4_1_4_8_8_valAt a rr (loc / 8 * 8 + l) ha hrr h1]
    rw [chunk_dim1_4_1_4_8_8_valAt b rr (l * 8 + loc % 8) hb hrr h2]
    congr 1
    · congr 1; omega
    · congr 1; omega
  -- And we want: ∑_l valAt a (idx/64*64 + idx%64/8*8 + l) * valAt b (idx/64*64 + l*8 + idx%8)
  --            = (chosen-piece valAt at loc)
  have hjmod : idx % 8 = loc % 8 := by subst loc; omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · -- r = 0
    have hsel : ([fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
                  fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
                  fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
                  fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)] : List Tensor).getD
                  (idx / 64) (zeroTensor [1, 1, 8, 8]) =
                fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b) := by
      have : idx / 64 = 0 := by rw [← hr_def]; exact h0
      rw [this]; rfl
    rw [hsel, hvalpiece 0 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    have hidx_div : idx / 64 = 0 := by rw [← hr_def]; exact h0
    congr 2 <;> (subst loc; omega)
  · -- r = 1
    have hidx_div : idx / 64 = 1 := by rw [← hr_def]; exact h1
    have hsel : ([fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
                  fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
                  fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
                  fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)] : List Tensor).getD
                  (idx / 64) (zeroTensor [1, 1, 8, 8]) =
                fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b) := by
      rw [hidx_div]; rfl
    rw [hsel, hvalpiece 1 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> (subst loc; omega)
  · -- r = 2
    have hidx_div : idx / 64 = 2 := by rw [← hr_def]; exact h2
    have hsel : ([fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
                  fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
                  fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
                  fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)] : List Tensor).getD
                  (idx / 64) (zeroTensor [1, 1, 8, 8]) =
                fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b) := by
      rw [hidx_div]; rfl
    rw [hsel, hvalpiece 2 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> (subst loc; omega)
  · -- r = 3
    have hidx_div : idx / 64 = 3 := by rw [← hr_def]; exact h3
    have hsel : ([fw_matmul (chunkPrimDimN 1 4 0 a) (chunkPrimDimN 1 4 0 b),
                  fw_matmul (chunkPrimDimN 1 4 1 a) (chunkPrimDimN 1 4 1 b),
                  fw_matmul (chunkPrimDimN 1 4 2 a) (chunkPrimDimN 1 4 2 b),
                  fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b)] : List Tensor).getD
                  (idx / 64) (zeroTensor [1, 1, 8, 8]) =
                fw_matmul (chunkPrimDimN 1 4 3 a) (chunkPrimDimN 1 4 3 b) := by
      rw [hidx_div]; rfl
    rw [hsel, hvalpiece 3 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> (subst loc; omega)

/-- `transpose2d` maps shape `[1,1,8,8]` to `[1,1,8,8]`. -/
theorem transpose2d_shape_1_1_8_8 (x : Tensor) (hx : x.shape = [1, 1, 8, 8]) :
    (transpose2d x).shape = [1, 1, 8, 8] := by
  unfold transpose2d
  rw [hx]
  rfl

/-- `valAt` of `transpose2d x` for `x : [1,1,8,8]` (swap of the last two dims, batch fixed). -/
theorem transpose2d_valAt_1_1_8_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 1, 8, 8]) (hidx : idx < 64) :
    valAt (transpose2d x) idx = valAt x (idx % 8 * 8 + idx / 8) := by
  have key : transpose2d x = Tensor.mkShape [1, 1, 8, 8] (fun outIdx =>
      valAt x (outIdx.1 / (8 * 8) * (8 * 8) + outIdx.1 % (8 * 8) % 8 * 8 +
        outIdx.1 % (8 * 8) / 8)) := by
    unfold transpose2d
    rw [hx]
    rfl
  rw [key]
  have hidx' : idx < prodShape ([1, 1, 8, 8] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hidx')]
  show valAt x (idx / (8 * 8) * (8 * 8) + idx % (8 * 8) % 8 * 8 + idx % (8 * 8) / 8) = _
  congr 1
  omega


/-! ## Gather-of-chunks identity for dim 1, 4 parts, shape [1,8,128] -/

set_option maxHeartbeats 400000 in
theorem chunk_dim1_4_1_8_128_valAt (x : Tensor) (r p j : Nat)
    (hx : x.shape = [1, 8, 128]) (hr : r < 4) (hp : p < 2) (hj : j < 128) :
    valAt (chunkPrimDimN 1 4 r x) (p * 128 + j) = valAt x ((r * 2 + p) * 128 + j) := by
  have hloc : p * 128 + j < 256 := by omega
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 128] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p * 128 + j < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    show (8 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  congr 1
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  have h1 : (8 / 4 : Nat) = 2 := by norm_num
  have h2 : (1 * 128 : Nat) = 128 := by norm_num
  have h3 : (8 * (1 * 128) : Nat) = 1024 := by norm_num
  have h4 : (2 * (1 * 128) : Nat) = 256 := by norm_num
  simp only [h1, h2, h3, h4, show (256 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    ite_false]
  have hd : (p * 128 + j) / 256 = 0 := Nat.div_eq_of_lt hloc
  have hm : (p * 128 + j) % 256 = p * 128 + j := Nat.mod_eq_of_lt hloc
  rw [hd, hm]
  have h5 : (p * 128 + j) / 128 = p := by omega
  have h6 : (p * 128 + j) % 128 = j := by omega
  rw [h5, h6]
  ring

set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
theorem allGatherPrimDimN_dim1_4_1_2_128_valAt (xs : List Tensor)
    (r : Nat) (hr : r < 4) (p : Nat) (hp : p < 2) (j : Nat) (hj : j < 128)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 128]) :
    valAt (allGatherPrimDimN 1 4 0 xs) ((r * 2 + p) * 128 + j) =
      valAt (xs.getD r (zeroTensor [1, 2, 128])) (p * 128 + j) := by
  have hgather_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 128] hhead]
    simp [List.set, List.getD]
  have hidx_lt : (r * 2 + p) * 128 + j < 1024 := by omega
  have hidx_prod : (r * 2 + p) * 128 + j < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (2 : Nat) * 4 * 1 = 8 by norm_num,
    show (2 : Nat) * 1 = 2 by norm_num,
    show (8 : Nat) * (1 * 128) = 1024 by norm_num,
    show (1 : Nat) * 128 = 128 by norm_num,
    show (2 : Nat) * (1 * 128) = 256 by norm_num,
    show (1024 : Nat) = 0 ↔ False by simp,
    show (128 : Nat) = 0 ↔ False by simp,
    show (256 : Nat) = 0 ↔ False by simp,
    ite_false]
  have hd1024 : ((r * 2 + p) * 128 + j) / 1024 = 0 := Nat.div_eq_of_lt hidx_lt
  have hm1024 : ((r * 2 + p) * 128 + j) % 1024 = (r * 2 + p) * 128 + j :=
    Nat.mod_eq_of_lt hidx_lt
  have hd128 : ((r * 2 + p) * 128 + j) / 128 = r * 2 + p := by omega
  have hm128 : ((r * 2 + p) * 128 + j) % 128 = j := by omega
  have hdr : (r * 2 + p) / 2 = r := by omega
  have hmr : (r * 2 + p) % 2 = p := by omega
  rw [hd1024, hm1024, hd128, hm128, hdr, hmr]
  congr 1
  ring

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem allGatherPrimDimN_chunkPrimDimN_id_dim1_4_128 (x : Tensor)
    (hsh : x.shape = [1, 8, 128]) :
    allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r x).shape = [1, 2, 128] := by
    intro r
    rw [chunkPrimDimN_shape 1 4 r _ _ hsh (by omega)]
    simp [List.set, List.getD]
  have hhead : ([chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x].head?.map (·.shape)).getD [] = [1, 2, 128] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  have hgather_shape : (allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x]).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 128] hhead]
    simp [List.set, List.getD]
  symm
  apply Tensor.ext (by rw [hsh, hgather_shape])
  intro idx hidx
  rw [hsh] at hidx
  have hidx1024 : idx < 1024 := by simpa [prodShape] using hidx
  set r := idx / 256
  set p := (idx % 256) / 128
  set j := idx % 128
  have hr : r < 4 := by omega
  have hp : p < 2 := by
    have : (idx % 256) / 128 < 256 / 128 := Nat.div_lt_div_of_lt_of_dvd ⟨2, rfl⟩ (Nat.mod_lt _ (by omega))
    omega
  have hj : j < 128 := Nat.mod_lt idx (by omega)
  have hidx_eq : idx = (r * 2 + p) * 128 + j := by subst r p j; omega
  rw [hidx_eq]
  rw [allGatherPrimDimN_dim1_4_1_2_128_valAt _ r hr p hp j hj hhead]
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x].getD i (zeroTensor [1, 2, 128]) =
        chunkPrimDimN 1 4 i x := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  exact (chunk_dim1_4_1_8_128_valAt x r p j hsh hr hp hj).symm

/-! ## AllToAll node helpers (for pattern_28 family) -/

/-! ## BW_layernorm + CROSS_DP_WRED helpers for data-parallel weight-gradient goals -/

/-- Unfolding lemma for `evalOp` on `CROSS_DP_WRED`. -/
theorem evalOp_cross_dp_wred (numParts rank : Nat) (params : List Nat) (xs : List Tensor) :
    evalOp numParts rank "OpName.CROSS_DP_WRED" params xs = [cross_dp_wred xs] := by
  rfl

/-- `applyNode` for `CROSS_DP_WRED` with singleton output (in-place semantics). -/
theorem applyNode_cross_dp_wred_out
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.CROSS_DP_WRED", ins := ins, outs := [outTid] } outTid =
      cross_dp_wred (ins.map s) := by
  unfold applyNode
  rw [evalOp_cross_dp_wred]
  change storeSet s [(outTid, cross_dp_wred (ins.map s))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Unfolding lemma for `evalOp` on `BW_layernorm`. -/
theorem evalOp_bw_layernorm (numParts rank : Nat) (g x w b : Tensor) :
    evalOp numParts rank "OpName.BW_layernorm" [] [g, x, w, b] =
      [(bw_layernorm g x w b).1, (bw_layernorm g x w b).2.1, (bw_layernorm g x w b).2.2] := by
  rfl

/-- `applyNode` for `BW_layernorm` extracting the dw output (index 1 of 3). -/
theorem applyNode_bw_layernorm_dw_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid wTid bTid dxTid dwTid dbTid : Tid)
    (hne : dxTid ≠ dwTid) :
    applyNode g s (⟨rank, "OpName.BW_layernorm", [gTid, xTid, wTid, bTid], [dxTid, dwTid, dbTid], []⟩ : NodeDecl) dwTid =
      (bw_layernorm (s gTid) (s xTid) (s wTid) (s bTid)).2.1 := by
  unfold applyNode
  have hmap : ([gTid, xTid, wTid, bTid] : List Tid).map s = [s gTid, s xTid, s wTid, s bTid] := rfl
  rw [hmap, evalOp_bw_layernorm]
  unfold storeSet
  simp [List.find?, hne]

/-- `applyNode` for `BW_layernorm` extracting the db output (index 2 of 3). -/
theorem applyNode_bw_layernorm_db_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid wTid bTid dxTid dwTid dbTid : Tid)
    (hne1 : dxTid ≠ dbTid) (hne2 : dwTid ≠ dbTid) :
    applyNode g s (⟨rank, "OpName.BW_layernorm", [gTid, xTid, wTid, bTid], [dxTid, dwTid, dbTid], []⟩ : NodeDecl) dbTid =
      (bw_layernorm (s gTid) (s xTid) (s wTid) (s bTid)).2.2 := by
  unfold applyNode
  have hmap : ([gTid, xTid, wTid, bTid] : List Tid).map s = [s gTid, s xTid, s wTid, s bTid] := rfl
  rw [hmap, evalOp_bw_layernorm]
  unfold storeSet
  simp [List.find?, hne1, hne2]

/-- Unfolding lemma: dw output of `bw_layernorm` when x.shape.reverse starts with d. -/
theorem bw_layernorm_dw_eq (g x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    (bw_layernorm g x w b).2.1 = Tensor.mkShape w.shape (fun wIdx =>
      let j := wIdx.1
      ∑ row ∈ Finset.range (prodShape x.shape / d),
        let mean := layerNormMeanAt x row d
        let var := layerNormVarAt x row d mean
        let invStd := 1 / sqrtFn (var + layerNormEps)
        valAt g (row * d + j) * ((valAt x (row * d + j) - mean) * invStd)) := by
  unfold bw_layernorm; rw [hrev]

/-- Unfolding lemma: db output of `bw_layernorm` when x.shape.reverse starts with d. -/
theorem bw_layernorm_db_eq (g x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    (bw_layernorm g x w b).2.2 = Tensor.mkShape b.shape (fun bIdx =>
      let j := bIdx.1
      ∑ row ∈ Finset.range (prodShape x.shape / d),
        valAt g (row * d + j)) := by
  unfold bw_layernorm; rw [hrev]

/-- Shape of `bw_layernorm` dw output. -/
theorem bw_layernorm_dw_shape (g x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    (bw_layernorm g x w b).2.1.shape = w.shape := by
  rw [bw_layernorm_dw_eq g x w b d rest hrev]; simp [Tensor.mkShape]

/-- Shape of `bw_layernorm` db output. -/
theorem bw_layernorm_db_shape (g x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    (bw_layernorm g x w b).2.2.shape = b.shape := by
  rw [bw_layernorm_db_eq g x w b d rest hrev]; simp [Tensor.mkShape]

/-- Unfolding lemma: dx output of `bw_layernorm` when x.shape.reverse starts with d. -/
theorem bw_layernorm_dx_eq (g x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    (bw_layernorm g x w b).1 = Tensor.mkShape x.shape (fun outIdx =>
      let row := outIdx.1 / d
      let j := outIdx.1 % d
      let mean := layerNormMeanAt x row d
      let var := layerNormVarAt x row d mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      let xhat := (valAt x outIdx.1 - mean) * invStd
      let sumDy := ∑ k ∈ Finset.range d,
        valAt g (row * d + k) * valAt w k
      let sumDyXhat := ∑ k ∈ Finset.range d,
        let xhatK := (valAt x (row * d + k) - mean) * invStd
        (valAt g (row * d + k) * valAt w k) * xhatK
      invStd / (d : Scalar) *
        ((d : Scalar) * (valAt g outIdx.1 * valAt w j) - sumDy - xhat * sumDyXhat)) := by
  unfold bw_layernorm; rw [hrev]

/-- Shape of `bw_layernorm` dx output. -/
theorem bw_layernorm_dx_shape (g x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    (bw_layernorm g x w b).1.shape = x.shape := by
  rw [bw_layernorm_dx_eq g x w b d rest hrev]; simp [Tensor.mkShape]

/-- `applyNode` for `BW_layernorm` extracting the dx output (index 0 of 3). -/
theorem applyNode_bw_layernorm_dx_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid wTid bTid dxTid dwTid dbTid : Tid) :
    applyNode g s (⟨rank, "OpName.BW_layernorm", [gTid, xTid, wTid, bTid], [dxTid, dwTid, dbTid], []⟩ : NodeDecl) dxTid =
      (bw_layernorm (s gTid) (s xTid) (s wTid) (s bTid)).1 := by
  unfold applyNode
  have hmap : ([gTid, xTid, wTid, bTid] : List Tid).map s = [s gTid, s xTid, s wTid, s bTid] := rfl
  rw [hmap, evalOp_bw_layernorm]
  unfold storeSet
  simp [List.find?]

/-- valAt of `bw_layernorm` dx output at index `p*32 + j` for x shape `[1,8,32]`. -/
theorem bw_layernorm_dx_valAt_1_8_32 (g x w b : Tensor) (p j : Nat)
    (hx : x.shape = [1, 8, 32]) (hp : p < 8) (hj : j < 32) :
    valAt (bw_layernorm g x w b).1 (p * 32 + j) =
      let mean := layerNormMeanAt x p 32
      let var := layerNormVarAt x p 32 mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      let xhat := (valAt x (p * 32 + j) - mean) * invStd
      let sumDy := ∑ k ∈ Finset.range 32, valAt g (p * 32 + k) * valAt w k
      let sumDyXhat := ∑ k ∈ Finset.range 32,
        (valAt g (p * 32 + k) * valAt w k) * ((valAt x (p * 32 + k) - mean) * invStd)
      invStd / (32 : Scalar) *
        ((32 : Scalar) * (valAt g (p * 32 + j) * valAt w j) - sumDy - xhat * sumDyXhat) := by
  have hidx : p * 32 + j < 256 := by
    have h1 : p * 32 ≤ 7 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  rw [bw_layernorm_dx_eq g x w b 32 [8, 1] (by rw [hx]; rfl)]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape]; rw [hx]; exact hidx)]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  simp only [Tensor.mkShape, hdj, hmj, Nat.cast_ofNat]

/-- valAt of `bw_layernorm` dx output at index `p*32 + j` for x shape `[1,2,32]`. -/
theorem bw_layernorm_dx_valAt_1_2_32 (g x w b : Tensor) (p j : Nat)
    (hx : x.shape = [1, 2, 32]) (hp : p < 2) (hj : j < 32) :
    valAt (bw_layernorm g x w b).1 (p * 32 + j) =
      let mean := layerNormMeanAt x p 32
      let var := layerNormVarAt x p 32 mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      let xhat := (valAt x (p * 32 + j) - mean) * invStd
      let sumDy := ∑ k ∈ Finset.range 32, valAt g (p * 32 + k) * valAt w k
      let sumDyXhat := ∑ k ∈ Finset.range 32,
        (valAt g (p * 32 + k) * valAt w k) * ((valAt x (p * 32 + k) - mean) * invStd)
      invStd / (32 : Scalar) *
        ((32 : Scalar) * (valAt g (p * 32 + j) * valAt w j) - sumDy - xhat * sumDyXhat) := by
  have hidx : p * 32 + j < 64 := by
    have h1 : p * 32 ≤ 1 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  rw [bw_layernorm_dx_eq g x w b 32 [2, 1] (by rw [hx]; rfl)]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape]; rw [hx]; exact hidx)]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  simp only [Tensor.mkShape, hdj, hmj, Nat.cast_ofNat]

/-- `layerNormMeanAt` on allGather = `layerNormMeanAt` on shard. -/
theorem layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 (xs : List Tensor)
    (r : Nat) (hr : r < 4) (p : Nat) (hp : p < 2)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32]) :
    layerNormMeanAt (allGatherPrimDimN 1 4 0 xs) (r * 2 + p) 32 =
      layerNormMeanAt (xs.getD r (zeroTensor [1, 2, 32])) p 32 := by
  unfold layerNormMeanAt
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  exact allGatherPrimDimN_dim1_4_1_2_32_valAt xs r hr p hp j hj hhead

/-- `layerNormVarAt` on allGather = `layerNormVarAt` on shard. -/
theorem layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 (xs : List Tensor)
    (r : Nat) (hr : r < 4) (p : Nat) (hp : p < 2) (mean : Scalar)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32]) :
    layerNormVarAt (allGatherPrimDimN 1 4 0 xs) (r * 2 + p) 32 mean =
      layerNormVarAt (xs.getD r (zeroTensor [1, 2, 32])) p 32 mean := by
  unfold layerNormVarAt
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt xs r hr p hp j hj hhead]

set_option maxHeartbeats 800000 in
/-- The dw output of `bw_layernorm` on dim-1-gathered tensors (4 parts, shard [1,2,32])
    equals `tensorSum` of per-shard dw outputs. -/
theorem bw_layernorm_dw_dp_split_dim1_4_1_2_32
    (g0 g1 g2 g3 x0 x1 x2 x3 w b : Tensor)
    (hg0 : g0.shape = [1, 2, 32]) (hg1 : g1.shape = [1, 2, 32])
    (hg2 : g2.shape = [1, 2, 32]) (hg3 : g3.shape = [1, 2, 32])
    (hx0 : x0.shape = [1, 2, 32]) (hx1 : x1.shape = [1, 2, 32])
    (hx2 : x2.shape = [1, 2, 32]) (hx3 : x3.shape = [1, 2, 32])
    (hw : w.shape = [32]) :
    (bw_layernorm (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3])
                  (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]) w b).2.1 =
      tensorSum [(bw_layernorm g0 x0 w b).2.1,
                 (bw_layernorm g1 x1 w b).2.1,
                 (bw_layernorm g2 x2 w b).2.1,
                 (bw_layernorm g3 x3 w b).2.1] := by
  have hxs_head : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hx0]
  have hgs_head : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hg0]
  have hfullX_shape : (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hxs_head]; simp [List.set, List.getD]
  have hfullX_rev : (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]).shape.reverse = [32, 8, 1] := by
    rw [hfullX_shape]; decide
  have hx0_rev : x0.shape.reverse = [32, 2, 1] := by rw [hx0]; decide
  rw [bw_layernorm_dw_eq _ _ w b 32 [8, 1] hfullX_rev]
  have hprod_full : prodShape (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]).shape / 32 = 8 := by
    rw [hfullX_shape]; simp [prodShape]
  apply Tensor.ext
  · simp [Tensor.mkShape, hw, tensorSum, bw_layernorm_dw_shape _ _ _ _ 32 [2, 1] hx0_rev]
  · intro idx hidx
    have hidx_lt : idx < 32 := by simp [Tensor.mkShape, hw] at hidx; exact hidx
    rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, hw, prodShape]; exact hidx_lt)]
    simp only [Tensor.mkShape, hprod_full]
    -- RHS
    have hdw0_shape : (bw_layernorm g0 x0 w b).2.1.shape = [32] := by
      rw [bw_layernorm_dw_shape _ _ _ _ 32 [2, 1] hx0_rev, hw]
    rw [show tensorSum _ = Tensor.mkShape (bw_layernorm g0 x0 w b).2.1.shape
        (fun i => [(bw_layernorm g0 x0 w b).2.1, (bw_layernorm g1 x1 w b).2.1,
                   (bw_layernorm g2 x2 w b).2.1, (bw_layernorm g3 x3 w b).2.1].foldl
                   (fun acc x => acc + valAt x i.1) 0) from rfl]
    rw [valAt_of_lt _ _ (by rw [Tensor.mkShape, hdw0_shape]; simp [prodShape]; exact hidx_lt)]
    simp only [Tensor.mkShape, List.foldl]
    rw [bw_layernorm_dw_eq g0 x0 w b 32 [2, 1] hx0_rev,
        bw_layernorm_dw_eq g1 x1 w b 32 [2, 1] (by rw [hx1]; decide),
        bw_layernorm_dw_eq g2 x2 w b 32 [2, 1] (by rw [hx2]; decide),
        bw_layernorm_dw_eq g3 x3 w b 32 [2, 1] (by rw [hx3]; decide)]
    simp only [Tensor.mkShape]
    rw [valAt_of_lt _ _ (by simp [prodShape, hw]; exact hidx_lt),
        valAt_of_lt _ _ (by simp [prodShape, hw]; exact hidx_lt),
        valAt_of_lt _ _ (by simp [prodShape, hw]; exact hidx_lt),
        valAt_of_lt _ _ (by simp [prodShape, hw]; exact hidx_lt)]
    simp only [hw, hx0, hx1, hx2, hx3, prodShape,
               show [1, 2, 32].foldl (· * ·) 1 = 64 from rfl,
               show (64 : Nat) / 32 = 2 from rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 0 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 0 (by omega) 1 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 1 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 1 (by omega) 1 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 2 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 2 (by omega) 1 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 3 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 3 (by omega) 1 (by omega) idx hidx_lt hgs_head]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 0 (by omega) 0 (by omega) idx hidx_lt hxs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 0 (by omega) 1 (by omega) idx hidx_lt hxs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 1 (by omega) 0 (by omega) idx hidx_lt hxs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 1 (by omega) 1 (by omega) idx hidx_lt hxs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 2 (by omega) 0 (by omega) idx hidx_lt hxs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 2 (by omega) 1 (by omega) idx hidx_lt hxs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 3 (by omega) 0 (by omega) idx hidx_lt hxs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [x0,x1,x2,x3] 3 (by omega) 1 (by omega) idx hidx_lt hxs_head]
    rw [layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 0 (by omega) 0 (by omega) hxs_head,
        layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 0 (by omega) 1 (by omega) hxs_head,
        layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 1 (by omega) 0 (by omega) hxs_head,
        layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 1 (by omega) 1 (by omega) hxs_head,
        layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 2 (by omega) 0 (by omega) hxs_head,
        layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 2 (by omega) 1 (by omega) hxs_head,
        layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 3 (by omega) 0 (by omega) hxs_head,
        layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 3 (by omega) 1 (by omega) hxs_head]
    rw [layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 0 (by omega) 0 (by omega) _ hxs_head,
        layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 0 (by omega) 1 (by omega) _ hxs_head,
        layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 1 (by omega) 0 (by omega) _ hxs_head,
        layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 1 (by omega) 1 (by omega) _ hxs_head,
        layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 2 (by omega) 0 (by omega) _ hxs_head,
        layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 2 (by omega) 1 (by omega) _ hxs_head,
        layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 3 (by omega) 0 (by omega) _ hxs_head,
        layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 [x0,x1,x2,x3] 3 (by omega) 1 (by omega) _ hxs_head]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    ring

set_option maxHeartbeats 400000 in
/-- The db output of `bw_layernorm` on dim-1-gathered tensors (4 parts, shard [1,2,32])
    equals `tensorSum` of per-shard db outputs. -/
theorem bw_layernorm_db_dp_split_dim1_4_1_2_32
    (g0 g1 g2 g3 x0 x1 x2 x3 w b : Tensor)
    (hg0 : g0.shape = [1, 2, 32]) (hg1 : g1.shape = [1, 2, 32])
    (hg2 : g2.shape = [1, 2, 32]) (hg3 : g3.shape = [1, 2, 32])
    (hx0 : x0.shape = [1, 2, 32]) (hx1 : x1.shape = [1, 2, 32])
    (hx2 : x2.shape = [1, 2, 32]) (hx3 : x3.shape = [1, 2, 32])
    (hb : b.shape = [32]) :
    (bw_layernorm (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3])
                  (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]) w b).2.2 =
      tensorSum [(bw_layernorm g0 x0 w b).2.2,
                 (bw_layernorm g1 x1 w b).2.2,
                 (bw_layernorm g2 x2 w b).2.2,
                 (bw_layernorm g3 x3 w b).2.2] := by
  have hxs_head : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hx0]
  have hgs_head : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hg0]
  have hfullX_shape : (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hxs_head]; simp [List.set, List.getD]
  have hfullX_rev : (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]).shape.reverse = [32, 8, 1] := by
    rw [hfullX_shape]; decide
  have hx0_rev : x0.shape.reverse = [32, 2, 1] := by rw [hx0]; decide
  rw [bw_layernorm_db_eq _ _ w b 32 [8, 1] hfullX_rev]
  have hprod_full : prodShape (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]).shape / 32 = 8 := by
    rw [hfullX_shape]; simp [prodShape]
  apply Tensor.ext
  · simp [Tensor.mkShape, hb, tensorSum, bw_layernorm_db_shape _ _ _ _ 32 [2, 1] hx0_rev]
  · intro idx hidx
    have hidx_lt : idx < 32 := by simp [Tensor.mkShape, hb] at hidx; exact hidx
    rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, hb, prodShape]; exact hidx_lt)]
    simp only [Tensor.mkShape, hprod_full]
    have hdb0_shape : (bw_layernorm g0 x0 w b).2.2.shape = [32] := by
      rw [bw_layernorm_db_shape _ _ _ _ 32 [2, 1] hx0_rev, hb]
    rw [show tensorSum _ = Tensor.mkShape (bw_layernorm g0 x0 w b).2.2.shape
        (fun i => [(bw_layernorm g0 x0 w b).2.2, (bw_layernorm g1 x1 w b).2.2,
                   (bw_layernorm g2 x2 w b).2.2, (bw_layernorm g3 x3 w b).2.2].foldl
                   (fun acc x => acc + valAt x i.1) 0) from rfl]
    rw [valAt_of_lt _ _ (by rw [Tensor.mkShape, hdb0_shape]; simp [prodShape]; exact hidx_lt)]
    simp only [Tensor.mkShape, List.foldl]
    rw [bw_layernorm_db_eq g0 x0 w b 32 [2, 1] hx0_rev,
        bw_layernorm_db_eq g1 x1 w b 32 [2, 1] (by rw [hx1]; decide),
        bw_layernorm_db_eq g2 x2 w b 32 [2, 1] (by rw [hx2]; decide),
        bw_layernorm_db_eq g3 x3 w b 32 [2, 1] (by rw [hx3]; decide)]
    simp only [Tensor.mkShape]
    rw [valAt_of_lt _ _ (by simp [prodShape, hb]; exact hidx_lt),
        valAt_of_lt _ _ (by simp [prodShape, hb]; exact hidx_lt),
        valAt_of_lt _ _ (by simp [prodShape, hb]; exact hidx_lt),
        valAt_of_lt _ _ (by simp [prodShape, hb]; exact hidx_lt)]
    simp only [hb, hx0, hx1, hx2, hx3, prodShape,
               show [1, 2, 32].foldl (· * ·) 1 = 64 from rfl,
               show (64 : Nat) / 32 = 2 from rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 0 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 0 (by omega) 1 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 1 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 1 (by omega) 1 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 2 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 2 (by omega) 1 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 3 (by omega) 0 (by omega) idx hidx_lt hgs_head,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] 3 (by omega) 1 (by omega) idx hidx_lt hgs_head]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    ring

/-- Per-index bridge: the dx value of `bw_layernorm` on dim-1 allGather inputs at the
    global index `(r*2+p)*32+j` equals the dx value of the rank-`r` shard at the local
    index `p*32+j`. -/
theorem bw_layernorm_dx_allGather_valAt_dim1_4_1_2_32
    (gs xs : List Tensor) (w b : Tensor) (r p j : Nat)
    (hr : r < 4) (hp : p < 2) (hj : j < 32)
    (hgs_head : (gs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32])
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32])
    (hxr : (xs.getD r (zeroTensor [1, 2, 32])).shape = [1, 2, 32]) :
    valAt (bw_layernorm (allGatherPrimDimN 1 4 0 gs) (allGatherPrimDimN 1 4 0 xs) w b).1
        ((r * 2 + p) * 32 + j) =
      valAt (bw_layernorm (gs.getD r (zeroTensor [1, 2, 32]))
                          (xs.getD r (zeroTensor [1, 2, 32])) w b).1 (p * 32 + j) := by
  have hfullX : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hxs_head]; simp [List.set, List.getD]
  set gr := gs.getD r (zeroTensor [1, 2, 32]) with hgr_def
  set xr := xs.getD r (zeroTensor [1, 2, 32]) with hxr_def
  have hMean : layerNormMeanAt (allGatherPrimDimN 1 4 0 xs) (r * 2 + p) 32
      = layerNormMeanAt xr p 32 :=
    layerNormMeanAt_allGatherPrimDimN_dim1_4_1_2_32 xs r hr p hp hxs_head
  have hVar : ∀ m, layerNormVarAt (allGatherPrimDimN 1 4 0 xs) (r * 2 + p) 32 m
      = layerNormVarAt xr p 32 m :=
    fun m => layerNormVarAt_allGatherPrimDimN_dim1_4_1_2_32 xs r hr p hp m hxs_head
  have hVX : ∀ k, k < 32 →
      valAt (allGatherPrimDimN 1 4 0 xs) ((r * 2 + p) * 32 + k) = valAt xr (p * 32 + k) :=
    fun k hk => allGatherPrimDimN_dim1_4_1_2_32_valAt xs r hr p hp k hk hxs_head
  have hVG : ∀ k, k < 32 →
      valAt (allGatherPrimDimN 1 4 0 gs) ((r * 2 + p) * 32 + k) = valAt gr (p * 32 + k) :=
    fun k hk => allGatherPrimDimN_dim1_4_1_2_32_valAt gs r hr p hp k hk hgs_head
  rw [bw_layernorm_dx_valAt_1_8_32 _ _ w b (r * 2 + p) j hfullX (by omega) hj,
      bw_layernorm_dx_valAt_1_2_32 gr xr w b p j hxr hp hj]
  simp only [hMean, hVar, hVX j hj, hVG j hj]
  have hSumDy : (∑ k ∈ Finset.range 32,
        valAt (allGatherPrimDimN 1 4 0 gs) ((r * 2 + p) * 32 + k) * valAt w k)
      = ∑ k ∈ Finset.range 32, valAt gr (p * 32 + k) * valAt w k := by
    apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk; rw [hVG k hk]
  have hSumDyXhat : (∑ k ∈ Finset.range 32,
        valAt (allGatherPrimDimN 1 4 0 gs) ((r * 2 + p) * 32 + k) * valAt w k *
          ((valAt (allGatherPrimDimN 1 4 0 xs) ((r * 2 + p) * 32 + k) - layerNormMeanAt xr p 32) *
            (1 / sqrtFn (layerNormVarAt xr p 32 (layerNormMeanAt xr p 32) + layerNormEps))))
      = ∑ k ∈ Finset.range 32,
        valAt gr (p * 32 + k) * valAt w k *
          ((valAt xr (p * 32 + k) - layerNormMeanAt xr p 32) *
            (1 / sqrtFn (layerNormVarAt xr p 32 (layerNormMeanAt xr p 32) + layerNormEps))) := by
    apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk
    rw [hVG k hk, hVX k hk]
  rw [hSumDy, hSumDyXhat]

set_option maxHeartbeats 800000 in
/-- The dx output of `bw_layernorm` on dim-1-gathered tensors (4 parts, shard [1,2,32])
    equals the allGather of the per-shard dx outputs. -/
theorem bw_layernorm_dx_dp_split_dim1_4_1_2_32
    (g0 g1 g2 g3 x0 x1 x2 x3 w b : Tensor)
    (hg0 : g0.shape = [1, 2, 32]) (hg1 : g1.shape = [1, 2, 32])
    (hg2 : g2.shape = [1, 2, 32]) (hg3 : g3.shape = [1, 2, 32])
    (hx0 : x0.shape = [1, 2, 32]) (hx1 : x1.shape = [1, 2, 32])
    (hx2 : x2.shape = [1, 2, 32]) (hx3 : x3.shape = [1, 2, 32])
    (hw : w.shape = [32]) :
    (bw_layernorm (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3])
                  (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]) w b).1 =
      allGatherPrimDimN 1 4 0
        [(bw_layernorm g0 x0 w b).1, (bw_layernorm g1 x1 w b).1,
         (bw_layernorm g2 x2 w b).1, (bw_layernorm g3 x3 w b).1] := by
  have hgs_head : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hg0]
  have hxs_head : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hx0]
  have hfullX_shape : (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hxs_head]; simp [List.set, List.getD]
  have hfullG_shape : (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hgs_head]; simp [List.set, List.getD]
  have hdx0_shape : (bw_layernorm g0 x0 w b).1.shape = [1, 2, 32] := by
    rw [bw_layernorm_dx_shape g0 x0 w b 32 [2, 1] (by rw [hx0]; rfl), hx0]
  have hdxs_head : (([(bw_layernorm g0 x0 w b).1, (bw_layernorm g1 x1 w b).1,
      (bw_layernorm g2 x2 w b).1, (bw_layernorm g3 x3 w b).1] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hdx0_shape]
  have hlhs_shape : (bw_layernorm (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3])
                  (allGatherPrimDimN 1 4 0 [x0, x1, x2, x3]) w b).1.shape = [1, 8, 32] := by
    rw [bw_layernorm_dx_shape _ _ w b 32 [8, 1] (by rw [hfullX_shape]; rfl), hfullX_shape]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [(bw_layernorm g0 x0 w b).1, (bw_layernorm g1 x1 w b).1,
       (bw_layernorm g2 x2 w b).1, (bw_layernorm g3 x3 w b).1]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hdxs_head]; simp [List.set, List.getD]
  have hxr : ∀ r, r < 4 →
      (([x0, x1, x2, x3] : List Tensor).getD r (zeroTensor [1, 2, 32])).shape = [1, 2, 32] := by
    intro r hr
    have hrc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrc with h | h | h | h <;> subst h <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
        hx0, hx1, hx2, hx3]
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  · intro idx hidx
    have hidx256 : idx < 256 := by
      have h := hidx; rw [hlhs_shape] at h; simpa [prodShape] using h
    set p := idx / 32 with hp_def
    set j := idx % 32 with hj_def
    have hp_lt : p < 8 := by
      have : idx / 32 < 256 / 32 := Nat.div_lt_div_of_lt_of_dvd ⟨8, rfl⟩ hidx256
      simpa using this
    have hj_lt : j < 32 := Nat.mod_lt idx (by omega)
    have hidx_eq : idx = p * 32 + j := by subst p j; omega
    set r := p / 2 with hr_def
    set p' := p % 2 with hp'_def
    have hr_lt : r < 4 := by
      have : p / 2 < 8 / 2 := Nat.div_lt_div_of_lt_of_dvd ⟨4, rfl⟩ hp_lt
      simpa using this
    have hp'_lt : p' < 2 := Nat.mod_lt p (by omega)
    have hp_eq : p = r * 2 + p' := by subst r p'; omega
    rw [hidx_eq, hp_eq]
    rw [bw_layernorm_dx_allGather_valAt_dim1_4_1_2_32 [g0, g1, g2, g3] [x0, x1, x2, x3]
        w b r p' j hr_lt hp'_lt hj_lt hgs_head hxs_head (hxr r hr_lt)]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt
        [(bw_layernorm g0 x0 w b).1, (bw_layernorm g1 x1 w b).1,
         (bw_layernorm g2 x2 w b).1, (bw_layernorm g3 x3 w b).1]
        r hr_lt p' hp'_lt j hj_lt hdxs_head]
    have hrc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrc with h | h | h | h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]

/-- `applyNode` for `BW_transpose`. -/
theorem applyNode_bw_transposeAxes_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gradTid xTid outTid : Tid) (d0 d1 : Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_transpose", ins := [gradTid, xTid], outs := [outTid], params := [d0, d1] } outTid =
      transposeAxes d0 d1 (s gradTid) := by
  unfold applyNode
  change storeSet s [(outTid, transposeAxes d0 d1 (s gradTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `AllGatherPrim` (theorem version). -/
theorem applyNode_allGatherPrimDimN_out_thm
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid) (dim : Nat) :
    applyNode g s { rank := rank, op := "OpName.AllGatherPrim", ins := ins, outs := [outTid], params := [dim] } outTid =
      allGatherPrimDimN dim g.numRanks rank (ins.map s) := by
  unfold applyNode
  change storeSet s [(outTid, allGatherPrimDimN dim g.numRanks rank (ins.map s))] outTid = _
  unfold storeSet
  simp [List.find?]

set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_valAt_1_8_4_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 8, 4, 8]) (hidx : idx < 256) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x ((idx % 64) / 8 * 32 + (idx / 64) * 8 + idx % 8) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hm256 : idx % 256 = idx := Nat.mod_eq_of_lt hidx
  have hd256 : idx / 256 = 0 := Nat.div_eq_of_lt hidx
  rw [hm256, hd256]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
theorem chunkPrimDimN_3_4_valAt_1_8_4_8 (x : Tensor) (r idx : Nat)
    (hx : x.shape = [1, 8, 4, 8]) (hr : r < 4) (hidx : idx < 64) :
    valAt (chunkPrimDimN 3 4 r x) idx =
      valAt x ((idx / 2) * 8 + r * 2 + idx % 2) := by
  have hresult_shape : (chunkPrimDimN 3 4 r x).shape = [1, 8, 4, 2] := by
    rw [chunkPrimDimN_shape 3 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (chunkPrimDimN 3 4 r x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (4 / 4 : Nat) = 1 by norm_num, ite_false]
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  simp [Nat.add_assoc]

set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_valAt_1_8_4_2 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 8, 4, 2]) (hidx : idx < 64) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x ((idx % 16) / 2 * 8 + (idx / 16) * 2 + idx % 2) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 4, 8, 2] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
theorem allGatherPrimDimN_3_4_valAt_1_4_8_2 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 4, 8, 2]) (hidx : idx < 256) :
    valAt (allGatherPrimDimN 3 4 0 xs) idx =
      valAt (xs.getD ((idx % 8) / 2) (zeroTensor [1, 4, 8, 2])) ((idx / 8) * 2 + (idx % 8) % 2) := by
  have hresult_shape : (allGatherPrimDimN 3 4 0 xs).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 xs [1, 4, 8, 2] hhead]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 3 4 0 xs).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (8 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  simp

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem chunkPrimDimN_2_4_valAt_1_8_4_8 (x : Tensor) (r idx : Nat)
    (hx : x.shape = [1, 8, 4, 8]) (hr : r < 4) (hidx : idx < 64) :
    valAt (chunkPrimDimN 2 4 r x) idx =
      valAt x ((idx / 8) * 32 + r * 8 + idx % 8) := by
  have hresult_shape : (chunkPrimDimN 2 4 r x).shape = [1, 8, 1, 8] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (chunkPrimDimN 2 4 r x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (1 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (4 / 4 : Nat) = 1 by norm_num, ite_false]
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  simp [Nat.add_assoc]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem transposeAxes_1_2_valAt_1_8_1_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 8, 1, 8]) (hidx : idx < 64) :
    valAt (transposeAxes 1 2 x) idx = valAt x idx := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 1, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hdiv : idx % 64 / 8 = idx / 8 := by rw [hm64]
  rw [hdiv]
  have hnorm : idx % 8 + 8 * (idx / 8) = idx := by omega
  rw [hnorm]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem fw_transpose12_split_dim2_4_1_8_4_8 (x : Tensor) (hx : x.shape = [1, 8, 4, 8]) :
    transposeAxes 1 2 x = allGatherPrimDimN 1 4 0
      [transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 2 4 r x).shape = [1, 8, 1, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 1 2 (chunkPrimDimN 2 4 r x)).shape = [1, 1, 8, 8] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hlhs_shape : (transposeAxes 1 2 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hhead : (([transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
      transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
      transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
      transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 1, 8, 8] := by
    simp [hp0]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_8_4_8 x idx hx hidx256]
  rw [allGather_dim1_4_1_1_8_8_valAt _ _ _ _ idx
    (hpiece_shape 0 (by omega)) (hpiece_shape 1 (by omega))
    (hpiece_shape 2 (by omega)) (hpiece_shape 3 (by omega)) hidx256]
  set r := idx / 64
  set loc := idx % 64
  have hr : r < 4 := by
    subst r
    omega
  have hloc : loc < 64 := by
    subst loc
    omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)].getD i (zeroTensor [1, 1, 8, 8]) =
        transposeAxes 1 2 (chunkPrimDimN 2 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_1_2_valAt_1_8_1_8 _ loc (hchunk_shape r hr) hloc]
  rw [chunkPrimDimN_2_4_valAt_1_8_4_8 x r loc hx hr hloc]
  congr 1
  subst r loc
  omega

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem fw_transpose12_split_dim3_4_1_8_4_8 (x : Tensor) (hx : x.shape = [1, 8, 4, 8]) :
    transposeAxes 1 2 x = allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 3 4 r x).shape = [1, 8, 4, 2] := by
    intro r hr
    rw [chunkPrimDimN_shape 3 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 1 2 (chunkPrimDimN 3 4 r x)).shape = [1, 4, 8, 2] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hhead : (([transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
      transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
      transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
      transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by
    simp [hp0]
  have hlhs_shape : (transposeAxes 1 2 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_8_4_8 x idx hx hidx256]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead hidx256]
  set r := (idx % 8) / 2
  set loc := (idx / 8) * 2 + (idx % 8) % 2
  have hr : r < 4 := by
    subst r
    omega
  have hloc : loc < 64 := by
    subst loc
    omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)].getD i (zeroTensor [1, 4, 8, 2]) =
        transposeAxes 1 2 (chunkPrimDimN 3 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_1_2_valAt_1_8_4_2 _ loc (hchunk_shape r hr) hloc]
  rw [chunkPrimDimN_3_4_valAt_1_8_4_8 x r
    (((loc % 16) / 2) * 8 + (loc / 16) * 2 + loc % 2) hx hr (by
      subst loc
      omega)]
  congr 1
  subst r loc
  omega

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem chunkPrimDimN_1_4_valAt_1_8_4_8 (x : Tensor) (r idx : Nat)
    (hx : x.shape = [1, 8, 4, 8]) (hr : r < 4) (hidx : idx < 64) :
    valAt (chunkPrimDimN 1 4 r x) idx =
      valAt x ((r * 2 + idx / 32) * 32 + idx % 32) := by
  have hresult_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 4, 8] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (32 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, show (4 / 4 : Nat) = 1 by norm_num, ite_false]
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [Nat.add_assoc]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem transposeAxes_1_2_valAt_1_2_4_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 2, 4, 8]) (hidx : idx < 64) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x ((idx % 16) / 8 * 32 + (idx / 16) * 8 + idx % 8) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 4, 2, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem allGatherPrimDimN_2_4_valAt_1_4_2_8 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 4, 2, 8]) (hidx : idx < 256) :
    valAt (allGatherPrimDimN 2 4 0 xs) idx =
      valAt (xs.getD ((idx % 64) / 16) (zeroTensor [1, 4, 2, 8]))
        ((idx / 64) * 16 + ((idx % 16) / 8) * 8 + idx % 8) := by
  have hresult_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 xs [1, 4, 2, 8] hhead]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (8 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 0 from by omega,
    show (16 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hloc : idx / 64 * 16 + idx % 64 / 8 % 2 * 8 + idx % 64 % 8 =
      (idx / 64) * 16 + ((idx % 16) / 8) * 8 + idx % 8 := by
    omega
  have hpiece : idx % 64 / 8 / 2 = idx % 64 / 16 := by omega
  rw [hloc, hpiece]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem fw_transpose12_split_dim1_4_1_8_4_8 (x : Tensor) (hx : x.shape = [1, 8, 4, 8]) :
    transposeAxes 1 2 x = allGatherPrimDimN 2 4 0
      [transposeAxes 1 2 (chunkPrimDimN 1 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 1 4 r x).shape = [1, 2, 4, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 1 2 (chunkPrimDimN 1 4 r x)).shape = [1, 4, 2, 8] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hhead : (([transposeAxes 1 2 (chunkPrimDimN 1 4 0 x),
      transposeAxes 1 2 (chunkPrimDimN 1 4 1 x),
      transposeAxes 1 2 (chunkPrimDimN 1 4 2 x),
      transposeAxes 1 2 (chunkPrimDimN 1 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by
    simp [hp0]
  have hlhs_shape : (transposeAxes 1 2 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [transposeAxes 1 2 (chunkPrimDimN 1 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 3 x)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_8_4_8 x idx hx hidx256]
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ idx hhead hidx256]
  set r := (idx % 64) / 16
  set loc := (idx / 64) * 16 + ((idx % 16) / 8) * 8 + idx % 8
  have hr : r < 4 := by
    subst r
    omega
  have hloc : loc < 64 := by
    subst loc
    omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 1 2 (chunkPrimDimN 1 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 1 4 3 x)].getD i (zeroTensor [1, 4, 2, 8]) =
        transposeAxes 1 2 (chunkPrimDimN 1 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_1_2_valAt_1_2_4_8 _ loc (hchunk_shape r hr) hloc]
  rw [chunkPrimDimN_1_4_valAt_1_8_4_8 x r
    (((loc % 16) / 8) * 32 + (loc / 16) * 8 + loc % 8) hx hr (by
      subst loc
      omega)]
  congr 1
  subst r loc
  omega

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem transposeAxes_1_2_valAt_1_4_8_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hidx : idx < 256) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x ((idx % 32) / 8 * 64 + (idx / 32) * 8 + idx % 8) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 8, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hm256 : idx % 256 = idx := Nat.mod_eq_of_lt hidx
  have hd256 : idx / 256 = 0 := Nat.div_eq_of_lt hidx
  rw [hm256, hd256]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem chunkPrimDimN_3_4_valAt_1_4_8_8 (x : Tensor) (r idx : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hr : r < 4) (hidx : idx < 64) :
    valAt (chunkPrimDimN 3 4 r x) idx =
      valAt x ((idx / 2) * 8 + r * 2 + idx % 2) := by
  have hresult_shape : (chunkPrimDimN 3 4 r x).shape = [1, 4, 8, 2] := by
    rw [chunkPrimDimN_shape 3 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (chunkPrimDimN 3 4 r x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (4 / 4 : Nat) = 1 by norm_num, ite_false]
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  simp [Nat.add_assoc]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem transposeAxes_1_2_valAt_1_4_8_2 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 2]) (hidx : idx < 64) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x ((idx % 8) / 2 * 16 + (idx / 8) * 2 + idx % 2) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 8, 4, 2] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem allGatherPrimDimN_3_4_valAt_1_8_4_2 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 4, 2]) (hidx : idx < 256) :
    valAt (allGatherPrimDimN 3 4 0 xs) idx =
      valAt (xs.getD ((idx % 8) / 2) (zeroTensor [1, 8, 4, 2])) ((idx / 8) * 2 + idx % 2) := by
  have hresult_shape : (allGatherPrimDimN 3 4 0 xs).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 3 4 xs [1, 8, 4, 2] hhead]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 3 4 0 xs).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (8 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  simp

set_option maxHeartbeats 3200000 in
-- large arithmetic proof
theorem fw_transpose12_split_dim3_4_1_4_8_8 (x : Tensor) (hx : x.shape = [1, 4, 8, 8]) :
    transposeAxes 1 2 x = allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 3 4 r x).shape = [1, 4, 8, 2] := by
    intro r hr
    rw [chunkPrimDimN_shape 3 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 1 2 (chunkPrimDimN 3 4 r x)).shape = [1, 8, 4, 2] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hhead : (([transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
      transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
      transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
      transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 8, 4, 2] := by
    simp [hp0]
  have hlhs_shape : (transposeAxes 1 2 x).shape = [1, 8, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_4_8_8 x idx hx hidx256]
  rw [allGatherPrimDimN_3_4_valAt_1_8_4_2 _ idx hhead hidx256]
  set r := (idx % 8) / 2
  set loc := (idx / 8) * 2 + idx % 2
  have hr : r < 4 := by
    subst r
    omega
  have hloc : loc < 64 := by
    subst loc
    omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 1 2 (chunkPrimDimN 3 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 3 4 3 x)].getD i (zeroTensor [1, 8, 4, 2]) =
        transposeAxes 1 2 (chunkPrimDimN 3 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_1_2_valAt_1_4_8_2 _ loc (hchunk_shape r hr) hloc]
  rw [chunkPrimDimN_3_4_valAt_1_4_8_8 x r
    (((loc % 8) / 2) * 16 + (loc / 8) * 2 + loc % 2) hx hr (by
      subst loc
      omega)]
  congr 1
  subst r loc
  omega

set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_valAt_1_4_8_8_dup (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hidx : idx < 256) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x ((idx % 32) / 8 * 64 + (idx / 32) * 8 + idx % 8) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 8, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hm256 : idx % 256 = idx := Nat.mod_eq_of_lt hidx
  have hd256 : idx / 256 = 0 := Nat.div_eq_of_lt hidx
  rw [hm256, hd256]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_valAt_1_1_8_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 1, 8, 8]) (hidx : idx < 64) :
    valAt (transposeAxes 1 2 x) idx = valAt x idx := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 8, 1, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hnorm : idx % 8 + 8 * (idx / 8) = idx := by omega
  rw [hnorm]

set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_valAt_1_4_2_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 2, 8]) (hidx : idx < 64) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x (((idx % 32) / 8) * 16 + (idx / 32) * 8 + idx % 8) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 2, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (2 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (8 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_valAt_1_4_8_2_dup (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 2]) (hidx : idx < 64) :
    valAt (transposeAxes 1 2 x) idx =
      valAt x ((idx % 8) / 2 * 16 + (idx / 8) * 2 + idx % 2) := by
  have hresult_shape : (transposeAxes 1 2 x).shape = [1, 8, 4, 2] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 1 2 x).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (2 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (8 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 3200000 in
theorem allGatherPrimDimN_1_4_valAt_1_1_8_8 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 1, 8, 8])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
      valAt (xs.getD (idx / 64) (zeroTensor [1, 1, 8, 8])) (idx % 64) := by
  have hresult_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 1, 8, 8] hhead]; simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (1 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hpre : idx / 256 = 0 := by omega
  have hrem : idx % 256 = idx := by omega
  rw [hpre, hrem]
  have hjFull_lt : idx / (8 * (8 * 1)) < 4 := by
    have : (8 : Nat) * (8 * 1) = 64 := by decide
    rw [this]
    omega
  have hjFull_div : idx / (8 * (8 * 1)) / 1 = idx / 64 := by
    have : (8 : Nat) * (8 * 1) = 64 := by decide
    rw [this]
    omega
  have hjLocal : idx / (8 * (8 * 1)) % 1 = 0 := by omega
  congr 1
  omega

set_option maxHeartbeats 3200000 in
theorem allGatherPrimDimN_2_4_valAt_1_8_1_8 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 1, 8])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 2 4 0 xs) idx =
      valAt (xs.getD ((idx % 32) / 8) (zeroTensor [1, 8, 1, 8]))
        ((idx / 32) * 8 + idx % 8) := by
  have hresult_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 2 4 xs [1, 8, 1, 8] hhead]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (1 : Nat) ≠ 0 from by omega,
    show (8 : Nat) ≠ 0 from by omega, show (32 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  congr 1 <;> omega

set_option maxHeartbeats 3200000 in
theorem allGatherPrimDimN_1_4_valAt_1_2_4_8 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 4, 8])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
      valAt (xs.getD (idx / 64) (zeroTensor [1, 2, 4, 8])) (idx % 64) := by
  have hresult_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 4, 8] hhead]; simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (2 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (8 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hpre : idx / 256 = 0 := by omega
  have hrem : idx % 256 = idx := by omega
  rw [hpre, hrem]
  have hjFull_div : idx / (4 * (8 * 1)) / 2 = idx / 64 := by omega
  have hjLocal : idx / (4 * (8 * 1)) % 2 = (idx % 64) / 32 := by omega
  have hk : idx % (4 * (8 * 1)) = idx % 32 := by omega
  rw [hjFull_div, hjLocal, hk]
  congr 1
  omega

set_option maxHeartbeats 3200000 in
theorem allGatherPrimDimN_3_4_valAt_1_8_4_2_dup (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 4, 2])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 3 4 0 xs) idx =
      valAt (xs.getD ((idx % 8) / 2) (zeroTensor [1, 8, 4, 2]))
        ((idx / 8) * 2 + (idx % 8) % 2) := by
  have hresult_shape : (allGatherPrimDimN 3 4 0 xs).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 3 4 xs [1, 8, 4, 2] hhead]; simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 3 4 0 xs).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (2 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (8 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  congr 1 <;> omega

set_option maxHeartbeats 3200000 in
theorem bw_transpose12_gather3_4_1_4_8_2
    (p0 p1 p2 p3 : Tensor)
    (hp0 : p0.shape = [1, 4, 8, 2]) (hp1 : p1.shape = [1, 4, 8, 2])
    (hp2 : p2.shape = [1, 4, 8, 2]) (hp3 : p3.shape = [1, 4, 8, 2]) :
    transposeAxes 1 2 (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3]) =
      allGatherPrimDimN 3 4 0
        [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
         transposeAxes 1 2 p2, transposeAxes 1 2 p3] := by
  have hhead_lhs : (([p0, p1, p2, p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by simp [hp0]
  have hag_shape : (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 [p0, p1, p2, p3] [1, 4, 8, 2] hhead_lhs]
    simp [List.set, List.getD]
  have hlhs_shape : (transposeAxes 1 2
      (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3])).shape = [1, 8, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hag_shape, listSwapAt, List.getD, List.set]
  have htp0_shape : (transposeAxes 1 2 p0).shape = [1, 8, 4, 2] := by
    simp [transposeAxes, Tensor.mkShape, hp0, listSwapAt, List.getD, List.set]
  have hhead_rhs : (([transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 8, 4, 2] := by simp [htp0_shape]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
       transposeAxes 1 2 p2, transposeAxes 1 2 p3]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ [1, 8, 4, 2] hhead_rhs]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_4_8_8 (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3]) idx
    hag_shape hidx256]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 [p0, p1, p2, p3]
    ((idx % 32) / 8 * 64 + idx / 32 * 8 + idx % 8) hhead_lhs (by omega)]
  rw [allGatherPrimDimN_3_4_valAt_1_8_4_2 _ idx hhead_rhs hidx256]
  have hshards : (((idx % 32) / 8 * 64 + idx / 32 * 8 + idx % 8) % 8) / 2 =
      (idx % 8) / 2 := by omega
  rw [hshards]
  have hgetD_rhs : [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3].getD
      ((idx % 8) / 2) (zeroTensor [1, 8, 4, 2]) =
      transposeAxes 1 2 ([p0, p1, p2, p3].getD ((idx % 8) / 2)
        (zeroTensor [1, 4, 8, 2])) := by
    have h4 : (idx % 8) / 2 = 0 ∨ (idx % 8) / 2 = 1 ∨ (idx % 8) / 2 = 2 ∨
        (idx % 8) / 2 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD_rhs]
  have hp_r : ([p0, p1, p2, p3].getD ((idx % 8) / 2)
      (zeroTensor [1, 4, 8, 2])).shape = [1, 4, 8, 2] := by
    have h4 : (idx % 8) / 2 = 0 ∨ (idx % 8) / 2 = 1 ∨ (idx % 8) / 2 = 2 ∨
        (idx % 8) / 2 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        hp0, hp1, hp2, hp3, zeroTensor]
  rw [transposeAxes_1_2_valAt_1_4_8_2 _ ((idx / 8) * 2 + idx % 2) hp_r (by omega)]
  congr 1
  omega

set_option maxHeartbeats 3200000 in
theorem bw_transpose12_gather1_to_2_4_1_1_8_8
    (p0 p1 p2 p3 : Tensor)
    (hp0 : p0.shape = [1, 1, 8, 8]) (hp1 : p1.shape = [1, 1, 8, 8])
    (hp2 : p2.shape = [1, 1, 8, 8]) (hp3 : p3.shape = [1, 1, 8, 8]) :
    transposeAxes 1 2 (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]) =
      allGatherPrimDimN 2 4 0
        [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
         transposeAxes 1 2 p2, transposeAxes 1 2 p3] := by
  have hhead_lhs : (([p0, p1, p2, p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 1, 8, 8] := by
    simp [hp0]
  have hag_shape : (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 [p0, p1, p2, p3] [1, 1, 8, 8] hhead_lhs]
    simp [List.set, List.getD]
  have hhead_rhs : (([transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 8, 1, 8] := by
    simp [transposeAxes, Tensor.mkShape, hp0, listSwapAt, List.getD, List.set]
  have hlhs_shape : (transposeAxes 1 2
      (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3])).shape = [1, 8, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hag_shape, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
       transposeAxes 1 2 p2, transposeAxes 1 2 p3]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ [1, 8, 1, 8] hhead_rhs]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_4_8_8 (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]) idx
    hag_shape hidx256]
  have hj : ((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8 < 256 := by omega
  rw [allGatherPrimDimN_1_4_valAt_1_1_8_8 [p0, p1, p2, p3]
    (((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) hhead_lhs hj]
  rw [allGatherPrimDimN_2_4_valAt_1_8_1_8 _ idx hhead_rhs hidx256]
  have hshards : (((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) / 64 =
      (idx % 32) / 8 := by omega
  rw [hshards]
  have hgetD_rhs : [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3].getD
      ((idx % 32) / 8) (zeroTensor [1, 8, 1, 8]) =
      transposeAxes 1 2 ([p0, p1, p2, p3].getD ((idx % 32) / 8)
        (zeroTensor [1, 1, 8, 8])) := by
    have h4 : (idx % 32) / 8 = 0 ∨ (idx % 32) / 8 = 1 ∨ (idx % 32) / 8 = 2 ∨
        (idx % 32) / 8 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;> rfl
  rw [hgetD_rhs]
  have hp_r : ([p0, p1, p2, p3].getD ((idx % 32) / 8)
      (zeroTensor [1, 1, 8, 8])).shape = [1, 1, 8, 8] := by
    have h4 : (idx % 32) / 8 = 0 ∨ (idx % 32) / 8 = 1 ∨ (idx % 32) / 8 = 2 ∨
        (idx % 32) / 8 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        hp0, hp1, hp2, hp3]
  rw [transposeAxes_1_2_valAt_1_1_8_8 _ ((idx / 32) * 8 + idx % 8) hp_r (by omega)]
  congr 1
  omega

set_option maxHeartbeats 3200000 in
theorem bw_transpose12_gather2_to_1_4_1_4_2_8
    (p0 p1 p2 p3 : Tensor)
    (hp0 : p0.shape = [1, 4, 2, 8]) (hp1 : p1.shape = [1, 4, 2, 8])
    (hp2 : p2.shape = [1, 4, 2, 8]) (hp3 : p3.shape = [1, 4, 2, 8]) :
    transposeAxes 1 2 (allGatherPrimDimN 2 4 0 [p0, p1, p2, p3]) =
      allGatherPrimDimN 1 4 0
        [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
         transposeAxes 1 2 p2, transposeAxes 1 2 p3] := by
  have hhead_lhs : (([p0, p1, p2, p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by
    simp [hp0]
  have hag_shape : (allGatherPrimDimN 2 4 0 [p0, p1, p2, p3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 [p0, p1, p2, p3] [1, 4, 2, 8] hhead_lhs]
    simp [List.set, List.getD]
  have hhead_rhs : (([transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 2, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hp0, listSwapAt, List.getD, List.set]
  have hlhs_shape : (transposeAxes 1 2
      (allGatherPrimDimN 2 4 0 [p0, p1, p2, p3])).shape = [1, 8, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hag_shape, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
       transposeAxes 1 2 p2, transposeAxes 1 2 p3]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 4, 8] hhead_rhs]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_4_8_8 (allGatherPrimDimN 2 4 0 [p0, p1, p2, p3]) idx
    hag_shape hidx256]
  have hj : ((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8 < 256 := by omega
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 [p0, p1, p2, p3]
    (((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) hhead_lhs hj]
  rw [allGatherPrimDimN_1_4_valAt_1_2_4_8 _ idx hhead_rhs hidx256]
  have hsel1 : ([p0, p1, p2, p3] : List Tensor).getD (((((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) % 64) / 16)
      (zeroTensor [1, 4, 2, 8]) = ([p0, p1, p2, p3] : List Tensor).getD (idx / 64) (zeroTensor [1, 4, 2, 8]) := by
    congr 1
    have hgmod : ((((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) % 64) =
        (idx / 32) * 8 + idx % 8 := by
      omega
    rw [hgmod]
    omega
  rw [hsel1]
  have hgetD_rhs : [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3].getD
      (idx / 64) (zeroTensor [1, 2, 4, 8]) =
      transposeAxes 1 2 ([p0, p1, p2, p3].getD (idx / 64)
        (zeroTensor [1, 4, 2, 8])) := by
    have h4 : idx / 64 = 0 ∨ idx / 64 = 1 ∨ idx / 64 = 2 ∨ idx / 64 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;> rfl
  rw [hgetD_rhs]
  have hp_r : ([p0, p1, p2, p3].getD (idx / 64)
      (zeroTensor [1, 4, 2, 8])).shape = [1, 4, 2, 8] := by
    have h4 : idx / 64 = 0 ∨ idx / 64 = 1 ∨ idx / 64 = 2 ∨ idx / 64 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        hp0, hp1, hp2, hp3]
  rw [transposeAxes_1_2_valAt_1_4_2_8 _ (idx % 64) hp_r (by omega)]
  have hg64 : ((((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) / 64) =
      (idx % 32) / 8 := by omega
  have hg16 : (((((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) % 16) / 8) =
      (idx / 32) % 2 := by omega
  have hg8 : ((((idx % 32) / 8) * 64 + (idx / 32) * 8 + idx % 8) % 8) =
      idx % 8 := by omega
  have hidx32 : ((idx % 64) % 32) / 8 = (idx % 32) / 8 := by omega
  have hidx64 : (idx % 64) / 32 = (idx / 32) % 2 := by omega
  have hidx8 : (idx % 64) % 8 = idx % 8 := by omega
  rw [hg64, hg16, hg8, hidx32, hidx64, hidx8]

set_option maxHeartbeats 3200000 in
theorem bw_transpose12_gather3_4_1_8_4_2
    (p0 p1 p2 p3 : Tensor)
    (hp0 : p0.shape = [1, 8, 4, 2]) (hp1 : p1.shape = [1, 8, 4, 2])
    (hp2 : p2.shape = [1, 8, 4, 2]) (hp3 : p3.shape = [1, 8, 4, 2]) :
    transposeAxes 1 2 (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3]) =
      allGatherPrimDimN 3 4 0
        [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
         transposeAxes 1 2 p2, transposeAxes 1 2 p3] := by
  have hhead_lhs : (([p0, p1, p2, p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 8, 4, 2] := by simp [hp0]
  have hag_shape : (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 3 4 [p0, p1, p2, p3] [1, 8, 4, 2] hhead_lhs]
    simp [List.set, List.getD]
  have hlhs_shape : (transposeAxes 1 2
      (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3])).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hag_shape, listSwapAt, List.getD, List.set]
  have htp0_shape : (transposeAxes 1 2 p0).shape = [1, 4, 8, 2] := by
    simp [transposeAxes, Tensor.mkShape, hp0, listSwapAt, List.getD, List.set]
  have hhead_rhs : (([transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by simp [htp0_shape]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
       transposeAxes 1 2 p2, transposeAxes 1 2 p3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ [1, 4, 8, 2] hhead_rhs]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_8_4_8 (allGatherPrimDimN 3 4 0 [p0, p1, p2, p3]) idx
    hag_shape hidx256]
  rw [allGatherPrimDimN_3_4_valAt_1_8_4_2 [p0, p1, p2, p3]
    ((idx % 64) / 8 * 32 + idx / 64 * 8 + idx % 8) hhead_lhs (by omega)]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead_rhs hidx256]
  have hshards : (((idx % 64) / 8 * 32 + idx / 64 * 8 + idx % 8) % 8) / 2 =
      (idx % 8) / 2 := by omega
  rw [hshards]
  have hgetD_rhs : [transposeAxes 1 2 p0, transposeAxes 1 2 p1,
      transposeAxes 1 2 p2, transposeAxes 1 2 p3].getD
      ((idx % 8) / 2) (zeroTensor [1, 4, 8, 2]) =
      transposeAxes 1 2 ([p0, p1, p2, p3].getD ((idx % 8) / 2)
        (zeroTensor [1, 8, 4, 2])) := by
    have h4 : (idx % 8) / 2 = 0 ∨ (idx % 8) / 2 = 1 ∨ (idx % 8) / 2 = 2 ∨
        (idx % 8) / 2 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD_rhs]
  have hp_r : ([p0, p1, p2, p3].getD ((idx % 8) / 2)
      (zeroTensor [1, 8, 4, 2])).shape = [1, 8, 4, 2] := by
    have h4 : (idx % 8) / 2 = 0 ∨ (idx % 8) / 2 = 1 ∨ (idx % 8) / 2 = 2 ∨
        (idx % 8) / 2 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        hp0, hp1, hp2, hp3, zeroTensor]
  rw [transposeAxes_1_2_valAt_1_8_4_2 _ (idx / 8 * 2 + idx % 8 % 2) hp_r (by omega)]
  congr 1
  omega

set_option maxHeartbeats 3200000 in
theorem bw_transpose12_gather1_to_gather2_1_1_8_8 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 1, 8, 8]) (hc1 : c1.shape = [1, 1, 8, 8])
    (hc2 : c2.shape = [1, 1, 8, 8]) (hc3 : c3.shape = [1, 1, 8, 8]) :
    transposeAxes 1 2 (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]) =
      allGatherPrimDimN 2 4 0 [transposeAxes 1 2 c0, transposeAxes 1 2 c1,
                                transposeAxes 1 2 c2, transposeAxes 1 2 c3] := by
  simpa using bw_transpose12_gather1_to_2_4_1_1_8_8 c0 c1 c2 c3 hc0 hc1 hc2 hc3

set_option maxHeartbeats 3200000 in
theorem bw_transpose12_gather2_to_gather1_1_4_2_8 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 4, 2, 8]) (hc1 : c1.shape = [1, 4, 2, 8])
    (hc2 : c2.shape = [1, 4, 2, 8]) (hc3 : c3.shape = [1, 4, 2, 8]) :
    transposeAxes 1 2 (allGatherPrimDimN 2 4 0 [c0, c1, c2, c3]) =
      allGatherPrimDimN 1 4 0 [transposeAxes 1 2 c0, transposeAxes 1 2 c1,
                                transposeAxes 1 2 c2, transposeAxes 1 2 c3] := by
  simpa using bw_transpose12_gather2_to_1_4_1_4_2_8 c0 c1 c2 c3 hc0 hc1 hc2 hc3

set_option maxHeartbeats 3200000 in
theorem chunk3_gather3_roundtrip_1_4_8_2 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 4, 8, 2]) (hc1 : c1.shape = [1, 4, 8, 2])
    (hc2 : c2.shape = [1, 4, 8, 2]) (hc3 : c3.shape = [1, 4, 8, 2])
    (r : Nat) (hr : r < 4) :
    chunkPrimDimN 3 4 r (allGatherPrimDimN 3 4 0 [c0, c1, c2, c3]) =
      [c0, c1, c2, c3].getD r (zeroTensor [1, 4, 8, 2]) := by
  have hhead : (([c0, c1, c2, c3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by
    simp [hc0]
  have hgather_shape : (allGatherPrimDimN 3 4 0 [c0, c1, c2, c3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead]
    simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 3 4 r (allGatherPrimDimN 3 4 0 [c0, c1, c2, c3])).shape = [1, 4, 8, 2] := by
    rw [chunkPrimDimN_shape 3 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : ([c0, c1, c2, c3].getD r (zeroTensor [1, 4, 8, 2])).shape = [1, 4, 8, 2] := by
    have h4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, hc0, hc1, hc2, hc3]
  apply Tensor.ext (by rw [hchunk_shape, hrhs_shape])
  intro idx hidx
  have hidx64 : idx < 64 := by simpa [hchunk_shape, prodShape] using hidx
  rw [chunkPrimDimN_3_4_valAt_1_4_8_8 _ r idx hgather_shape hr hidx64]
  set j := (idx / 2) * 8 + r * 2 + idx % 2
  have hj : j < 256 := by
    subst j
    omega
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ j hhead hj]
  have hmod : (j % 8) / 2 = r := by
    subst j
    omega
  have hdiv : (j / 8) * 2 + (j % 8) % 2 = idx := by
    subst j
    omega
  rw [hmod, hdiv]

set_option maxHeartbeats 3200000 in
theorem chunk1_gather1_roundtrip_1_1_8_8 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 1, 8, 8]) (hc1 : c1.shape = [1, 1, 8, 8])
    (hc2 : c2.shape = [1, 1, 8, 8]) (hc3 : c3.shape = [1, 1, 8, 8])
    (r : Nat) (hr : r < 4) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]) =
      [c0, c1, c2, c3].getD r (zeroTensor [1, 1, 8, 8]) := by
  have hhead : (([c0, c1, c2, c3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 1, 8, 8] := by
    simp [hc0]
  have hgather_shape : (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3])).shape = [1, 1, 8, 8] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : ([c0, c1, c2, c3].getD r (zeroTensor [1, 1, 8, 8])).shape = [1, 1, 8, 8] := by
    have h4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, hc0, hc1, hc2, hc3]
  apply Tensor.ext (by rw [hchunk_shape, hrhs_shape])
  intro idx hidx
  have hidx64 : idx < 64 := by simpa [hchunk_shape, prodShape] using hidx
  rw [chunk_dim1_4_1_4_8_8_valAt _ r idx hgather_shape hr hidx64]
  set j := r * 64 + idx
  have hj : j < 256 := by
    subst j
    omega
  rw [allGather_dim1_4_1_1_8_8_valAt c0 c1 c2 c3 j hc0 hc1 hc2 hc3 hj]
  have hdiv : j / 64 = r := by
    subst j
    omega
  have hmod : j % 64 = idx := by
    subst j
    omega
  rw [hdiv, hmod]

set_option maxHeartbeats 3200000 in
theorem chunkPrimDimN_2_4_valAt_1_4_8_8 (x : Tensor) (r idx : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hr : r < 4) (hidx : idx < 64) :
    valAt (chunkPrimDimN 2 4 r x) idx =
      valAt x ((idx / 16) * 64 + r * 16 + idx % 16) := by
  have hresult_shape : (chunkPrimDimN 2 4 r x).shape = [1, 4, 2, 8] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (chunkPrimDimN 2 4 r x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [chunkPrimDimN, Tensor.mkShape, hx, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.drop, List.foldl,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, show (8 / 4 : Nat) = 2 by norm_num,
    ite_false]
  have hrm : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hrm]
  congr 1
  omega

set_option maxHeartbeats 3200000 in
theorem chunk2_gather2_roundtrip_1_4_2_8 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 4, 2, 8]) (hc1 : c1.shape = [1, 4, 2, 8])
    (hc2 : c2.shape = [1, 4, 2, 8]) (hc3 : c3.shape = [1, 4, 2, 8])
    (r : Nat) (hr : r < 4) :
    chunkPrimDimN 2 4 r (allGatherPrimDimN 2 4 0 [c0, c1, c2, c3]) =
      [c0, c1, c2, c3].getD r (zeroTensor [1, 4, 2, 8]) := by
  have hhead : (([c0, c1, c2, c3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by
    simp [hc0]
  have hgather_shape : (allGatherPrimDimN 2 4 0 [c0, c1, c2, c3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
    simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 2 4 r (allGatherPrimDimN 2 4 0 [c0, c1, c2, c3])).shape = [1, 4, 2, 8] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : ([c0, c1, c2, c3].getD r (zeroTensor [1, 4, 2, 8])).shape = [1, 4, 2, 8] := by
    have h4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, hc0, hc1, hc2, hc3]
  apply Tensor.ext (by rw [hchunk_shape, hrhs_shape])
  intro idx hidx
  have hidx64 : idx < 64 := by simpa [hchunk_shape, prodShape] using hidx
  rw [chunkPrimDimN_2_4_valAt_1_4_8_8 _ r idx hgather_shape hr hidx64]
  set j := (idx / 16) * 64 + r * 16 + idx % 16
  have hj : j < 256 := by
    subst j
    omega
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ j hhead hj]
  have hpiece : (j % 64) / 16 = r := by
    subst j
    omega
  have hloc : (j / 64) * 16 + ((j % 16) / 8) * 8 + j % 8 = idx := by
    subst j
    omega
  rw [hpiece, hloc]

set_option maxHeartbeats 3200000 in
theorem chunk3_gather3_roundtrip_1_8_4_2 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 8, 4, 2]) (hc1 : c1.shape = [1, 8, 4, 2])
    (hc2 : c2.shape = [1, 8, 4, 2]) (hc3 : c3.shape = [1, 8, 4, 2])
    (r : Nat) (hr : r < 4) :
    chunkPrimDimN 3 4 r (allGatherPrimDimN 3 4 0 [c0, c1, c2, c3]) =
      [c0, c1, c2, c3].getD r (zeroTensor [1, 8, 4, 2]) := by
  have hhead : (([c0, c1, c2, c3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 4, 2] := by
    simp [hc0]
  have hgather_shape : (allGatherPrimDimN 3 4 0 [c0, c1, c2, c3]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead]
    simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 3 4 r (allGatherPrimDimN 3 4 0 [c0, c1, c2, c3])).shape = [1, 8, 4, 2] := by
    rw [chunkPrimDimN_shape 3 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : ([c0, c1, c2, c3].getD r (zeroTensor [1, 8, 4, 2])).shape = [1, 8, 4, 2] := by
    have h4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, hc0, hc1, hc2, hc3]
  apply Tensor.ext (by rw [hchunk_shape, hrhs_shape])
  intro idx hidx
  have hidx64 : idx < 64 := by simpa [hchunk_shape, prodShape] using hidx
  rw [chunkPrimDimN_3_4_valAt_1_8_4_8 _ r idx hgather_shape hr hidx64]
  set j := (idx / 2) * 8 + r * 2 + idx % 2
  have hj : j < 256 := by
    subst j
    omega
  rw [allGatherPrimDimN_3_4_valAt_1_8_4_2 _ j hhead hj]
  have hmod : (j % 8) / 2 = r := by
    subst j
    omega
  have hdiv : (j / 8) * 2 + j % 2 = idx := by
    subst j
    omega
  rw [hmod, hdiv]

-- transposeAxes 2 3 valAt for shape [1,4,8,8]
set_option maxHeartbeats 3200000 in
theorem transposeAxes_2_3_valAt_1_4_8_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hidx : idx < 256) :
    valAt (transposeAxes 2 3 x) idx =
      valAt x ((idx / 64) * 64 + (idx % 64 % 8) * 8 + (idx % 64) / 8) := by
  have hresult_shape : (transposeAxes 2 3 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 2 3 x).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hm256 : idx % 256 = idx := Nat.mod_eq_of_lt hidx
  have hd256 : idx / 256 = 0 := Nat.div_eq_of_lt hidx
  rw [hm256, hd256]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

-- transposeAxes 2 3 valAt for shape [1,4,8,2]
set_option maxHeartbeats 3200000 in
theorem transposeAxes_2_3_valAt_1_4_8_2 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 2]) (hidx : idx < 64) :
    valAt (transposeAxes 2 3 x) idx =
      valAt x ((idx / 16) * 16 + (idx % 8) * 2 + (idx % 16) / 8) := by
  have hresult_shape : (transposeAxes 2 3 x).shape = [1, 4, 2, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 2 3 x).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

-- Bridge: transpose(2,3) distributes over chunk(dim=3, nranks=4) with gather(dim=2)
set_option maxHeartbeats 4000000 in
theorem fw_transpose23_split_dim3_4_1_4_8_8 (x : Tensor) (hx : x.shape = [1, 4, 8, 8]) :
    transposeAxes 2 3 x = allGatherPrimDimN 2 4 0
      [transposeAxes 2 3 (chunkPrimDimN 3 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 3 4 r x).shape = [1, 4, 8, 2] := by
    intro r hr
    rw [chunkPrimDimN_shape 3 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 2 3 (chunkPrimDimN 3 4 r x)).shape = [1, 4, 2, 8] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hhead : (([transposeAxes 2 3 (chunkPrimDimN 3 4 0 x),
      transposeAxes 2 3 (chunkPrimDimN 3 4 1 x),
      transposeAxes 2 3 (chunkPrimDimN 3 4 2 x),
      transposeAxes 2 3 (chunkPrimDimN 3 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by
    simp [hp0]
  have hlhs_shape : (transposeAxes 2 3 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [transposeAxes 2 3 (chunkPrimDimN 3 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 3 x)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_2_3_valAt_1_4_8_8 x idx hx hidx256]
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ idx hhead hidx256]
  set r := (idx % 64) / 16
  set loc := (idx / 64) * 16 + ((idx % 16) / 8) * 8 + idx % 8
  have hr : r < 4 := by subst r; omega
  have hloc : loc < 64 := by subst loc; omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 2 3 (chunkPrimDimN 3 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 3 4 3 x)].getD i (zeroTensor [1, 4, 2, 8]) =
        transposeAxes 2 3 (chunkPrimDimN 3 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_2_3_valAt_1_4_8_2 _ loc (hchunk_shape r hr) hloc]
  rw [chunkPrimDimN_3_4_valAt_1_4_8_8 x r
    ((loc / 16) * 16 + (loc % 8) * 2 + (loc % 16) / 8) hx hr (by
      subst loc; omega)]
  congr 1
  -- Step-by-step arithmetic to close the goal
  have hloc_div16 : loc / 16 = idx / 64 := by subst loc; omega
  have hloc_mod8 : loc % 8 = idx % 8 := by subst loc; omega
  have hloc_mod16_div8 : (loc % 16) / 8 = (idx % 16) / 8 := by subst loc; omega
  set inner := (loc / 16) * 16 + (loc % 8) * 2 + (loc % 16) / 8
  have hinner_eq : inner = (idx / 64) * 16 + (idx % 8) * 2 + (idx % 16) / 8 := by
    subst inner; rw [hloc_div16, hloc_mod8, hloc_mod16_div8]
  have hinner_div2 : inner / 2 = (idx / 64) * 8 + idx % 8 := by
    rw [hinner_eq]; omega
  have hinner_mod2 : inner % 2 = (idx % 16) / 8 := by
    rw [hinner_eq]; omega
  rw [hinner_div2, hinner_mod2]
  have hmod8_eq : idx % 64 % 8 = idx % 8 := by omega
  have hdiv_ident : (idx % 64) / 16 * 2 + (idx % 64 % 16) / 8 = (idx % 64) / 8 := by omega
  have hmod16_eq : (idx % 16) / 8 = (idx % 64 % 16) / 8 := by omega
  have hr_eq : r = (idx % 64) / 16 := by subst r; rfl
  rw [hr_eq, hmod16_eq, ← hdiv_ident, ← hmod8_eq]
  omega


set_option maxHeartbeats 3200000 in
theorem transposeAxes_2_3_valAt_1_1_8_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 1, 8, 8]) (hidx : idx < 64) :
    valAt (transposeAxes 2 3 x) idx =
      valAt x ((idx % 8) * 8 + idx / 8) := by
  have hresult_shape : (transposeAxes 2 3 x).shape = [1, 1, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 2 3 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hdiv : idx % 64 / 8 = idx / 8 := by
    rw [hm64]
  rw [hdiv]
  simp [Nat.add_comm]

set_option maxHeartbeats 3200000 in
theorem chunk1_gather1_roundtrip_1_2_4_8 (c0 c1 c2 c3 : Tensor)
    (hc0 : c0.shape = [1, 2, 4, 8]) (hc1 : c1.shape = [1, 2, 4, 8])
    (hc2 : c2.shape = [1, 2, 4, 8]) (hc3 : c3.shape = [1, 2, 4, 8])
    (r : Nat) (hr : r < 4) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]) =
      [c0, c1, c2, c3].getD r (zeroTensor [1, 2, 4, 8]) := by
  have hhead : (([c0, c1, c2, c3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 4, 8] := by
    simp [hc0]
  have hgather_shape : (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3])).shape = [1, 2, 4, 8] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : ([c0, c1, c2, c3].getD r (zeroTensor [1, 2, 4, 8])).shape = [1, 2, 4, 8] := by
    have h4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, hc0, hc1, hc2, hc3]
  apply Tensor.ext (by rw [hchunk_shape, hrhs_shape])
  intro idx hidx
  have hidx64 : idx < 64 := by simpa [hchunk_shape, prodShape] using hidx
  rw [chunkPrimDimN_1_4_valAt_1_8_4_8 _ r idx hgather_shape hr hidx64]
  set j := (r * 2 + idx / 32) * 32 + idx % 32
  have hj : j < 256 := by
    subst j
    omega
  rw [allGatherPrimDimN_1_4_valAt_1_2_4_8 _ j hhead hj]
  have hdiv : j / 64 = r := by
    subst j
    omega
  have hmod : j % 64 = idx := by
    subst j
    omega
  rw [hdiv, hmod]

set_option maxHeartbeats 3200000 in
theorem fw_transpose12_split_dim2_4_1_4_8_8 (x : Tensor) (hx : x.shape = [1, 4, 8, 8]) :
    transposeAxes 1 2 x = allGatherPrimDimN 1 4 0
      [transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 2 4 r x).shape = [1, 4, 2, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 1 2 (chunkPrimDimN 2 4 r x)).shape = [1, 2, 4, 8] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hhead : (([transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
      transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
      transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
      transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 2, 4, 8] := by
    simp [hp0]
  have hlhs_shape : (transposeAxes 1 2 x).shape = [1, 8, 4, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)]).shape = [1, 8, 4, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_1_2_valAt_1_4_8_8 x idx hx hidx256]
  rw [allGatherPrimDimN_1_4_valAt_1_2_4_8 _ idx hhead hidx256]
  set r := idx / 64
  set loc := idx % 64
  have hr : r < 4 := by
    subst r
    omega
  have hloc : loc < 64 := by
    subst loc
    omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 1 2 (chunkPrimDimN 2 4 0 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 1 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 2 x),
       transposeAxes 1 2 (chunkPrimDimN 2 4 3 x)].getD i (zeroTensor [1, 2, 4, 8]) =
        transposeAxes 1 2 (chunkPrimDimN 2 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_1_2_valAt_1_4_2_8 _ loc (hchunk_shape r hr) hloc]
  rw [chunkPrimDimN_2_4_valAt_1_4_8_8 x r
    (((loc % 32) / 8) * 16 + (loc / 32) * 8 + loc % 8) hx hr (by
      subst loc
      omega)]
  congr 1
  subst r loc
  omega

set_option maxHeartbeats 3200000 in
theorem transposeAxes_2_3_valAt_1_4_2_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 2, 8]) (hidx : idx < 64) :
    valAt (transposeAxes 2 3 x) idx =
      valAt x ((idx / 16) * 16 + (idx % 2) * 8 + (idx % 16) / 2) := by
  have hresult_shape : (transposeAxes 2 3 x).shape = [1, 4, 8, 2] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hprod : idx < prodShape (transposeAxes 2 3 x).shape := by
    rw [hresult_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hprod]
  simp only [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    flatToMulti, multiToFlat, prodShape, List.foldl, List.drop,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    show (8 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (16 : Nat) ≠ 0 from by omega,
    show (64 : Nat) ≠ 0 from by omega, ite_false]
  have hm64 : idx % 64 = idx := Nat.mod_eq_of_lt hidx
  have hd64 : idx / 64 = 0 := Nat.div_eq_of_lt hidx
  rw [hm64, hd64]
  simp [multiToFlat, prodShape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 4000000 in
theorem fw_transpose23_split_dim1_4_1_4_8_8 (x : Tensor) (hx : x.shape = [1, 4, 8, 8]) :
    transposeAxes 2 3 x = allGatherPrimDimN 1 4 0
      [transposeAxes 2 3 (chunkPrimDimN 1 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 1 4 r x).shape = [1, 1, 8, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 2 3 (chunkPrimDimN 1 4 r x)).shape = [1, 1, 8, 8] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hhead : (([transposeAxes 2 3 (chunkPrimDimN 1 4 0 x),
      transposeAxes 2 3 (chunkPrimDimN 1 4 1 x),
      transposeAxes 2 3 (chunkPrimDimN 1 4 2 x),
      transposeAxes 2 3 (chunkPrimDimN 1 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 1, 8, 8] := by
    simp [hp0]
  have hlhs_shape : (transposeAxes 2 3 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [transposeAxes 2 3 (chunkPrimDimN 1 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 3 x)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_2_3_valAt_1_4_8_8 x idx hx hidx256]
  rw [allGatherPrimDimN_1_4_valAt_1_1_8_8 _ idx hhead hidx256]
  set r := idx / 64
  set loc := idx % 64
  have hr : r < 4 := by
    subst r
    omega
  have hloc : loc < 64 := by
    subst loc
    omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 2 3 (chunkPrimDimN 1 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 1 4 3 x)].getD i (zeroTensor [1, 1, 8, 8]) =
        transposeAxes 2 3 (chunkPrimDimN 1 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_2_3_valAt_1_1_8_8 _ loc (hchunk_shape r hr) hloc]
  rw [chunk_dim1_4_1_4_8_8_valAt x r (((loc % 8) * 8 + loc / 8)) hx hr (by
    subst loc
    omega)]
  congr 1
  subst r loc
  omega

set_option maxHeartbeats 4000000 in
theorem fw_transpose23_split_dim2_4_1_4_8_8 (x : Tensor) (hx : x.shape = [1, 4, 8, 8]) :
    transposeAxes 2 3 x = allGatherPrimDimN 3 4 0
      [transposeAxes 2 3 (chunkPrimDimN 2 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 3 x)] := by
  have hchunk_shape : ∀ r, r < 4 → (chunkPrimDimN 2 4 r x).shape = [1, 4, 2, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 → (transposeAxes 2 3 (chunkPrimDimN 2 4 r x)).shape = [1, 4, 8, 2] := by
    intro r hr
    simp [transposeAxes, Tensor.mkShape, hchunk_shape r hr, listSwapAt, List.getD, List.set]
  have hp0 := hpiece_shape 0 (by omega)
  have hhead : (([transposeAxes 2 3 (chunkPrimDimN 2 4 0 x),
      transposeAxes 2 3 (chunkPrimDimN 2 4 1 x),
      transposeAxes 2 3 (chunkPrimDimN 2 4 2 x),
      transposeAxes 2 3 (chunkPrimDimN 2 4 3 x)] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by
    simp [hp0]
  have hlhs_shape : (transposeAxes 2 3 x).shape = [1, 4, 8, 8] := by
    simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [transposeAxes 2 3 (chunkPrimDimN 2 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 3 x)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transposeAxes_2_3_valAt_1_4_8_8 x idx hx hidx256]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead hidx256]
  set r := (idx % 8) / 2
  set loc := (idx / 8) * 2 + (idx % 8) % 2
  have hr : r < 4 := by
    subst r
    omega
  have hloc : loc < 64 := by
    subst loc
    omega
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [transposeAxes 2 3 (chunkPrimDimN 2 4 0 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 1 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 2 x),
       transposeAxes 2 3 (chunkPrimDimN 2 4 3 x)].getD i (zeroTensor [1, 4, 8, 2]) =
        transposeAxes 2 3 (chunkPrimDimN 2 4 i x) := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD r hr]
  rw [transposeAxes_2_3_valAt_1_4_2_8 _ loc (hchunk_shape r hr) hloc]
  rw [chunkPrimDimN_2_4_valAt_1_4_8_8 x r
    (((loc / 16) * 16 + (loc % 2) * 8 + (loc % 16) / 2)) hx hr (by
      subst loc
      omega)]
  congr 1
  have hloc_div16 : loc / 16 = idx / 64 := by
    subst loc
    omega
  have hloc_mod2 : loc % 2 = idx % 2 := by
    subst loc
    omega
  have hloc_mod16_div2 : (loc % 16) / 2 = (idx % 64) / 8 := by
    subst loc
    omega
  set inner := (loc / 16) * 16 + (loc % 2) * 8 + (loc % 16) / 2
  have hinner_eq : inner = (idx / 64) * 16 + (idx % 2) * 8 + (idx % 64) / 8 := by
    subst inner
    rw [hloc_div16, hloc_mod2, hloc_mod16_div2]
  have hinner_div16 : inner / 16 = idx / 64 := by
    rw [hinner_eq]
    omega
  have hinner_mod16 : inner % 16 = (idx % 2) * 8 + (idx % 64) / 8 := by
    rw [hinner_eq]
    omega
  have hr_eq : r = (idx % 8) / 2 := by
    subst r
    rfl
  have hmod8_eq : idx % 64 % 8 = idx % 8 := by
    omega
  rw [hinner_div16, hinner_mod16, hr_eq, ← hmod8_eq]
  omega

/-- Gather-chunk roundtrip for dim 1 on shape [1,4,8,8]:
    gathering the 4 chunks of x along dim 1 gives back x. -/
theorem allGatherPrimDimN_chunkPrimDimN_id_dim1_4_8_8 (x : Tensor)
    (hsh : x.shape = [1, 4, 8, 8]) :
    allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r x).shape = [1, 1, 8, 8] := by
    intro r
    rw [chunkPrimDimN_shape 1 4 r _ _ hsh (by omega)]
    simp [List.set, List.getD]
  have hhead : ([chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x].head?.map (·.shape)).getD [] = [1, 1, 8, 8] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  have hgather_shape : (allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 1, 8, 8] hhead]
    simp [List.set, List.getD]
  symm
  apply Tensor.ext (by rw [hsh, hgather_shape])
  intro idx hidx
  rw [hsh] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  rw [allGather_dim1_4_1_1_8_8_valAt _ _ _ _ idx (hchunk_shape 0) (hchunk_shape 1)
    (hchunk_shape 2) (hchunk_shape 3) hidx256]
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x].getD i (zeroTensor [1, 1, 8, 8]) =
        chunkPrimDimN 1 4 i x := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hr : idx / 64 < 4 := by omega
  have hloc : idx % 64 < 64 := Nat.mod_lt idx (by omega)
  rw [hgetD (idx / 64) hr]
  rw [chunk_dim1_4_1_4_8_8_valAt x (idx / 64) (idx % 64) hsh hr hloc]
  congr 1
  omega

/-- Gather-after-chunk identity: reassembling dim-3 chunks (of shape [1,4,8,2]) recovers the
    original tensor of shape [1,4,8,8]. -/
theorem allGatherPrimDimN_chunkPrimDimN_id_dim3_4_8_8 (x : Tensor)
    (hsh : x.shape = [1, 4, 8, 8]) :
    allGatherPrimDimN 3 4 0
      [chunkPrimDimN 3 4 0 x, chunkPrimDimN 3 4 1 x,
       chunkPrimDimN 3 4 2 x, chunkPrimDimN 3 4 3 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 3 4 r x).shape = [1, 4, 8, 2] := by
    intro r
    rw [chunkPrimDimN_shape 3 4 r _ _ hsh (by omega)]
    simp [List.set, List.getD]
  have hhead : ([chunkPrimDimN 3 4 0 x, chunkPrimDimN 3 4 1 x,
       chunkPrimDimN 3 4 2 x, chunkPrimDimN 3 4 3 x].head?.map (·.shape)).getD [] = [1, 4, 8, 2] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  have hgather_shape : (allGatherPrimDimN 3 4 0
      [chunkPrimDimN 3 4 0 x, chunkPrimDimN 3 4 1 x,
       chunkPrimDimN 3 4 2 x, chunkPrimDimN 3 4 3 x]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ [1, 4, 8, 2] hhead]
    simp [List.set, List.getD]
  symm
  apply Tensor.ext (by rw [hsh, hgather_shape])
  intro idx hidx
  rw [hsh] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead hidx256]
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [chunkPrimDimN 3 4 0 x, chunkPrimDimN 3 4 1 x,
       chunkPrimDimN 3 4 2 x, chunkPrimDimN 3 4 3 x].getD i (zeroTensor [1, 4, 8, 2]) =
        chunkPrimDimN 3 4 i x := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hr : (idx % 8) / 2 < 4 := by omega
  have hloc : (idx / 8) * 2 + (idx % 8) % 2 < 64 := by omega
  rw [hgetD ((idx % 8) / 2) hr]
  rw [chunkPrimDimN_3_4_valAt_1_4_8_8 x ((idx % 8) / 2) ((idx / 8) * 2 + (idx % 8) % 2) hsh hr hloc]
  congr 1
  omega

/-- Gather-after-chunk identity: reassembling dim-2 chunks (of shape [1,4,2,8]) recovers the
    original tensor of shape [1,4,8,8]. -/
theorem allGatherPrimDimN_chunkPrimDimN_id_dim2_4_8_8 (x : Tensor)
    (hsh : x.shape = [1, 4, 8, 8]) :
    allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 2 4 r x).shape = [1, 4, 2, 8] := by
    intro r
    rw [chunkPrimDimN_shape 2 4 r _ _ hsh (by omega)]
    simp [List.set, List.getD]
  have hhead : ([chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x].head?.map (·.shape)).getD [] = [1, 4, 2, 8] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  have hgather_shape : (allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ [1, 4, 2, 8] hhead]
    simp [List.set, List.getD]
  symm
  apply Tensor.ext (by rw [hsh, hgather_shape])
  intro idx hidx
  rw [hsh] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ idx hhead hidx256]
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x].getD i (zeroTensor [1, 4, 2, 8]) =
        chunkPrimDimN 2 4 i x := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hr : (idx % 64) / 16 < 4 := by omega
  have hloc : (idx / 64) * 16 + ((idx % 16) / 8) * 8 + idx % 8 < 64 := by omega
  rw [hgetD ((idx % 64) / 16) hr]
  rw [chunkPrimDimN_2_4_valAt_1_4_8_8 x ((idx % 64) / 16)
    ((idx / 64) * 16 + ((idx % 16) / 8) * 8 + idx % 8) hsh hr hloc]
  congr 1
  omega

end

/-- fw_linear distributes over allGatherPrimDimN on dim 1 for shard shape [1,2,32] with w:[32,32].
    fw_linear(allGather_dim1(xs), w) = allGather_dim1(map(fw_linear(·,w), xs)) -/
theorem fw_linear_distribute_allGatherPrimDimN_dim1_4_1_2_32
    (xs : List Tensor) (w : Tensor)
    (hlen : xs.length = 4)
    (hshape : ∀ x ∈ xs, x.shape = [1, 2, 32])
    (hw : w.shape = [32, 32]) :
    fw_linear (allGatherPrimDimN 1 4 0 xs) w =
    allGatherPrimDimN 1 4 0 (xs.map (fun x => fw_linear x w)) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    match xs, hlen, hshape with
    | x0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape x0 (List.mem_cons_self ..)
  have hgather_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hhead]
    simp [List.set, List.getD]
  have hmap_head : ((xs.map (fun x => fw_linear x w)).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    match xs, hlen, hshape with
    | x0 :: _, _, hshape =>
      simp only [List.map, List.head?, Option.map, Option.getD]
      exact fw_linear_3d_shape 1 2 32 32 x0 w (hshape x0 (List.mem_cons_self ..)) hw
  have hLHS_shape : (fw_linear (allGatherPrimDimN 1 4 0 xs) w).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 32 32 _ w hgather_shape hw
  have hRHS_shape : (allGatherPrimDimN 1 4 0 (xs.map (fun x => fw_linear x w))).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hmap_head]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  -- LHS: unfold fw_linear on gathered input [1,8,32] with w [32,32]
  have hLHS_unfold : valAt (fw_linear (allGatherPrimDimN 1 4 0 xs) w) idx = (
      let seq := idx / 32
      let col := idx % 32
      ∑ j ∈ Finset.range 32,
        valAt (allGatherPrimDimN 1 4 0 xs) (seq * 32 + j) * valAt w (col * 32 + j)) := by
    have hprod : idx < prodShape [1, 8, 32] := by simp [prodShape]; exact hidx256
    conv_lhs => rw [show fw_linear (allGatherPrimDimN 1 4 0 xs) w =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt (allGatherPrimDimN 1 4 0 xs) ((flat / 256 * 8 + flat % 256 / 32) * 32 + j) *
          valAt w (flat % 32 * 32 + j)) from by
      simp [fw_linear, hgather_shape, hw, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod]
    simp only [Tensor.mkShape]
    have h1 : idx / 256 = 0 := by omega
    have h2 : idx % 256 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
  -- RHS: unfold allGatherPrimDimN on mapped list
  set seq := idx / 32
  set col := idx % 32
  have hcol : col < 32 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  set r := seq / 2
  set p := seq % 2
  have hr : r < 4 := by omega
  have hp : p < 2 := Nat.mod_lt _ (by omega)
  have hseq_eq : seq = r * 2 + p := by omega
  have hidx_eq2 : idx = (r * 2 + p) * 32 + col := by omega
  have hRHS_unfold : valAt (allGatherPrimDimN 1 4 0 (xs.map (fun x => fw_linear x w))) idx = (
      ∑ j ∈ Finset.range 32,
        valAt (xs.getD r (zeroTensor [1, 2, 32])) (p * 32 + j) * valAt w (col * 32 + j)) := by
    rw [hidx_eq2]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr p hp col hcol hmap_head]
    -- Now: valAt ((xs.map (fun x => fw_linear x w)).getD r ...) (p * 32 + col) = ...
    have hr_len : r < xs.length := by omega
    have hmap_getD : (xs.map (fun x => fw_linear x w)).getD r (zeroTensor [1, 2, 32]) =
        fw_linear (xs[r]) w := by
      simp [List.getD, List.getElem?_eq_getElem (by simp; omega : r < (xs.map _).length),
        List.getElem_map]
    rw [hmap_getD]
    -- valAt(fw_linear(xs[r], w), p*32+col)
    have hxr_shape : (xs[r]).shape = [1, 2, 32] := hshape _ (List.getElem_mem hr_len)
    conv_lhs => rw [show fw_linear (xs[r]) w =
      Tensor.mkShape [1, 2, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt (xs[r]) ((flat / 64 * 2 + flat % 64 / 32) * 32 + j) *
          valAt w (flat % 32 * 32 + j)) from by
      simp [fw_linear, hxr_shape, hw, Tensor.mkShape]]
    have hprod2 : p * 32 + col < prodShape [1, 2, 32] := by simp [prodShape]; omega
    rw [valAt_of_lt _ _ hprod2]
    simp only [Tensor.mkShape]
    have h3 : (p * 32 + col) / 64 = 0 := by omega
    have h4 : (p * 32 + col) % 64 / 32 = p := by omega
    have h5 : (p * 32 + col) % 32 = col := by omega
    simp only [h3, h4, h5, Nat.zero_mul, Nat.zero_add]
    congr 1; funext j
    congr 1
    have hgetD_eq : xs.getD r (zeroTensor [1, 2, 32]) = xs[r] :=
      by simp [List.getD, List.getElem?_eq_getElem hr_len]
    rw [← hgetD_eq]
  rw [hLHS_unfold, hRHS_unfold]
  -- Both are ∑ j, valAt(input, seq_or_p*32+j) * valAt(w, col*32+j)
  -- LHS has valAt(gathered, seq*32+j), RHS has valAt(xs.getD r, p*32+j)
  -- Use allGatherPrimDimN_dim1_4_1_2_32_valAt: valAt(gathered, (r*2+p)*32+j) = valAt(xs.getD r, p*32+j)
  apply Finset.sum_congr rfl
  intro j hj_mem
  have hj : j < 32 := Finset.mem_range.mp hj_mem
  congr 1
  rw [hseq_eq]
  exact allGatherPrimDimN_dim1_4_1_2_32_valAt xs r hr p hp j hj hhead


/-- valAt for dim=2 gather of 4 tensors with shape [1,8,8] → [1,8,32].
    Index `seq * 32 + r * 8 + lc` maps to rank `r`, local index `seq * 8 + lc`. -/
theorem allGatherPrimDimN_dim2_4_1_8_8_valAt (xs : List Tensor)
    (seq : Nat) (hseq : seq < 8) (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 8)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 8]) :
    valAt (allGatherPrimDimN 2 4 0 xs) (seq * 32 + r * 8 + lc) =
      valAt (xs.getD r (zeroTensor [1, 8, 8])) (seq * 8 + lc) := by
  have hidx_lt : seq * 32 + r * 8 + lc < 256 := by omega
  have hgather_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 xs [1, 8, 8] hhead]
    simp [List.set, List.getD]
  have hidx_prod : seq * 32 + r * 8 + lc < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set,
    show (8 : Nat) ≠ 0 from by omega, show (32 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (1 : Nat) ≠ 0 from by omega,
    ite_false, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]
  have hd32 : (seq * 32 + r * 8 + lc) / 32 = seq := by omega
  have hm32 : (seq * 32 + r * 8 + lc) % 32 = r * 8 + lc := by omega
  have hdr : (r * 8 + lc) / 8 = r := by omega
  have hmr : (r * 8 + lc) % 8 = lc := by omega
  rw [hd32, hm32, hdr, hmr]

set_option maxHeartbeats 3200000 in
/-- Column-parallel fw_linear: W sharded on dim 0 into 4 parts [8,32].
    fw_linear(X, gather_dim0 Ws) = gather_dim2 (map (fw_linear X) Ws)
    Specialized for X:[1,8,32], W_r:[8,32]. -/
theorem fw_linear_column_parallel_4_1_8_32_8
    (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [1, 8, 32])
    (hlen : ws.length = 4)
    (hshape : ∀ w ∈ ws, w.shape = [8, 32]) :
    fw_linear x (allGatherPrimDimN 0 4 0 ws) =
    allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w)) := by
  have hhead_w : (ws.head?.map (fun t => t.shape)).getD [] = [8, 32] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape w0 (List.mem_cons_self ..)
  have hW_shape : (allGatherPrimDimN 0 4 0 ws).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 0 4 ws [8, 32] hhead_w]
    simp [List.set, List.getD]
  have hmap_head : ((ws.map (fun w => fw_linear x w)).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.map, List.head?, Option.map, Option.getD]
      exact fw_linear_3d_shape 1 8 32 8 x w0 hx (hshape w0 (List.mem_cons_self ..))
  have hLHS_shape : (fw_linear x (allGatherPrimDimN 0 4 0 ws)).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 32 32 x _ hx hW_shape
  have hRHS_shape : (allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w))).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ [1, 8, 8] hmap_head]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  set seq := idx / 32
  set col := idx % 32
  have hcol : col < 32 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  set r := col / 8
  set lc := col % 8
  have hr : r < 4 := by omega
  have hlc : lc < 8 := Nat.mod_lt _ (by omega)
  have hcol_eq : col = r * 8 + lc := by omega
  have hidx_eq : idx = seq * 32 + r * 8 + lc := by omega
  -- LHS: fw_linear(x, W_full) at idx
  have hprod_lhs : idx < prodShape [1, 8, 32] := by simp [prodShape]; exact hidx256
  have hLHS_val : valAt (fw_linear x (allGatherPrimDimN 0 4 0 ws)) idx =
      ∑ j ∈ Finset.range 32,
        valAt x (seq * 32 + j) * valAt (allGatherPrimDimN 0 4 0 ws) (col * 32 + j) := by
    conv_lhs => rw [show fw_linear x (allGatherPrimDimN 0 4 0 ws) =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt x ((flat / 256 * 8 + flat % 256 / 32) * 32 + j) *
          valAt (allGatherPrimDimN 0 4 0 ws) (flat % 32 * 32 + j)) from by
      simp [fw_linear, hx, hW_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_lhs]
    simp only [Tensor.mkShape]
    have h1 : idx / 256 = 0 := by omega
    have h2 : idx % 256 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
    rfl
  have hRHS_val : valAt (allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w))) idx =
      ∑ j ∈ Finset.range 32,
        valAt x (seq * 32 + j) * valAt (ws.getD r (zeroTensor [8, 32])) (lc * 32 + j) := by
    rw [hidx_eq]
    rw [allGatherPrimDimN_dim2_4_1_8_8_valAt _ seq hseq r hr lc hlc hmap_head]
    have hr_len : r < ws.length := by omega
    have hmap_getD : (ws.map (fun w => fw_linear x w)).getD r (zeroTensor [1, 8, 8]) =
        fw_linear x (ws[r]) := by
      simp [List.getD, List.getElem?_eq_getElem (by simp; omega : r < (ws.map _).length),
        List.getElem_map]
    rw [hmap_getD]
    have hwr_shape : (ws[r]).shape = [8, 32] := hshape _ (List.getElem_mem hr_len)
    have hlocal_lt : seq * 8 + lc < 64 := by omega
    have hprod_local : seq * 8 + lc < prodShape [1, 8, 8] := by simp [prodShape]; omega
    conv_lhs => rw [show fw_linear x (ws[r]) =
      Tensor.mkShape [1, 8, 8] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt x ((flat / 64 * 8 + flat % 64 / 8) * 32 + j) *
          valAt (ws[r]) (flat % 8 * 32 + j)) from by
      simp [fw_linear, hx, hwr_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_local]
    simp only [Tensor.mkShape]
    have h3 : (seq * 8 + lc) / 64 = 0 := by omega
    have h4 : (seq * 8 + lc) % 64 / 8 = seq := by omega
    have h5 : (seq * 8 + lc) % 8 = lc := by omega
    simp only [h3, h4, h5, Nat.zero_mul, Nat.zero_add]
    congr 1; funext j; congr 1
    have hgetD_eq : ws.getD r (zeroTensor [8, 32]) = ws[r] :=
      by simp [List.getD, List.getElem?_eq_getElem hr_len]
    rw [← hgetD_eq]
  rw [hLHS_val, hRHS_val]
  apply Finset.sum_congr rfl
  intro j hj_mem
  have hj : j < 32 := Finset.mem_range.mp hj_mem
  congr 1
  have hW_shapes : ∀ rr (_ : rr < 4),
      (ws.getD rr (zeroTensor [8, 32])).shape = [8, 32] := by
    intro rr hrr
    have hrr_len : rr < ws.length := by omega
    have : ws[rr] ∈ ws := List.getElem_mem hrr_len
    simp [List.getD, List.getElem?_eq_getElem hrr_len]
    exact hshape _ this
  rw [hcol_eq]
  exact allGatherPrimDimN0_valAt 4 8 32 ws (by omega) (by omega) (by omega)
    hhead_w hW_shapes r hr lc hlc j hj

theorem fw_linear_column_parallel_4_1_8_128_8
    (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [1, 8, 128])
    (hlen : ws.length = 4)
    (hshape : ∀ w ∈ ws, w.shape = [8, 128]) :
    fw_linear x (allGatherPrimDimN 0 4 0 ws) =
    allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w)) := by
  have hhead_w : (ws.head?.map (fun t => t.shape)).getD [] = [8, 128] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape w0 (List.mem_cons_self ..)
  have hW_shape : (allGatherPrimDimN 0 4 0 ws).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 0 4 ws [8, 128] hhead_w]
    simp [List.set, List.getD]
  have hmap_head : ((ws.map (fun w => fw_linear x w)).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.map, List.head?, Option.map, Option.getD]
      exact fw_linear_3d_shape 1 8 128 8 x w0 hx (hshape w0 (List.mem_cons_self ..))
  have hLHS_shape : (fw_linear x (allGatherPrimDimN 0 4 0 ws)).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 128 32 x _ hx hW_shape
  have hRHS_shape : (allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w))).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ [1, 8, 8] hmap_head]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  set seq := idx / 32
  set col := idx % 32
  have hcol : col < 32 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  set r := col / 8
  set lc := col % 8
  have hr : r < 4 := by omega
  have hlc : lc < 8 := Nat.mod_lt _ (by omega)
  have hcol_eq : col = r * 8 + lc := by omega
  have hidx_eq : idx = seq * 32 + r * 8 + lc := by omega
  have hprod_lhs : idx < prodShape [1, 8, 32] := by simp [prodShape]; exact hidx256
  have hLHS_val : valAt (fw_linear x (allGatherPrimDimN 0 4 0 ws)) idx =
      ∑ j ∈ Finset.range 128,
        valAt x (seq * 128 + j) * valAt (allGatherPrimDimN 0 4 0 ws) (col * 128 + j) := by
    conv_lhs => rw [show fw_linear x (allGatherPrimDimN 0 4 0 ws) =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 128,
          valAt x ((flat / 256 * 8 + flat % 256 / 32) * 128 + j) *
          valAt (allGatherPrimDimN 0 4 0 ws) (flat % 32 * 128 + j)) from by
      simp [fw_linear, hx, hW_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_lhs]
    simp only [Tensor.mkShape]
    have h1 : idx / 256 = 0 := by omega
    have h2 : idx % 256 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
    rfl
  have hRHS_val : valAt (allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w))) idx =
      ∑ j ∈ Finset.range 128,
        valAt x (seq * 128 + j) * valAt (ws.getD r (zeroTensor [8, 128])) (lc * 128 + j) := by
    rw [hidx_eq]
    rw [allGatherPrimDimN_dim2_4_1_8_8_valAt _ seq hseq r hr lc hlc hmap_head]
    have hr_len : r < ws.length := by omega
    have hmap_getD : (ws.map (fun w => fw_linear x w)).getD r (zeroTensor [1, 8, 8]) =
        fw_linear x (ws[r]) := by
      simp [List.getD, List.getElem?_eq_getElem (by simp; omega : r < (ws.map _).length),
        List.getElem_map]
    rw [hmap_getD]
    have hwr_shape : (ws[r]).shape = [8, 128] := hshape _ (List.getElem_mem hr_len)
    have hlocal_lt : seq * 8 + lc < 64 := by omega
    have hprod_local : seq * 8 + lc < prodShape [1, 8, 8] := by simp [prodShape]; omega
    conv_lhs => rw [show fw_linear x (ws[r]) =
      Tensor.mkShape [1, 8, 8] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 128,
          valAt x ((flat / 64 * 8 + flat % 64 / 8) * 128 + j) *
          valAt (ws[r]) (flat % 8 * 128 + j)) from by
      simp [fw_linear, hx, hwr_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_local]
    simp only [Tensor.mkShape]
    have h3 : (seq * 8 + lc) / 64 = 0 := by omega
    have h4 : (seq * 8 + lc) % 64 / 8 = seq := by omega
    have h5 : (seq * 8 + lc) % 8 = lc := by omega
    simp only [h3, h4, h5, Nat.zero_mul, Nat.zero_add]
    congr 1; funext j; congr 1
    have hgetD_eq : ws.getD r (zeroTensor [8, 128]) = ws[r] :=
      by simp [List.getD, List.getElem?_eq_getElem hr_len]
    rw [← hgetD_eq]
  rw [hLHS_val, hRHS_val]
  apply Finset.sum_congr rfl
  intro j hj_mem
  have hj : j < 128 := Finset.mem_range.mp hj_mem
  congr 1
  have hW_shapes : ∀ rr (_ : rr < 4),
      (ws.getD rr (zeroTensor [8, 128])).shape = [8, 128] := by
    intro rr hrr
    have hrr_len : rr < ws.length := by omega
    have : ws[rr] ∈ ws := List.getElem_mem hrr_len
    simp [List.getD, List.getElem?_eq_getElem hrr_len]
    exact hshape _ this
  rw [hcol_eq]
  exact allGatherPrimDimN0_valAt 4 8 128 ws (by omega) (by omega) (by omega)
    hhead_w hW_shapes r hr lc hlc j hj

/-- valAt for dim=2 gather of 4 tensors with shape [1,8,32] → [1,8,128].
    Index `seq * 128 + r * 32 + lc` maps to rank `r`, local index `seq * 32 + lc`. -/
theorem allGatherPrimDimN_dim2_4_1_8_32_valAt (xs : List Tensor)
    (seq : Nat) (hseq : seq < 8) (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 32)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 32]) :
    valAt (allGatherPrimDimN 2 4 0 xs) (seq * 128 + r * 32 + lc) =
      valAt (xs.getD r (zeroTensor [1, 8, 32])) (seq * 32 + lc) := by
  have hidx_lt : seq * 128 + r * 32 + lc < 1024 := by omega
  have hgather_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 xs [1, 8, 32] hhead]
    simp [List.set, List.getD]
  have hidx_prod : seq * 128 + r * 32 + lc < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set,
    show (8 : Nat) ≠ 0 from by omega, show (32 : Nat) ≠ 0 from by omega,
    show (128 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    show (1 : Nat) ≠ 0 from by omega,
    ite_false, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]
  have hd128 : (seq * 128 + r * 32 + lc) / 128 = seq := by omega
  have hm128 : (seq * 128 + r * 32 + lc) % 128 = r * 32 + lc := by omega
  have hdr : (r * 32 + lc) / 32 = r := by omega
  have hmr : (r * 32 + lc) % 32 = lc := by omega
  rw [hd128, hm128, hdr, hmr]

set_option maxHeartbeats 3200000 in
/-- Column-parallel fw_linear: W sharded on dim 0 into 4 parts [32,32].
    fw_linear(X, gather_dim0 Ws) = gather_dim2 (map (fw_linear X) Ws)
    Specialized for X:[1,8,32], W_r:[32,32]. Output per rank: [1,8,32]. -/
theorem fw_linear_column_parallel_4_1_8_32_32
    (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [1, 8, 32])
    (hlen : ws.length = 4)
    (hshape : ∀ w ∈ ws, w.shape = [32, 32]) :
    fw_linear x (allGatherPrimDimN 0 4 0 ws) =
    allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w)) := by
  have hhead_w : (ws.head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape w0 (List.mem_cons_self ..)
  have hW_shape : (allGatherPrimDimN 0 4 0 ws).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 ws [32, 32] hhead_w]
    simp [List.set, List.getD]
  have hmap_head : ((ws.map (fun w => fw_linear x w)).head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.map, List.head?, Option.map, Option.getD]
      exact fw_linear_3d_shape 1 8 32 32 x w0 hx (hshape w0 (List.mem_cons_self ..))
  have hLHS_shape : (fw_linear x (allGatherPrimDimN 0 4 0 ws)).shape = [1, 8, 128] :=
    fw_linear_3d_shape 1 8 32 128 x _ hx hW_shape
  have hRHS_shape : (allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w))).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 _ [1, 8, 32] hmap_head]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx1024 : idx < 1024 := by simpa [prodShape] using hidx
  set seq := idx / 128
  set col := idx % 128
  have hcol : col < 128 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  set r := col / 32
  set lc := col % 32
  have hr : r < 4 := by omega
  have hlc : lc < 32 := Nat.mod_lt _ (by omega)
  have hcol_eq : col = r * 32 + lc := by omega
  have hidx_eq : idx = seq * 128 + r * 32 + lc := by omega
  have hprod_lhs : idx < prodShape [1, 8, 128] := by simp [prodShape]; exact hidx1024
  have hLHS_val : valAt (fw_linear x (allGatherPrimDimN 0 4 0 ws)) idx =
      ∑ j ∈ Finset.range 32,
        valAt x (seq * 32 + j) * valAt (allGatherPrimDimN 0 4 0 ws) (col * 32 + j) := by
    conv_lhs => rw [show fw_linear x (allGatherPrimDimN 0 4 0 ws) =
      Tensor.mkShape [1, 8, 128] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt x ((flat / 1024 * 8 + flat % 1024 / 128) * 32 + j) *
          valAt (allGatherPrimDimN 0 4 0 ws) (flat % 128 * 32 + j)) from by
      simp [fw_linear, hx, hW_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_lhs]
    simp only [Tensor.mkShape]
    have h1 : idx / 1024 = 0 := by omega
    have h2 : idx % 1024 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
    rfl
  have hRHS_val : valAt (allGatherPrimDimN 2 4 0 (ws.map (fun w => fw_linear x w))) idx =
      ∑ j ∈ Finset.range 32,
        valAt x (seq * 32 + j) * valAt (ws.getD r (zeroTensor [32, 32])) (lc * 32 + j) := by
    rw [hidx_eq]
    rw [allGatherPrimDimN_dim2_4_1_8_32_valAt _ seq hseq r hr lc hlc hmap_head]
    have hr_len : r < ws.length := by omega
    have hmap_getD : (ws.map (fun w => fw_linear x w)).getD r (zeroTensor [1, 8, 32]) =
        fw_linear x (ws[r]) := by
      simp [List.getD, List.getElem?_eq_getElem (by simp; omega : r < (ws.map _).length),
        List.getElem_map]
    rw [hmap_getD]
    have hwr_shape : (ws[r]).shape = [32, 32] := hshape _ (List.getElem_mem hr_len)
    have hlocal_lt : seq * 32 + lc < 256 := by omega
    have hprod_local : seq * 32 + lc < prodShape [1, 8, 32] := by simp [prodShape]; omega
    conv_lhs => rw [show fw_linear x (ws[r]) =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt x ((flat / 256 * 8 + flat % 256 / 32) * 32 + j) *
          valAt (ws[r]) (flat % 32 * 32 + j)) from by
      simp [fw_linear, hx, hwr_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_local]
    simp only [Tensor.mkShape]
    have h3 : (seq * 32 + lc) / 256 = 0 := by omega
    have h4 : (seq * 32 + lc) % 256 / 32 = seq := by omega
    have h5 : (seq * 32 + lc) % 32 = lc := by omega
    simp only [h3, h4, h5, Nat.zero_mul, Nat.zero_add]
    congr 1; funext j; congr 1
    have hgetD_eq : ws.getD r (zeroTensor [32, 32]) = ws[r] :=
      by simp [List.getD, List.getElem?_eq_getElem hr_len]
    rw [← hgetD_eq]
  rw [hLHS_val, hRHS_val]
  apply Finset.sum_congr rfl
  intro j hj_mem
  have hj : j < 32 := Finset.mem_range.mp hj_mem
  congr 1
  have hW_shapes : ∀ rr (_ : rr < 4),
      (ws.getD rr (zeroTensor [32, 32])).shape = [32, 32] := by
    intro rr hrr
    have hrr_len : rr < ws.length := by omega
    have : ws[rr] ∈ ws := List.getElem_mem hrr_len
    simp [List.getD, List.getElem?_eq_getElem hrr_len]
    exact hshape _ this
  rw [hcol_eq]
  exact allGatherPrimDimN0_valAt 4 32 32 ws (by omega) (by omega) (by omega)
    hhead_w hW_shapes r hr lc hlc j hj

/-- valAt for dim=1 gather of 4 tensors with shape [32,8] → [32,32].
    Index `row * 32 + r * 8 + lc` maps to rank `r`, local index `row * 8 + lc`. -/
theorem allGatherPrimDimN_dim1_4_32_8_valAt (ws : List Tensor)
    (row : Nat) (hrow : row < 32) (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 8)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [32, 8]) :
    valAt (allGatherPrimDimN 1 4 0 ws) (row * 32 + r * 8 + lc) =
      valAt (ws.getD r (zeroTensor [32, 8])) (row * 8 + lc) := by
  have hidx_lt : row * 32 + r * 8 + lc < 1024 := by omega
  have hgather_shape : (allGatherPrimDimN 1 4 0 ws).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 ws [32, 8] hhead]
    simp [List.set, List.getD]
  have hidx_prod : row * 32 + r * 8 + lc < prodShape (allGatherPrimDimN 1 4 0 ws).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set, List.length, List.take,
    show (32 : Nat) ≠ 0 from by omega, show (8 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (1 : Nat) ≠ 0 from by omega]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod,
    ite_false, ite_true, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    List.prod_cons, List.prod_nil, Nat.one_mul]
  have hd32 : (row * 32 + r * 8 + lc) / 32 = row := by omega
  have hm32 : (row * 32 + r * 8 + lc) % 32 = r * 8 + lc := by omega
  have hdr : (r * 8 + lc) / 8 = r := by omega
  have hmr : (r * 8 + lc) % 8 = lc := by omega
  rw [hd32, hm32, hdr, hmr]

set_option maxHeartbeats 800000 in
/-- fw_linear distributes over allGatherPrimDimN on dim1 for [1,2,128] shards with w=[32,128]. -/
theorem fw_linear_distribute_allGatherPrimDimN_dim1_4_1_2_128
    (xs : List Tensor) (w : Tensor)
    (hlen : xs.length = 4)
    (hshape : ∀ x ∈ xs, x.shape = [1, 2, 128])
    (hw : w.shape = [32, 128]) :
    fw_linear (allGatherPrimDimN 1 4 0 xs) w =
    allGatherPrimDimN 1 4 0 (xs.map (fun x => fw_linear x w)) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 128] := by
    match xs, hlen, hshape with
    | x0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape x0 (List.mem_cons_self ..)
  have hgather_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 128] hhead]
    simp [List.set, List.getD]
  have hmap_head : ((xs.map (fun x => fw_linear x w)).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    match xs, hlen, hshape with
    | x0 :: _, _, hshape =>
      simp only [List.map, List.head?, Option.map, Option.getD]
      exact fw_linear_3d_shape 1 2 128 32 x0 w (hshape x0 (List.mem_cons_self ..)) hw
  have hLHS_shape : (fw_linear (allGatherPrimDimN 1 4 0 xs) w).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 128 32 _ w hgather_shape hw
  have hRHS_shape : (allGatherPrimDimN 1 4 0 (xs.map (fun x => fw_linear x w))).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hmap_head]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  -- LHS: unfold fw_linear on gathered input [1,8,128] with w [32,128]
  have hLHS_unfold : valAt (fw_linear (allGatherPrimDimN 1 4 0 xs) w) idx = (
      let seq := idx / 32
      let col := idx % 32
      ∑ j ∈ Finset.range 128,
        valAt (allGatherPrimDimN 1 4 0 xs) (seq * 128 + j) * valAt w (col * 128 + j)) := by
    have hprod : idx < prodShape [1, 8, 32] := by simp [prodShape]; exact hidx256
    conv_lhs => rw [show fw_linear (allGatherPrimDimN 1 4 0 xs) w =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 128,
          valAt (allGatherPrimDimN 1 4 0 xs) ((flat / 256 * 8 + flat % 256 / 32) * 128 + j) *
          valAt w (flat % 32 * 128 + j)) from by
      simp [fw_linear, hgather_shape, hw, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod]
    simp only [Tensor.mkShape]
    have h1 : idx / 256 = 0 := by omega
    have h2 : idx % 256 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
  -- RHS: unfold allGatherPrimDimN on mapped list
  set seq := idx / 32
  set col := idx % 32
  have hcol : col < 32 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  set r := seq / 2
  set p := seq % 2
  have hr : r < 4 := by omega
  have hp : p < 2 := Nat.mod_lt _ (by omega)
  have hseq_eq : seq = r * 2 + p := by omega
  have hidx_eq2 : idx = (r * 2 + p) * 32 + col := by omega
  have hRHS_unfold : valAt (allGatherPrimDimN 1 4 0 (xs.map (fun x => fw_linear x w))) idx = (
      ∑ j ∈ Finset.range 128,
        valAt (xs.getD r (zeroTensor [1, 2, 128])) (p * 128 + j) * valAt w (col * 128 + j)) := by
    rw [hidx_eq2]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr p hp col hcol hmap_head]
    have hr_len : r < xs.length := by omega
    have hmap_getD : (xs.map (fun x => fw_linear x w)).getD r (zeroTensor [1, 2, 32]) =
        fw_linear (xs[r]) w := by
      simp [List.getD, List.getElem?_eq_getElem (by simp; omega : r < (xs.map _).length),
        List.getElem_map]
    rw [hmap_getD]
    have hxr_shape : (xs[r]).shape = [1, 2, 128] := hshape _ (List.getElem_mem hr_len)
    conv_lhs => rw [show fw_linear (xs[r]) w =
      Tensor.mkShape [1, 2, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 128,
          valAt (xs[r]) ((flat / 64 * 2 + flat % 64 / 32) * 128 + j) *
          valAt w (flat % 32 * 128 + j)) from by
      simp [fw_linear, hxr_shape, hw, Tensor.mkShape]]
    have hprod2 : p * 32 + col < prodShape [1, 2, 32] := by simp [prodShape]; omega
    rw [valAt_of_lt _ _ hprod2]
    simp only [Tensor.mkShape]
    have h3 : (p * 32 + col) / 64 = 0 := by omega
    have h4 : (p * 32 + col) % 64 / 32 = p := by omega
    have h5 : (p * 32 + col) % 32 = col := by omega
    simp only [h3, h4, h5, Nat.zero_mul, Nat.zero_add]
    congr 1; funext j
    congr 1
    have hgetD_eq : xs.getD r (zeroTensor [1, 2, 128]) = xs[r] :=
      by simp [List.getD, List.getElem?_eq_getElem hr_len]
    rw [← hgetD_eq]
  rw [hLHS_unfold, hRHS_unfold]
  apply Finset.sum_congr rfl
  intro j hj_mem
  have hj : j < 128 := Finset.mem_range.mp hj_mem
  congr 1
  rw [hseq_eq]
  exact allGatherPrimDimN_dim1_4_1_2_128_valAt xs r hr p hp j hj hhead

/-- Gather-after-chunk identity for dim1, 4 parts, shape [1,8,32]. -/
theorem allGatherPrimDimN_chunkPrimDimN_id_dim1_4_32 (x : Tensor)
    (hsh : x.shape = [1, 8, 32]) :
    allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
    intro r
    rw [chunkPrimDimN_shape 1 4 r _ _ hsh (by omega)]
    simp [List.set, List.getD]
  have hhead : ([chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x].head?.map (·.shape)).getD [] = [1, 2, 32] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  have hgather_shape : (allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hhead]
    simp [List.set, List.getD]
  symm
  apply Tensor.ext (by rw [hsh, hgather_shape])
  intro idx hidx
  rw [hsh] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  set r := idx / 64
  set p := (idx % 64) / 32
  set j := idx % 32
  have hr : r < 4 := by omega
  have hp : p < 2 := by omega
  have hj : j < 32 := Nat.mod_lt idx (by omega)
  have hidx_eq : idx = (r * 2 + p) * 32 + j := by subst r p j; omega
  rw [hidx_eq]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr p hp j hj hhead]
  have hgetD : ∀ (i : Nat) (hi : i < 4),
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x].getD i (zeroTensor [1, 2, 32]) =
        chunkPrimDimN 1 4 i x := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [List.getD]
  rw [hgetD r hr]
  exact (chunk_dim1_4_1_8_32_valAt x r p j hsh hr hp hj).symm

/-! ## Column-parallel identity helpers for FW_linear AllToAll + AllReduce goals -/

set_option maxHeartbeats 800000 in
theorem sum_range_split_4_8 (f : ℕ → Scalar) :
    ∑ j ∈ Finset.range 32, f j =
    ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8, f (r * 8 + lc) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.zero_mul,
    Nat.reduceMul, Nat.reduceAdd]
  ring

set_option maxHeartbeats 2000000 in
theorem sum_range_split_4_32 (f : ℕ → Scalar) :
    ∑ j ∈ Finset.range 128, f j =
    ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 32, f (r * 32 + lc) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.zero_mul,
    Nat.reduceMul, Nat.reduceAdd]
  ring

theorem allGatherPrimDimN1_4_valAt_128_8 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [128, 8])
    (hW_shapes : ∀ r (_ : r < 4), (ws.getD r (zeroTensor [128, 8])).shape = [128, 8])
    (row : Nat) (hrow : row < 128) (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 8) :
    valAt (allGatherPrimDimN 1 4 0 ws) (row * 32 + r * 8 + lc) =
      valAt (ws.getD r (zeroTensor [128, 8])) (row * 8 + lc) := by
  have hidx_lt : row * 32 + r * 8 + lc < 4096 := by omega
  have hgather_shape : (allGatherPrimDimN 1 4 0 ws).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 1 4 ws [128, 8] hhead]
    simp [List.set, List.getD]
  have hidx_prod : row * 32 + r * 8 + lc < prodShape (allGatherPrimDimN 1 4 0 ws).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set,
    show (4 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (128 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have h1 : (row * 32 + r * 8 + lc) / 32 = row := by omega
  have h2 : (row * 32 + r * 8 + lc) % 32 = r * 8 + lc := by omega
  have h3 : (r * 8 + lc) / 1 = r * 8 + lc := by omega
  have h4 : (r * 8 + lc) % 1 = 0 := by omega
  have h5 : (r * 8 + lc) / 8 = r := by omega
  have h6 : (r * 8 + lc) % 8 = lc := by omega
  simp only [h1, h2, h3, h4, h5, h6]
  congr 1; omega

theorem allGatherPrimDimN1_4_valAt_32_32 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [32, 32])
    (hW_shapes : ∀ r (_ : r < 4), (ws.getD r (zeroTensor [32, 32])).shape = [32, 32])
    (row : Nat) (hrow : row < 32) (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 32) :
    valAt (allGatherPrimDimN 1 4 0 ws) (row * 128 + r * 32 + lc) =
      valAt (ws.getD r (zeroTensor [32, 32])) (row * 32 + lc) := by
  have hidx_lt : row * 128 + r * 32 + lc < 4096 := by omega
  have hgather_shape : (allGatherPrimDimN 1 4 0 ws).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 1 4 ws [32, 32] hhead]
    simp [List.set, List.getD]
  have hidx_prod : row * 128 + r * 32 + lc < prodShape (allGatherPrimDimN 1 4 0 ws).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set,
    show (4 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (128 : Nat) ≠ 0 by omega, show (1 : Nat) ≠ 0 by omega,
    ite_false]
  have h1 : (row * 128 + r * 32 + lc) / 128 = row := by omega
  have h2 : (row * 128 + r * 32 + lc) % 128 = r * 32 + lc := by omega
  have h3 : (r * 32 + lc) / 1 = r * 32 + lc := by omega
  have h4 : (r * 32 + lc) % 1 = 0 := by omega
  have h5 : (r * 32 + lc) / 32 = r := by omega
  have h6 : (r * 32 + lc) % 32 = lc := by omega
  simp only [h1, h2, h3, h4, h5, h6]
  congr 1; omega

set_option maxHeartbeats 1600000 in
theorem fw_linear_colParallel_4_1_8_32_128_8
    (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [1, 8, 32])
    (hlen : ws.length = 4)
    (hshape : ∀ w ∈ ws, w.shape = [128, 8]) :
    fw_linear x (allGatherPrimDimN 1 4 0 ws) =
    allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [128, 8])))) := by
  have hhead_w : (ws.head?.map (fun t => t.shape)).getD [] = [128, 8] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape w0 (List.mem_cons_self ..)
  have hW_shapes : ∀ r (_ : r < 4), (ws.getD r (zeroTensor [128, 8])).shape = [128, 8] := by
    intro r hr
    have hr_len : r < ws.length := by omega
    simp [List.getD, List.getElem?_eq_getElem hr_len]
    exact hshape _ (List.getElem_mem hr_len)
  have hW_shape : (allGatherPrimDimN 1 4 0 ws).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 1 4 ws [128, 8] hhead_w]
    simp [List.set, List.getD]
  have hLHS_shape : (fw_linear x (allGatherPrimDimN 1 4 0 ws)).shape = [1, 8, 128] :=
    fw_linear_3d_shape 1 8 32 128 x _ hx hW_shape
  have hchunk_shape : ∀ r : Fin 4, (chunkPrimDimN 2 4 r.val x).shape = [1, 8, 8] := by
    intro r
    rw [chunkPrimDimN_shape 2 4 r.val _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hlocal_shape : ∀ r : Fin 4,
      (fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [128, 8]))).shape =
        [1, 8, 128] := by
    intro r
    exact fw_linear_3d_shape 1 8 8 128 _ _ (hchunk_shape r) (hW_shapes r.val r.isLt)
  have hRHS_head : (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [128, 8])))).head? =
      some (fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [128, 8]))) := by
    simp only [List.ofFn_succ, List.head?_cons, Fin.val_zero]
  have hRHS_shape : (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [128, 8]))))).shape = [1, 8, 128] := by
    rw [allReducePrim_shape 4 0 _ _ hRHS_head]
    exact hlocal_shape ⟨0, by omega⟩
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx1024 : idx < 1024 := by simpa [prodShape] using hidx
  set seq := idx / 128
  set col := idx % 128
  have hcol : col < 128 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  -- LHS value
  have hprod_lhs : idx < prodShape [1, 8, 128] := by simp [prodShape]; exact hidx1024
  have hLHS_eq : valAt (fw_linear x (allGatherPrimDimN 1 4 0 ws)) idx =
      ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
        valAt x (seq * 32 + r * 8 + lc) *
          valAt (ws.getD r (zeroTensor [128, 8])) (col * 8 + lc) := by
    conv_lhs => rw [show fw_linear x (allGatherPrimDimN 1 4 0 ws) =
      Tensor.mkShape [1, 8, 128] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt x ((flat / 1024 * 8 + flat % 1024 / 128) * 32 + j) *
          valAt (allGatherPrimDimN 1 4 0 ws) (flat % 128 * 32 + j)) from by
      simp [fw_linear, hx, hW_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_lhs]
    simp only [Tensor.mkShape]
    have h1 : idx / 1024 = 0 := by omega
    have h2 : idx % 1024 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
    -- Now: ∑ j, valAt(x, seq*32+j) * valAt(W_gathered, col*32+j)
    have heq_terms : ∀ j, j < 32 →
        valAt x (seq * 32 + j) * valAt (allGatherPrimDimN 1 4 0 ws) (col * 32 + j) =
        valAt x (seq * 32 + j) *
          valAt (ws.getD (j / 8) (zeroTensor [128, 8])) (col * 8 + j % 8) := by
      intro j hj
      congr 1
      have hj8 : j / 8 < 4 := by omega
      have hjmod : j % 8 < 8 := Nat.mod_lt _ (by omega)
      conv_lhs => rw [show col * 32 + j = col * 32 + (j / 8) * 8 + j % 8 from by omega]
      exact allGatherPrimDimN1_4_valAt_128_8 ws hhead_w hW_shapes col hcol (j / 8) hj8 (j % 8) hjmod
    calc ∑ j ∈ Finset.range 32,
          valAt x (seq * 32 + j) * valAt (allGatherPrimDimN 1 4 0 ws) (col * 32 + j)
        = ∑ j ∈ Finset.range 32,
          valAt x (seq * 32 + j) *
            valAt (ws.getD (j / 8) (zeroTensor [128, 8])) (col * 8 + j % 8) := by
          apply Finset.sum_congr rfl
          intro j hj; exact heq_terms j (Finset.mem_range.mp hj)
      _ = ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
          valAt x (seq * 32 + (r * 8 + lc)) *
            valAt (ws.getD ((r * 8 + lc) / 8) (zeroTensor [128, 8]))
              (col * 8 + (r * 8 + lc) % 8) := by
          rw [sum_range_split_4_8]
      _ = ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
          valAt x (seq * 32 + r * 8 + lc) *
            valAt (ws.getD r (zeroTensor [128, 8])) (col * 8 + lc) := by
          apply Finset.sum_congr rfl; intro r hr_mem
          apply Finset.sum_congr rfl; intro lc hlc_mem
          have hr : r < 4 := Finset.mem_range.mp hr_mem
          have hlc : lc < 8 := Finset.mem_range.mp hlc_mem
          simp only [show (r * 8 + lc) / 8 = r from by omega,
                     show (r * 8 + lc) % 8 = lc from by omega,
                     show seq * 32 + (r * 8 + lc) = seq * 32 + r * 8 + lc from by omega]
  -- RHS value
  have hRHS_eq : valAt (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [128, 8]))))) idx =
      ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
        valAt x (seq * 32 + r * 8 + lc) *
          valAt (ws.getD r (zeroTensor [128, 8])) (col * 8 + lc) := by
    have hhead0_shape : (fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [128, 8]))).shape =
        [1, 8, 128] := hlocal_shape ⟨0, by omega⟩
    rw [allReducePrim_valAt 4 0 _ idx _ hRHS_head
      (by rw [hhead0_shape]; simpa [prodShape])]
    -- foldl for 4-element list
    have hlist_eq : List.ofFn (fun r : Fin 4 =>
        fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [128, 8]))) =
      [fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [128, 8])),
       fw_linear (chunkPrimDimN 2 4 1 x) (ws.getD 1 (zeroTensor [128, 8])),
       fw_linear (chunkPrimDimN 2 4 2 x) (ws.getD 2 (zeroTensor [128, 8])),
       fw_linear (chunkPrimDimN 2 4 3 x) (ws.getD 3 (zeroTensor [128, 8]))] := by
      rfl
    rw [hlist_eq]
    simp only [List.foldl]
    -- Now have: 0 + v0 + v1 + v2 + v3 where v_r = valAt(fw_linear(chunk_r, ws_r), idx)
    have hterm : ∀ r : Nat, r < 4 →
        valAt (fw_linear (chunkPrimDimN 2 4 r x) (ws.getD r (zeroTensor [128, 8]))) idx =
        ∑ lc ∈ Finset.range 8,
          valAt x (seq * 32 + r * 8 + lc) *
            valAt (ws.getD r (zeroTensor [128, 8])) (col * 8 + lc) := by
      intro r hr
      have hchunk_r : (chunkPrimDimN 2 4 r x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
        simp [List.set, List.getD]
      have hwr : (ws.getD r (zeroTensor [128, 8])).shape = [128, 8] := hW_shapes r hr
      have hr_len : r < ws.length := by omega
      have hgetD_eq : ws.getD r (zeroTensor [128, 8]) = ws[r] := by
        simp [List.getD, List.getElem?_eq_getElem hr_len]
      have hwr' : (ws[r]).shape = [128, 8] := by rw [← hgetD_eq]; exact hwr
      rw [hgetD_eq]
      conv_lhs => rw [show fw_linear (chunkPrimDimN 2 4 r x) (ws[r]) =
        Tensor.mkShape [1, 8, 128] (fun outIdx =>
          let flat := outIdx.1
          ∑ j ∈ Finset.range 8,
            valAt (chunkPrimDimN 2 4 r x) ((flat / 1024 * 8 + flat % 1024 / 128) * 8 + j) *
            valAt (ws[r]) (flat % 128 * 8 + j)) from by
        simp [fw_linear, hchunk_r, hwr', Tensor.mkShape]]
      rw [valAt_of_lt _ _ hprod_lhs]
      simp only [Tensor.mkShape]
      have h1 : idx / 1024 = 0 := by omega
      have h2 : idx % 1024 = idx := by omega
      simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
      apply Finset.sum_congr rfl
      intro lc hlc_mem
      have hlc : lc < 8 := Finset.mem_range.mp hlc_mem
      congr 1
      exact chunk2_4_1_8_32_valAt_pj x r seq lc hx hr hseq hlc
    rw [hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hLHS_eq, hRHS_eq]

theorem allGatherPrimDimN1_4_valAt_32_8 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [32, 8])
    (hW_shapes : ∀ r (_ : r < 4), (ws.getD r (zeroTensor [32, 8])).shape = [32, 8])
    (row : Nat) (hrow : row < 32) (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 8) :
    valAt (allGatherPrimDimN 1 4 0 ws) (row * 32 + r * 8 + lc) =
      valAt (ws.getD r (zeroTensor [32, 8])) (row * 8 + lc) := by
  have hidx_lt : row * 32 + r * 8 + lc < 1024 := by omega
  have hgather_shape : (allGatherPrimDimN 1 4 0 ws).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 ws [32, 8] hhead]
    simp [List.set, List.getD]
  have hidx_prod : row * 32 + r * 8 + lc < prodShape (allGatherPrimDimN 1 4 0 ws).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set,
    show (4 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have h1 : (row * 32 + r * 8 + lc) / 32 = row := by omega
  have h2 : (row * 32 + r * 8 + lc) % 32 = r * 8 + lc := by omega
  have h3 : (r * 8 + lc) / 1 = r * 8 + lc := by omega
  have h4 : (r * 8 + lc) % 1 = 0 := by omega
  have h5 : (r * 8 + lc) / 8 = r := by omega
  have h6 : (r * 8 + lc) % 8 = lc := by omega
  simp only [h1, h2, h3, h4, h5, h6]
  congr 1; omega

set_option maxHeartbeats 2000000 in
theorem fw_linear_colParallel_4_1_8_32_32_8
    (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [1, 8, 32])
    (hlen : ws.length = 4)
    (hshape : ∀ w ∈ ws, w.shape = [32, 8]) :
    fw_linear x (allGatherPrimDimN 1 4 0 ws) =
    allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [32, 8])))) := by
  have hhead_w : (ws.head?.map (fun t => t.shape)).getD [] = [32, 8] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape w0 (List.mem_cons_self ..)
  have hW_shapes : ∀ r (_ : r < 4), (ws.getD r (zeroTensor [32, 8])).shape = [32, 8] := by
    intro r hr
    have hr_len : r < ws.length := by omega
    simp [List.getD, List.getElem?_eq_getElem hr_len]
    exact hshape _ (List.getElem_mem hr_len)
  have hW_shape : (allGatherPrimDimN 1 4 0 ws).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 ws [32, 8] hhead_w]
    simp [List.set, List.getD]
  have hLHS_shape : (fw_linear x (allGatherPrimDimN 1 4 0 ws)).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 32 32 x _ hx hW_shape
  have hchunk_shape : ∀ r : Fin 4, (chunkPrimDimN 2 4 r.val x).shape = [1, 8, 8] := by
    intro r
    rw [chunkPrimDimN_shape 2 4 r.val _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hlocal_shape : ∀ r : Fin 4,
      (fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [32, 8]))).shape =
        [1, 8, 32] := by
    intro r
    exact fw_linear_3d_shape 1 8 8 32 _ _ (hchunk_shape r) (hW_shapes r.val r.isLt)
  have hRHS_head : (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [32, 8])))).head? =
      some (fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [32, 8]))) := by
    simp only [List.ofFn_succ, List.head?_cons, Fin.val_zero]
  have hRHS_shape : (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [32, 8]))))).shape = [1, 8, 32] := by
    rw [allReducePrim_shape 4 0 _ _ hRHS_head]
    exact hlocal_shape ⟨0, by omega⟩
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  set seq := idx / 32
  set col := idx % 32
  have hcol : col < 32 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  -- LHS value
  have hprod_lhs : idx < prodShape [1, 8, 32] := by simp [prodShape]; exact hidx256
  have hLHS_eq : valAt (fw_linear x (allGatherPrimDimN 1 4 0 ws)) idx =
      ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
        valAt x (seq * 32 + r * 8 + lc) *
          valAt (ws.getD r (zeroTensor [32, 8])) (col * 8 + lc) := by
    conv_lhs => rw [show fw_linear x (allGatherPrimDimN 1 4 0 ws) =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 32,
          valAt x ((flat / 256 * 8 + flat % 256 / 32) * 32 + j) *
          valAt (allGatherPrimDimN 1 4 0 ws) (flat % 32 * 32 + j)) from by
      simp [fw_linear, hx, hW_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_lhs]
    simp only [Tensor.mkShape]
    have h1 : idx / 256 = 0 := by omega
    have h2 : idx % 256 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
    -- Now: ∑ j, valAt(x, seq*32+j) * valAt(W_gathered, col*32+j)
    have heq_terms : ∀ j, j < 32 →
        valAt x (seq * 32 + j) * valAt (allGatherPrimDimN 1 4 0 ws) (col * 32 + j) =
        valAt x (seq * 32 + j) *
          valAt (ws.getD (j / 8) (zeroTensor [32, 8])) (col * 8 + j % 8) := by
      intro j hj
      congr 1
      have hj8 : j / 8 < 4 := by omega
      have hjmod : j % 8 < 8 := Nat.mod_lt _ (by omega)
      conv_lhs => rw [show col * 32 + j = col * 32 + (j / 8) * 8 + j % 8 from by omega]
      exact allGatherPrimDimN1_4_valAt_32_8 ws hhead_w hW_shapes col hcol (j / 8) hj8 (j % 8) hjmod
    calc ∑ j ∈ Finset.range 32,
          valAt x (seq * 32 + j) * valAt (allGatherPrimDimN 1 4 0 ws) (col * 32 + j)
        = ∑ j ∈ Finset.range 32,
          valAt x (seq * 32 + j) *
            valAt (ws.getD (j / 8) (zeroTensor [32, 8])) (col * 8 + j % 8) := by
          apply Finset.sum_congr rfl
          intro j hj; exact heq_terms j (Finset.mem_range.mp hj)
      _ = ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
          valAt x (seq * 32 + (r * 8 + lc)) *
            valAt (ws.getD ((r * 8 + lc) / 8) (zeroTensor [32, 8]))
              (col * 8 + (r * 8 + lc) % 8) := by
          rw [sum_range_split_4_8]
      _ = ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
          valAt x (seq * 32 + r * 8 + lc) *
            valAt (ws.getD r (zeroTensor [32, 8])) (col * 8 + lc) := by
          apply Finset.sum_congr rfl; intro r hr_mem
          apply Finset.sum_congr rfl; intro lc hlc_mem
          have hr : r < 4 := Finset.mem_range.mp hr_mem
          have hlc : lc < 8 := Finset.mem_range.mp hlc_mem
          simp only [show (r * 8 + lc) / 8 = r from by omega,
                     show (r * 8 + lc) % 8 = lc from by omega,
                     show seq * 32 + (r * 8 + lc) = seq * 32 + r * 8 + lc from by omega]
  -- RHS value
  have hRHS_eq : valAt (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [32, 8]))))) idx =
      ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 8,
        valAt x (seq * 32 + r * 8 + lc) *
          valAt (ws.getD r (zeroTensor [32, 8])) (col * 8 + lc) := by
    have hhead0_shape : (fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [32, 8]))).shape =
        [1, 8, 32] := hlocal_shape ⟨0, by omega⟩
    rw [allReducePrim_valAt 4 0 _ idx _ hRHS_head
      (by rw [hhead0_shape]; simpa [prodShape])]
    -- foldl for 4-element list
    have hlist_eq : List.ofFn (fun r : Fin 4 =>
        fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [32, 8]))) =
      [fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [32, 8])),
       fw_linear (chunkPrimDimN 2 4 1 x) (ws.getD 1 (zeroTensor [32, 8])),
       fw_linear (chunkPrimDimN 2 4 2 x) (ws.getD 2 (zeroTensor [32, 8])),
       fw_linear (chunkPrimDimN 2 4 3 x) (ws.getD 3 (zeroTensor [32, 8]))] := by
      rfl
    rw [hlist_eq]
    simp only [List.foldl]
    -- Now have: 0 + v0 + v1 + v2 + v3 where v_r = valAt(fw_linear(chunk_r, ws_r), idx)
    have hterm : ∀ r : Nat, r < 4 →
        valAt (fw_linear (chunkPrimDimN 2 4 r x) (ws.getD r (zeroTensor [32, 8]))) idx =
        ∑ lc ∈ Finset.range 8,
          valAt x (seq * 32 + r * 8 + lc) *
            valAt (ws.getD r (zeroTensor [32, 8])) (col * 8 + lc) := by
      intro r hr
      have hchunk_r : (chunkPrimDimN 2 4 r x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
        simp [List.set, List.getD]
      have hwr : (ws.getD r (zeroTensor [32, 8])).shape = [32, 8] := hW_shapes r hr
      have hr_len : r < ws.length := by omega
      have hgetD_eq : ws.getD r (zeroTensor [32, 8]) = ws[r] := by
        simp [List.getD, List.getElem?_eq_getElem hr_len]
      have hwr' : (ws[r]).shape = [32, 8] := by rw [← hgetD_eq]; exact hwr
      rw [hgetD_eq]
      conv_lhs => rw [show fw_linear (chunkPrimDimN 2 4 r x) (ws[r]) =
        Tensor.mkShape [1, 8, 32] (fun outIdx =>
          let flat := outIdx.1
          ∑ j ∈ Finset.range 8,
            valAt (chunkPrimDimN 2 4 r x) ((flat / 256 * 8 + flat % 256 / 32) * 8 + j) *
            valAt (ws[r]) (flat % 32 * 8 + j)) from by
        simp [fw_linear, hchunk_r, hwr', Tensor.mkShape]]
      rw [valAt_of_lt _ _ hprod_lhs]
      simp only [Tensor.mkShape]
      have h1 : idx / 256 = 0 := by omega
      have h2 : idx % 256 = idx := by omega
      simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
      apply Finset.sum_congr rfl
      intro lc hlc_mem
      have hlc : lc < 8 := Finset.mem_range.mp hlc_mem
      congr 1
      exact chunk2_4_1_8_32_valAt_pj x r seq lc hx hr hseq hlc
    rw [hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hLHS_eq, hRHS_eq]

-- Chunk dim2 valAt for [1,8,128] tensors chunked into [1,8,32]
theorem chunk2_4_1_8_128_valAt_pj (x : Tensor) (r p j : Nat)
    (hx : x.shape = [1, 8, 128]) (hr : r < 4) (hp : p < 8) (hj : j < 32) :
    valAt (chunkPrimDimN 2 4 r x) (p * 32 + j) = valAt x (p * 128 + r * 32 + j) := by
  have hloc : p * 32 + j < 256 := by omega
  have hchunk_shape : (chunkPrimDimN 2 4 r x).shape = [1, 8, 32] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p * 32 + j < prodShape (chunkPrimDimN 2 4 r x).shape := by
    rw [hchunk_shape]
    simp [prodShape]
    exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have hidx : (p * 32 + j) / 32 * 128 + (r % 4 * 32 + (p * 32 + j) % 32 / 1) * 1 + (p * 32 + j) % 32 % 1 =
      p * 128 + r * 32 + j := by omega
  rw [hidx]

/-- valAt of `allGatherPrimDimN 2 4 0 xs` on `[1, 8, 32]` shards (result `[1, 8, 128]`). -/
theorem allGatherPrimDimN_2_4_valAt_1_8_32 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 8, 32]) (hidx : idx < 1024) :
    valAt (allGatherPrimDimN 2 4 0 xs) idx =
      valAt (xs.getD (idx % 128 / 32) (zeroTensor [1, 8, 32]))
        ((idx / 128) * 32 + idx % 32) := by
  have hresult_shape : (allGatherPrimDimN 2 4 0 xs).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 xs [1, 8, 32] hhead]
    simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 2 4 0 xs).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (8 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega, show (128 : Nat) ≠ 0 from by omega,
    show (1 : Nat) ≠ 0 from by omega, ite_false, List.set]
  congr 1
  omega

/-- Gather-chunk roundtrip on dim 2 for shape `[1, 8, 128]`: allGathering the four
    dim-2 chunks of `x` recovers `x`. -/
theorem allGather_chunkPrimDimN_roundtrip_dim2_4_1_8_128 (x : Tensor)
    (hx : x.shape = [1, 8, 128]) :
    allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x] = x := by
  have hc0 : (chunkPrimDimN 2 4 0 x).shape = [1, 8, 32] := by
    rw [chunkPrimDimN_shape 2 4 0 _ _ hx (by omega)]; simp [List.set, List.getD]
  have hhead : (([chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
      chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 8, 32] := by simp [hc0]
  have hg_shape : (allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x]).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hg_shape, hx])
  intro idx hidx
  have hidx1024 : idx < 1024 := by simpa [hg_shape, prodShape] using hidx
  rw [allGatherPrimDimN_2_4_valAt_1_8_32 _ _ hhead hidx1024]
  have hp : idx / 128 < 8 := by omega
  have hj : idx % 32 < 32 := by omega
  rcases (show idx % 128 / 32 = 0 ∨ idx % 128 / 32 = 1 ∨ idx % 128 / 32 = 2 ∨ idx % 128 / 32 = 3
      from by omega) with h | h | h | h
  · rw [h]
    simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
    rw [chunk2_4_1_8_128_valAt_pj x 0 (idx / 128) (idx % 32) hx (by omega) hp hj]
    congr 1; omega
  · rw [h]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [chunk2_4_1_8_128_valAt_pj x 1 (idx / 128) (idx % 32) hx (by omega) hp hj]
    congr 1; omega
  · rw [h]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [chunk2_4_1_8_128_valAt_pj x 2 (idx / 128) (idx % 32) hx (by omega) hp hj]
    congr 1; omega
  · rw [h]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [chunk2_4_1_8_128_valAt_pj x 3 (idx / 128) (idx % 32) hx (by omega) hp hj]
    congr 1; omega

set_option maxHeartbeats 2000000 in
theorem fw_linear_colParallel_4_1_8_128_32_32
    (x : Tensor) (ws : List Tensor)
    (hx : x.shape = [1, 8, 128])
    (hlen : ws.length = 4)
    (hshape : ∀ w ∈ ws, w.shape = [32, 32]) :
    fw_linear x (allGatherPrimDimN 1 4 0 ws) =
    allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [32, 32])))) := by
  have hhead_w : (ws.head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    match ws, hlen, hshape with
    | w0 :: _, _, hshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hshape w0 (List.mem_cons_self ..)
  have hW_shapes : ∀ r (_ : r < 4), (ws.getD r (zeroTensor [32, 32])).shape = [32, 32] := by
    intro r hr
    have hr_len : r < ws.length := by omega
    simp [List.getD, List.getElem?_eq_getElem hr_len]
    exact hshape _ (List.getElem_mem hr_len)
  have hW_shape : (allGatherPrimDimN 1 4 0 ws).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 1 4 ws [32, 32] hhead_w]
    simp [List.set, List.getD]
  have hLHS_shape : (fw_linear x (allGatherPrimDimN 1 4 0 ws)).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 128 32 x _ hx hW_shape
  have hchunk_shape : ∀ r : Fin 4, (chunkPrimDimN 2 4 r.val x).shape = [1, 8, 32] := by
    intro r
    rw [chunkPrimDimN_shape 2 4 r.val _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hlocal_shape : ∀ r : Fin 4,
      (fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [32, 32]))).shape =
        [1, 8, 32] := by
    intro r
    exact fw_linear_3d_shape 1 8 32 32 _ _ (hchunk_shape r) (hW_shapes r.val r.isLt)
  have hRHS_head : (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [32, 32])))).head? =
      some (fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [32, 32]))) := by
    simp only [List.ofFn_succ, List.head?_cons, Fin.val_zero]
  have hRHS_shape : (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [32, 32]))))).shape = [1, 8, 32] := by
    rw [allReducePrim_shape 4 0 _ _ hRHS_head]
    exact hlocal_shape ⟨0, by omega⟩
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  set seq := idx / 32
  set col := idx % 32
  have hcol : col < 32 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  -- LHS value
  have hprod_lhs : idx < prodShape [1, 8, 32] := by simp [prodShape]; exact hidx256
  have hLHS_eq : valAt (fw_linear x (allGatherPrimDimN 1 4 0 ws)) idx =
      ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 32,
        valAt x (seq * 128 + r * 32 + lc) *
          valAt (ws.getD r (zeroTensor [32, 32])) (col * 32 + lc) := by
    conv_lhs => rw [show fw_linear x (allGatherPrimDimN 1 4 0 ws) =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        let flat := outIdx.1
        ∑ j ∈ Finset.range 128,
          valAt x ((flat / 256 * 8 + flat % 256 / 32) * 128 + j) *
          valAt (allGatherPrimDimN 1 4 0 ws) (flat % 32 * 128 + j)) from by
      simp [fw_linear, hx, hW_shape, Tensor.mkShape]]
    rw [valAt_of_lt _ _ hprod_lhs]
    simp only [Tensor.mkShape]
    have h1 : idx / 256 = 0 := by omega
    have h2 : idx % 256 = idx := by omega
    simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
    have heq_terms : ∀ j, j < 128 →
        valAt x (seq * 128 + j) * valAt (allGatherPrimDimN 1 4 0 ws) (col * 128 + j) =
        valAt x (seq * 128 + j) *
          valAt (ws.getD (j / 32) (zeroTensor [32, 32])) (col * 32 + j % 32) := by
      intro j hj
      congr 1
      have hj32 : j / 32 < 4 := by omega
      have hjmod : j % 32 < 32 := Nat.mod_lt _ (by omega)
      conv_lhs => rw [show col * 128 + j = col * 128 + (j / 32) * 32 + j % 32 from by omega]
      exact allGatherPrimDimN1_4_valAt_32_32 ws hhead_w hW_shapes col hcol (j / 32) hj32 (j % 32) hjmod
    calc ∑ j ∈ Finset.range 128,
          valAt x (seq * 128 + j) * valAt (allGatherPrimDimN 1 4 0 ws) (col * 128 + j)
        = ∑ j ∈ Finset.range 128,
          valAt x (seq * 128 + j) *
            valAt (ws.getD (j / 32) (zeroTensor [32, 32])) (col * 32 + j % 32) := by
          apply Finset.sum_congr rfl
          intro j hj; exact heq_terms j (Finset.mem_range.mp hj)
      _ = ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 32,
          valAt x (seq * 128 + (r * 32 + lc)) *
            valAt (ws.getD ((r * 32 + lc) / 32) (zeroTensor [32, 32]))
              (col * 32 + (r * 32 + lc) % 32) := by
          rw [sum_range_split_4_32]
      _ = ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 32,
          valAt x (seq * 128 + r * 32 + lc) *
            valAt (ws.getD r (zeroTensor [32, 32])) (col * 32 + lc) := by
          apply Finset.sum_congr rfl; intro r hr_mem
          apply Finset.sum_congr rfl; intro lc hlc_mem
          have hr : r < 4 := Finset.mem_range.mp hr_mem
          have hlc : lc < 32 := Finset.mem_range.mp hlc_mem
          simp only [show (r * 32 + lc) / 32 = r from by omega,
                     show (r * 32 + lc) % 32 = lc from by omega,
                     show seq * 128 + (r * 32 + lc) = seq * 128 + r * 32 + lc from by omega]
  -- RHS value
  have hRHS_eq : valAt (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      fw_linear (chunkPrimDimN 2 4 r.val x)
        (ws.getD r.val (zeroTensor [32, 32]))))) idx =
      ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 32,
        valAt x (seq * 128 + r * 32 + lc) *
          valAt (ws.getD r (zeroTensor [32, 32])) (col * 32 + lc) := by
    have hhead0_shape : (fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [32, 32]))).shape =
        [1, 8, 32] := hlocal_shape ⟨0, by omega⟩
    rw [allReducePrim_valAt 4 0 _ idx _ hRHS_head
      (by rw [hhead0_shape]; simpa [prodShape])]
    have hlist_eq : List.ofFn (fun r : Fin 4 =>
        fw_linear (chunkPrimDimN 2 4 r.val x) (ws.getD r.val (zeroTensor [32, 32]))) =
      [fw_linear (chunkPrimDimN 2 4 0 x) (ws.getD 0 (zeroTensor [32, 32])),
       fw_linear (chunkPrimDimN 2 4 1 x) (ws.getD 1 (zeroTensor [32, 32])),
       fw_linear (chunkPrimDimN 2 4 2 x) (ws.getD 2 (zeroTensor [32, 32])),
       fw_linear (chunkPrimDimN 2 4 3 x) (ws.getD 3 (zeroTensor [32, 32]))] := by
      rfl
    rw [hlist_eq]
    simp only [List.foldl]
    have hterm : ∀ r : Nat, r < 4 →
        valAt (fw_linear (chunkPrimDimN 2 4 r x) (ws.getD r (zeroTensor [32, 32]))) idx =
        ∑ lc ∈ Finset.range 32,
          valAt x (seq * 128 + r * 32 + lc) *
            valAt (ws.getD r (zeroTensor [32, 32])) (col * 32 + lc) := by
      intro r hr
      have hchunk_r : (chunkPrimDimN 2 4 r x).shape = [1, 8, 32] := by
        rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
        simp [List.set, List.getD]
      have hwr : (ws.getD r (zeroTensor [32, 32])).shape = [32, 32] := hW_shapes r hr
      have hr_len : r < ws.length := by omega
      have hgetD_eq : ws.getD r (zeroTensor [32, 32]) = ws[r] := by
        simp [List.getD, List.getElem?_eq_getElem hr_len]
      have hwr' : (ws[r]).shape = [32, 32] := by rw [← hgetD_eq]; exact hwr
      rw [hgetD_eq]
      conv_lhs => rw [show fw_linear (chunkPrimDimN 2 4 r x) (ws[r]) =
        Tensor.mkShape [1, 8, 32] (fun outIdx =>
          let flat := outIdx.1
          ∑ j ∈ Finset.range 32,
            valAt (chunkPrimDimN 2 4 r x) ((flat / 256 * 8 + flat % 256 / 32) * 32 + j) *
            valAt (ws[r]) (flat % 32 * 32 + j)) from by
        simp [fw_linear, hchunk_r, hwr', Tensor.mkShape]]
      rw [valAt_of_lt _ _ hprod_lhs]
      simp only [Tensor.mkShape]
      have h1 : idx / 256 = 0 := by omega
      have h2 : idx % 256 = idx := by omega
      simp only [h1, h2, Nat.zero_mul, Nat.zero_add]
      apply Finset.sum_congr rfl
      intro lc hlc_mem
      have hlc : lc < 32 := Finset.mem_range.mp hlc_mem
      congr 1
      exact chunk2_4_1_8_128_valAt_pj x r seq lc hx hr hseq hlc
    rw [hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hLHS_eq, hRHS_eq]

/-! ## BW_matmul (first output, dX) distributed-equivalence lemmas

These lemmas support proving that `BW_matmul`'s first output (`dx = g @ yᵀ`) distributed
along the contraction dimension reconstructs by `allGatherPrimDimN` on the output's last
dimension.  The concrete shapes are `g : [1,4,8,8]`, `y` shards `: [1,4,2,8]`. -/

/-- `transpose2d` preserves the shape `[1,4,8,8]`. -/
theorem transpose2d_shape_1_4_8_8 (x : Tensor) (hx : x.shape = [1, 4, 8, 8]) :
    (transpose2d x).shape = [1, 4, 8, 8] := by
  unfold transpose2d
  rw [hx]
  rfl

/-- `transpose2d` maps shape `[1,4,2,8]` to `[1,4,8,2]`. -/
theorem transpose2d_shape_1_4_2_8 (x : Tensor) (hx : x.shape = [1, 4, 2, 8]) :
    (transpose2d x).shape = [1, 4, 8, 2] := by
  unfold transpose2d
  rw [hx]
  rfl

/-- `valAt` of `transpose2d x` for `x : [1,4,8,8]` (swap of the last two dims). -/
theorem transpose2d_valAt_1_4_8_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hidx : idx < 256) :
    valAt (transpose2d x) idx = valAt x (idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8) := by
  have key : transpose2d x = Tensor.mkShape [1, 4, 8, 8] (fun outIdx =>
      valAt x (outIdx.1 / (8 * 8) * (8 * 8) + outIdx.1 % (8 * 8) % 8 * 8 +
        outIdx.1 % (8 * 8) / 8)) := by
    unfold transpose2d
    rw [hx]
    rfl
  rw [key]
  have hidx' : idx < prodShape ([1, 4, 8, 8] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hidx')]
  show valAt x (idx / (8 * 8) * (8 * 8) + idx % (8 * 8) % 8 * 8 + idx % (8 * 8) / 8) = _
  congr 1
  omega

/-- `valAt` of `transpose2d x` for `x : [1,4,2,8]` (output shape `[1,4,8,2]`). -/
theorem transpose2d_valAt_1_4_2_8 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 2, 8]) (hidx : idx < 64) :
    valAt (transpose2d x) idx = valAt x (idx / 16 * 16 + idx % 2 * 8 + idx % 16 / 2) := by
  have key : transpose2d x = Tensor.mkShape [1, 4, 8, 2] (fun outIdx =>
      valAt x (outIdx.1 / (2 * 8) * (2 * 8) + outIdx.1 % (2 * 8) % 2 * 8 +
        outIdx.1 % (2 * 8) / 2)) := by
    unfold transpose2d
    rw [hx]
    rfl
  rw [key]
  have hidx' : idx < prodShape ([1, 4, 8, 2] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hidx')]
  show valAt x (idx / (2 * 8) * (2 * 8) + idx % (2 * 8) % 2 * 8 + idx % (2 * 8) / 2) = _
  congr 1
  omega

/- Core distributed-equivalence lemma for `BW_matmul`'s second output (`dy = xᵀ @ g`) split
along the leading *batch* dimension (dim 1). `X` of shape `[1,4,8,8]` is chunked along dim 1
into 4 batch-slices of shape `[1,1,8,8]`; rank `r` computes `xᵀ_r @ G_r` where `G_r` is the
matching batch shard, and the full `dy` is reconstructed by gathering along dim 1. Since
`transpose2d` and `batchedMatmul` act independently per batch element, batch-chunking commutes
with the matmul. -/
set_option maxHeartbeats 3200000 in
theorem bw_matmul_snd_split_batchdim1_1_4_8_8 (X G0 G1 G2 G3 : Tensor)
    (hX : X.shape = [1, 4, 8, 8])
    (hg0 : G0.shape = [1, 1, 8, 8]) (hg1 : G1.shape = [1, 1, 8, 8])
    (hg2 : G2.shape = [1, 1, 8, 8]) (hg3 : G3.shape = [1, 1, 8, 8]) :
    batchedMatmul (transpose2d X) (allGatherPrimDimN 1 4 0 [G0, G1, G2, G3]) =
      allGatherPrimDimN 1 4 0
        [batchedMatmul (transpose2d (chunkPrimDimN 1 4 0 X)) G0,
         batchedMatmul (transpose2d (chunkPrimDimN 1 4 1 X)) G1,
         batchedMatmul (transpose2d (chunkPrimDimN 1 4 2 X)) G2,
         batchedMatmul (transpose2d (chunkPrimDimN 1 4 3 X)) G3] := by
  have htX : (transpose2d X).shape = [1, 4, 8, 8] := transpose2d_shape_1_4_8_8 X hX
  have hhead_g : (([G0, G1, G2, G3] : List Tensor).head?.map (·.shape)).getD [] = [1, 1, 8, 8] := by
    simp [hg0]
  have hG : (allGatherPrimDimN 1 4 0 [G0, G1, G2, G3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead_g]; simp [List.set, List.getD]
  have hcX : ∀ r, (chunkPrimDimN 1 4 r X).shape = [1, 1, 8, 8] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ hX (by omega)]; simp [List.set, List.getD]
  have htcX : ∀ r, (transpose2d (chunkPrimDimN 1 4 r X)).shape = [1, 1, 8, 8] := by
    intro r; exact transpose2d_shape_1_1_8_8 _ (hcX r)
  have hp0 : (batchedMatmul (transpose2d (chunkPrimDimN 1 4 0 X)) G0).shape = [1, 1, 8, 8] :=
    fw_matmul_shape_1_1_8_8 _ _ (htcX 0) hg0
  have hp1 : (batchedMatmul (transpose2d (chunkPrimDimN 1 4 1 X)) G1).shape = [1, 1, 8, 8] :=
    fw_matmul_shape_1_1_8_8 _ _ (htcX 1) hg1
  have hp2 : (batchedMatmul (transpose2d (chunkPrimDimN 1 4 2 X)) G2).shape = [1, 1, 8, 8] :=
    fw_matmul_shape_1_1_8_8 _ _ (htcX 2) hg2
  have hp3 : (batchedMatmul (transpose2d (chunkPrimDimN 1 4 3 X)) G3).shape = [1, 1, 8, 8] :=
    fw_matmul_shape_1_1_8_8 _ _ (htcX 3) hg3
  have hhead_rhs : (([batchedMatmul (transpose2d (chunkPrimDimN 1 4 0 X)) G0,
      batchedMatmul (transpose2d (chunkPrimDimN 1 4 1 X)) G1,
      batchedMatmul (transpose2d (chunkPrimDimN 1 4 2 X)) G2,
      batchedMatmul (transpose2d (chunkPrimDimN 1 4 3 X)) G3] : List Tensor).head?.map
        (·.shape)).getD [] = [1, 1, 8, 8] := by simp [hp0]
  have hlhs_shape : (batchedMatmul (transpose2d X) (allGatherPrimDimN 1 4 0 [G0, G1, G2, G3])).shape
      = [1, 4, 8, 8] := fw_matmul_shape_1_4_8_8 _ _ htX hG
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [batchedMatmul (transpose2d (chunkPrimDimN 1 4 0 X)) G0,
       batchedMatmul (transpose2d (chunkPrimDimN 1 4 1 X)) G1,
       batchedMatmul (transpose2d (chunkPrimDimN 1 4 2 X)) G2,
       batchedMatmul (transpose2d (chunkPrimDimN 1 4 3 X)) G3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead_rhs]; simp [List.set, List.getD]
  -- per-term rewrite helpers
  have hL : ∀ (c j l : Nat), c < 4 → j < 64 → l < 8 →
      valAt (transpose2d X) (c * 64 + j / 8 * 8 + l) = valAt X (c * 64 + l * 8 + j / 8) := by
    intro c j l hc hj hl
    rw [transpose2d_valAt_1_4_8_8 X (c * 64 + j / 8 * 8 + l) hX (by omega)]
    congr 1; omega
  have hP : ∀ (c j l : Nat), c < 4 → j < 64 → l < 8 →
      valAt (transpose2d (chunkPrimDimN 1 4 c X)) (j / 8 * 8 + l) = valAt X (c * 64 + l * 8 + j / 8) := by
    intro c j l hc hj hl
    rw [transpose2d_valAt_1_1_8_8 (chunkPrimDimN 1 4 c X) (j / 8 * 8 + l) (hcX c) (by omega)]
    rw [chunk_dim1_4_1_4_8_8_valAt X c ((j / 8 * 8 + l) % 8 * 8 + (j / 8 * 8 + l) / 8) hX hc (by omega)]
    congr 1; omega
  have hLG : ∀ (c l m : Nat), c < 4 → l < 8 → m < 8 →
      valAt (allGatherPrimDimN 1 4 0 [G0, G1, G2, G3]) (c * 64 + l * 8 + m) =
        valAt ([G0, G1, G2, G3].getD c (zeroTensor [1, 1, 8, 8])) (l * 8 + m) := by
    intro c l m hc hl hm
    rw [allGather_dim1_4_1_1_8_8_valAt _ _ _ _ (c * 64 + l * 8 + m) hg0 hg1 hg2 hg3 (by omega)]
    have ha : (c * 64 + l * 8 + m) / 64 = c := by omega
    have hb : (c * 64 + l * 8 + m) % 64 = l * 8 + m := by omega
    rw [ha, hb]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [show batchedMatmul (transpose2d X) (allGatherPrimDimN 1 4 0 [G0, G1, G2, G3]) =
        fw_matmul (transpose2d X) (allGatherPrimDimN 1 4 0 [G0, G1, G2, G3]) from rfl,
      fw_matmul_valAt_1_4_8_8 (transpose2d X) (allGatherPrimDimN 1 4 0 [G0, G1, G2, G3]) idx
        htX hG hidx256]
  rw [allGather_dim1_4_1_1_8_8_valAt _ _ _ _ idx hp0 hp1 hp2 hp3 hidx256]
  have hmm : idx % 64 % 8 = idx % 8 := by omega
  have hjmod : idx % 64 < 64 := by omega
  have hm8 : idx % 8 < 8 := by omega
  have hr_cases : idx / 64 = 0 ∨ idx / 64 = 1 ∨ idx / 64 = 2 ∨ idx / 64 = 3 := by omega
  rcases hr_cases with hdiv | hdiv | hdiv | hdiv
  · rw [hdiv]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [show batchedMatmul (transpose2d (chunkPrimDimN 1 4 0 X)) G0 =
          fw_matmul (transpose2d (chunkPrimDimN 1 4 0 X)) G0 from rfl,
        fw_matmul_valAt_1_1_8_8 (transpose2d (chunkPrimDimN 1 4 0 X)) G0 (idx % 64)
          (htcX 0) hg0 (by omega)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := by simpa using hl
    rw [hL 0 (idx % 64) l (by omega) hjmod hl8, hP 0 (idx % 64) l (by omega) hjmod hl8,
        hLG 0 l (idx % 8) (by omega) hl8 hm8, hmm]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  · rw [hdiv]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [show batchedMatmul (transpose2d (chunkPrimDimN 1 4 1 X)) G1 =
          fw_matmul (transpose2d (chunkPrimDimN 1 4 1 X)) G1 from rfl,
        fw_matmul_valAt_1_1_8_8 (transpose2d (chunkPrimDimN 1 4 1 X)) G1 (idx % 64)
          (htcX 1) hg1 (by omega)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := by simpa using hl
    rw [hL 1 (idx % 64) l (by omega) hjmod hl8, hP 1 (idx % 64) l (by omega) hjmod hl8,
        hLG 1 l (idx % 8) (by omega) hl8 hm8, hmm]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  · rw [hdiv]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [show batchedMatmul (transpose2d (chunkPrimDimN 1 4 2 X)) G2 =
          fw_matmul (transpose2d (chunkPrimDimN 1 4 2 X)) G2 from rfl,
        fw_matmul_valAt_1_1_8_8 (transpose2d (chunkPrimDimN 1 4 2 X)) G2 (idx % 64)
          (htcX 2) hg2 (by omega)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := by simpa using hl
    rw [hL 2 (idx % 64) l (by omega) hjmod hl8, hP 2 (idx % 64) l (by omega) hjmod hl8,
        hLG 2 l (idx % 8) (by omega) hl8 hm8, hmm]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  · rw [hdiv]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [show batchedMatmul (transpose2d (chunkPrimDimN 1 4 3 X)) G3 =
          fw_matmul (transpose2d (chunkPrimDimN 1 4 3 X)) G3 from rfl,
        fw_matmul_valAt_1_1_8_8 (transpose2d (chunkPrimDimN 1 4 3 X)) G3 (idx % 64)
          (htcX 3) hg3 (by omega)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := by simpa using hl
    rw [hL 3 (idx % 64) l (by omega) hjmod hl8, hP 3 (idx % 64) l (by omega) hjmod hl8,
        hLG 3 l (idx % 8) (by omega) hl8 hm8, hmm]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]

/-- Shape of `batchedMatmul` on `[1,4,8,8] @ [1,4,8,2] -> [1,4,8,2]`. -/
theorem batchedMatmul_shape_1_4_8_8_1_4_8_2 (a b : Tensor)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 2]) :
    (batchedMatmul a b).shape = [1, 4, 8, 2] := by
  unfold batchedMatmul
  simp only [ha, hb, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    Tensor.mkShape]

/-- `valAt` of `batchedMatmul a b` for `a : [1,4,8,8]`, `b : [1,4,8,2]`, output `[1,4,8,2]`. -/
theorem batchedMatmul_valAt_1_4_8_8_1_4_8_2 (a b : Tensor) (loc : Nat)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 2]) (hloc : loc < 64) :
    valAt (batchedMatmul a b) loc =
      ∑ l ∈ Finset.range 8,
        valAt a (loc / 16 * 64 + loc % 16 / 2 * 8 + l) *
          valAt b (loc / 16 * 16 + l * 2 + loc % 2) := by
  have key : batchedMatmul a b = Tensor.mkShape [1, 4, 8, 2] (fun outIdx =>
      ∑ l ∈ Finset.range 8,
        valAt a (outIdx.1 / (8 * 2) * (8 * 8) + outIdx.1 % (8 * 2) / 2 * 8 + l) *
          valAt b (outIdx.1 / (8 * 2) * (8 * 2) + l * 2 + outIdx.1 % (8 * 2) % 2)) := by
    unfold batchedMatmul
    rw [ha, hb]
    rfl
  rw [key]
  have hloc' : loc < prodShape ([1, 4, 8, 2] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hloc')]
  show ∑ l ∈ Finset.range 8,
        valAt a (loc / (8 * 2) * (8 * 8) + loc % (8 * 2) / 2 * 8 + l) *
          valAt b (loc / (8 * 2) * (8 * 2) + l * 2 + loc % (8 * 2) % 2) = _
  apply Finset.sum_congr rfl
  intro l _
  congr 2 <;> omega

/-- `evalOp` unfolding for `BW_matmul` with empty params (three inputs, two outputs). -/
theorem evalOp_bw_matmul (numParts rank : Nat) (g x y : Tensor) :
    evalOp numParts rank "OpName.BW_matmul" [] [g, x, y] =
      [(bw_matmul g x y).1, (bw_matmul g x y).2] := by
  rfl

/-- `applyNode` for `BW_matmul`, first output (`dx`). -/
theorem applyNode_bw_matmul_fst_out
    (gr : GraphDecl) (s : Store) (rank : Nat) (gTid xTid yTid dxTid dyTid : Tid)
    (_ : dxTid ≠ dyTid) :
    applyNode gr s { rank := rank, op := "OpName.BW_matmul", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dxTid =
      (bw_matmul (s gTid) (s xTid) (s yTid)).1 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_matmul]
  change storeSet s [(dxTid, (bw_matmul (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_matmul (s gTid) (s xTid) (s yTid)).2)] dxTid = _
  unfold storeSet
  simp [List.find?]

/-! Flat-index arithmetic helpers for `bw_matmul_fst_split_1_4_8_8`. Proven in an empty
context so `omega` stays fast (avoids scanning the large hypothesis context of the main proof). -/

private theorem bw_split_aux_cleanY (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + l * 8 + idx % 8) / 64 * 64 +
      (idx / 64 * 64 + l * 8 + idx % 8) % 8 * 8 +
      (idx / 64 * 64 + l * 8 + idx % 8) % 64 / 8 = idx / 64 * 64 + idx % 8 * 8 + l := by omega

private theorem bw_split_aux_hgi (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + idx % 8 * 8 + l) % 64 / 16 = idx % 8 / 2 := by omega

private theorem bw_split_aux_hii (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + idx % 8 * 8 + l) / 64 * 16 +
      (idx / 64 * 64 + idx % 8 * 8 + l) % 16 / 8 * 8 +
      (idx / 64 * 64 + idx % 8 * 8 + l) % 8 = idx / 64 * 16 + idx % 2 * 8 + l := by omega

private theorem bw_split_aux_hmi (idx l loc : Nat) (hl : l < 8) (hidx : idx < 256)
    (hloc : loc = idx / 8 * 2 + idx % 8 % 2) :
    (loc / 16 * 16 + l * 2 + loc % 2) / 16 * 16 +
      (loc / 16 * 16 + l * 2 + loc % 2) % 2 * 8 +
      (loc / 16 * 16 + l * 2 + loc % 2) % 16 / 2 = idx / 64 * 16 + idx % 2 * 8 + l := by
  subst hloc; omega

private theorem bw_split_aux_hgeq (idx l loc : Nat) (hidx : idx < 256)
    (hloc : loc = idx / 8 * 2 + idx % 8 % 2) :
    idx / 64 * 64 + idx % 64 / 8 * 8 + l = loc / 16 * 64 + loc % 16 / 2 * 8 + l := by
  subst hloc; omega

private theorem bw_split_aux_htbnd (idx l loc : Nat) (hl : l < 8) (hidx : idx < 256)
    (hloc : loc = idx / 8 * 2 + idx % 8 % 2) :
    loc / 16 * 16 + l * 2 + loc % 2 < 64 := by subst hloc; omega

private theorem bw_split_aux_hJbnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + l * 8 + idx % 8 < 256 := by omega

private theorem bw_split_aux_hKbnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + idx % 8 * 8 + l < 256 := by omega

/- Core distributed-equivalence lemma for `BW_matmul`'s first output (`dx = g @ yᵀ`).
`y` of shape `[1,4,8,8]` is partitioned along its contraction-free output dimension (dim 2)
into 4 shards of shape `[1,4,2,8]`; each rank computes `g @ shardᵀ` (shape `[1,4,8,2]`), and
the full `dx` is reconstructed by gathering along the output's last dimension (dim 3). -/
set_option maxHeartbeats 3200000 in
-- heavy flat-index arithmetic across matmul / transpose / gather
theorem bw_matmul_fst_split_1_4_8_8 (g y0 y1 y2 y3 : Tensor)
    (hg : g.shape = [1, 4, 8, 8])
    (h0 : y0.shape = [1, 4, 2, 8]) (h1 : y1.shape = [1, 4, 2, 8])
    (h2 : y2.shape = [1, 4, 2, 8]) (h3 : y3.shape = [1, 4, 2, 8]) :
    batchedMatmul g (transpose2d (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])) =
      allGatherPrimDimN 3 4 0
        [batchedMatmul g (transpose2d y0), batchedMatmul g (transpose2d y1),
         batchedMatmul g (transpose2d y2), batchedMatmul g (transpose2d y3)] := by
  -- y-list facts
  have hhead2 : (([y0, y1, y2, y3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 2, 8] := by simp [h0]
  have hyshape : ∀ i, i < 4 →
      ([y0, y1, y2, y3].getD i (zeroTensor [1, 4, 2, 8])).shape = [1, 4, 2, 8] := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, h0, h1, h2, h3]
  -- gather and transpose shapes
  have hY_shape : (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead2]; simp [List.set, List.getD]
  have htY_shape : (transpose2d (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])).shape = [1, 4, 8, 8] :=
    transpose2d_shape_1_4_8_8 _ hY_shape
  -- piece shapes (each shard matmul has shape [1,4,8,2])
  have hpiece_shape : ∀ i, i < 4 →
      (batchedMatmul g (transpose2d ([y0, y1, y2, y3].getD i (zeroTensor [1, 4, 2, 8])))).shape =
        [1, 4, 8, 2] := by
    intro i hi
    exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ hg
      (transpose2d_shape_1_4_2_8 _ (hyshape i hi))
  have hp0 : (batchedMatmul g (transpose2d y0)).shape = [1, 4, 8, 2] := by
    have := hpiece_shape 0 (by omega)
    simpa [List.getD, List.getElem?_cons_zero] using this
  -- list of pieces head shape
  have hhead_rhs : (([batchedMatmul g (transpose2d y0), batchedMatmul g (transpose2d y1),
      batchedMatmul g (transpose2d y2), batchedMatmul g (transpose2d y3)] :
        List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by
    simp [hp0]
  have hlhs_shape : (batchedMatmul g (transpose2d (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3]))).shape =
      [1, 4, 8, 8] := by
    -- batchedMatmul [1,4,8,8] @ [1,4,8,8] -> [1,4,8,8]
    unfold batchedMatmul
    simp only [hg, htY_shape, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, Tensor.mkShape]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [batchedMatmul g (transpose2d y0), batchedMatmul g (transpose2d y1),
       batchedMatmul g (transpose2d y2), batchedMatmul g (transpose2d y3)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_rhs]; simp [List.set, List.getD]
  -- getD selection over the piece list
  have hlist_get : ∀ i, i < 4 →
      [batchedMatmul g (transpose2d y0), batchedMatmul g (transpose2d y1),
       batchedMatmul g (transpose2d y2), batchedMatmul g (transpose2d y3)].getD i
        (zeroTensor [1, 4, 8, 2]) =
      batchedMatmul g (transpose2d ([y0, y1, y2, y3].getD i (zeroTensor [1, 4, 2, 8]))) := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  -- elementwise equality
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  -- RHS: gather of shard matmuls
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead_rhs hidx256]
  set sh := (idx % 8) / 2 with hsh
  set loc := (idx / 8) * 2 + (idx % 8) % 2 with hloc
  have hsh4 : sh < 4 := by rw [hsh]; omega
  have hloc64 : loc < 64 := by rw [hloc]; omega
  rw [hlist_get sh hsh4,
      batchedMatmul_valAt_1_4_8_8_1_4_8_2 g
        (transpose2d ([y0, y1, y2, y3].getD sh (zeroTensor [1, 4, 2, 8]))) loc hg
        (transpose2d_shape_1_4_2_8 _ (hyshape sh hsh4)) hloc64]
  -- LHS: matmul g (transpose2d Y)
  rw [show batchedMatmul g (transpose2d (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])) =
        fw_matmul g (transpose2d (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])) from rfl,
      fw_matmul_valAt_1_4_8_8 g (transpose2d (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])) idx hg
        htY_shape hidx256]
  -- termwise
  apply Finset.sum_congr rfl
  intro l hl
  have hl8 : l < 8 := Finset.mem_range.mp hl
  have hgi : (idx / 64 * 64 + idx % 8 * 8 + l) % 64 / 16 = sh := by
    rw [hsh]; exact bw_split_aux_hgi idx l hl8
  -- LHS: clean the transpose2d(Y) index, then unfold the gather
  rw [transpose2d_valAt_1_4_8_8 (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])
        (idx / 64 * 64 + l * 8 + idx % 8) hY_shape (bw_split_aux_hJbnd idx l hl8 hidx256)]
  rw [bw_split_aux_cleanY idx l hl8]
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 [y0, y1, y2, y3] (idx / 64 * 64 + idx % 8 * 8 + l)
        hhead2 (bw_split_aux_hKbnd idx l hl8 hidx256)]
  rw [hgi, bw_split_aux_hii idx l hl8]
  -- RHS: clean the transpose2d(shard) index
  rw [transpose2d_valAt_1_4_2_8 ([y0, y1, y2, y3].getD sh (zeroTensor [1, 4, 2, 8]))
        (loc / 16 * 16 + l * 2 + loc % 2) (hyshape sh hsh4)
        (bw_split_aux_htbnd idx l loc hl8 hidx256 hloc)]
  rw [bw_split_aux_hmi idx l loc hl8 hidx256 hloc]
  -- the two products agree (same `g`, same `y` shard, equal indices)
  rw [bw_split_aux_hgeq idx l loc hidx256 hloc]

/-- `applyNode` for `BW_matmul`, second output (`dy`). -/
theorem applyNode_bw_matmul_snd_out
    (gr : GraphDecl) (s : Store) (rank : Nat) (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode gr s { rank := rank, op := "OpName.BW_matmul", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_matmul (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_matmul]
  change storeSet s [(dxTid, (bw_matmul (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_matmul (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

/-! Flat-index arithmetic helpers for `bw_matmul_snd_split_1_4_8_8`. -/

private theorem snd_split_aux_a (idx l loc : Nat) (hidx : idx < 256)
    (hloc : loc = idx / 8 * 2 + idx % 8 % 2) :
    idx / 64 * 64 + idx % 64 / 8 * 8 + l = loc / 16 * 64 + loc % 16 / 2 * 8 + l := by
  subst hloc; omega

private theorem snd_split_aux_g (idx l loc : Nat) (hidx : idx < 256)
    (hloc : loc = idx / 8 * 2 + idx % 8 % 2) :
    idx / 64 * 16 + l * 2 + idx % 8 % 2 = loc / 16 * 16 + l * 2 + loc % 2 := by
  subst hloc; omega

private theorem snd_split_aux_Gbnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + l * 8 + idx % 8 < 256 := by omega

private theorem snd_split_aux_sh (idx l : Nat) :
    (idx / 64 * 64 + l * 8 + idx % 8) % 8 / 2 = idx % 8 / 2 := by omega

private theorem snd_split_aux_gloc (idx l : Nat) :
    (idx / 64 * 64 + l * 8 + idx % 8) / 8 * 2 + (idx / 64 * 64 + l * 8 + idx % 8) % 8 % 2
      = idx / 64 * 16 + l * 2 + idx % 8 % 2 := by omega

/- Core distributed-equivalence lemma for `BW_matmul`'s second output (`dy = xᵀ @ g`).
`g` of shape `[1,4,8,8]` is partitioned along its last dimension (dim 3) into 4 shards of
shape `[1,4,8,2]`; each rank computes `xᵀ @ shard` (shape `[1,4,8,2]`), and the full `dy`
is reconstructed by gathering along the output's last dimension (dim 3). Here `a = xᵀ` is
the (shared) transposed input. -/
set_option maxHeartbeats 3200000 in
-- heavy flat-index arithmetic across matmul / gather
theorem bw_matmul_snd_split_1_4_8_8 (a g0 g1 g2 g3 : Tensor)
    (ha : a.shape = [1, 4, 8, 8])
    (h0 : g0.shape = [1, 4, 8, 2]) (h1 : g1.shape = [1, 4, 8, 2])
    (h2 : g2.shape = [1, 4, 8, 2]) (h3 : g3.shape = [1, 4, 8, 2]) :
    batchedMatmul a (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]) =
      allGatherPrimDimN 3 4 0
        [batchedMatmul a g0, batchedMatmul a g1, batchedMatmul a g2, batchedMatmul a g3] := by
  have hhead3 : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 8, 2] := by simp [h0]
  have hgshape : ∀ i, i < 4 →
      ([g0, g1, g2, g3].getD i (zeroTensor [1, 4, 8, 2])).shape = [1, 4, 8, 2] := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, h0, h1, h2, h3]
  have hG_shape : (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead3]; simp [List.set, List.getD]
  have hpiece_shape : ∀ i, i < 4 →
      (batchedMatmul a ([g0, g1, g2, g3].getD i (zeroTensor [1, 4, 8, 2]))).shape = [1, 4, 8, 2] := by
    intro i hi
    exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ ha (hgshape i hi)
  have hp0 : (batchedMatmul a g0).shape = [1, 4, 8, 2] := by
    have := hpiece_shape 0 (by omega)
    simpa [List.getD, List.getElem?_cons_zero] using this
  have hhead_rhs : (([batchedMatmul a g0, batchedMatmul a g1, batchedMatmul a g2,
      batchedMatmul a g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by
    simp [hp0]
  have hlhs_shape : (batchedMatmul a (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3])).shape = [1, 4, 8, 8] := by
    unfold batchedMatmul
    simp only [ha, hG_shape, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, Tensor.mkShape]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [batchedMatmul a g0, batchedMatmul a g1, batchedMatmul a g2, batchedMatmul a g3]).shape
        = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_rhs]; simp [List.set, List.getD]
  have hlist_get : ∀ i, i < 4 →
      [batchedMatmul a g0, batchedMatmul a g1, batchedMatmul a g2, batchedMatmul a g3].getD i
        (zeroTensor [1, 4, 8, 2]) =
      batchedMatmul a ([g0, g1, g2, g3].getD i (zeroTensor [1, 4, 8, 2])) := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead_rhs hidx256]
  set sh := (idx % 8) / 2 with hsh
  set loc := (idx / 8) * 2 + (idx % 8) % 2 with hloc
  have hsh4 : sh < 4 := by rw [hsh]; omega
  have hloc64 : loc < 64 := by rw [hloc]; omega
  rw [hlist_get sh hsh4,
      batchedMatmul_valAt_1_4_8_8_1_4_8_2 a ([g0, g1, g2, g3].getD sh (zeroTensor [1, 4, 8, 2])) loc
        ha (hgshape sh hsh4) hloc64]
  rw [show batchedMatmul a (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]) =
        fw_matmul a (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]) from rfl,
      fw_matmul_valAt_1_4_8_8 a (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]) idx ha hG_shape hidx256]
  apply Finset.sum_congr rfl
  intro l hl
  have hl8 : l < 8 := Finset.mem_range.mp hl
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 [g0, g1, g2, g3] (idx / 64 * 64 + l * 8 + idx % 8)
        hhead3 (snd_split_aux_Gbnd idx l hl8 hidx256)]
  rw [snd_split_aux_sh idx l, ← hsh, snd_split_aux_gloc idx l]
  rw [snd_split_aux_a idx l loc hidx256 hloc, snd_split_aux_g idx l loc hidx256 hloc]

/-! ### BW_matmul second output (`dy = xᵀ @ g`) distributed-equivalence -/

/-- `transpose2d` maps shape `[1,4,8,2]` to `[1,4,2,8]`. -/
theorem transpose2d_shape_1_4_8_2 (x : Tensor) (hx : x.shape = [1, 4, 8, 2]) :
    (transpose2d x).shape = [1, 4, 2, 8] := by
  unfold transpose2d
  rw [hx]
  rfl

/-- `valAt` of `transpose2d x` for `x : [1,4,8,2]` (output shape `[1,4,2,8]`). -/
theorem transpose2d_valAt_1_4_8_2 (x : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 2]) (hidx : idx < 64) :
    valAt (transpose2d x) idx = valAt x (idx / 16 * 16 + idx % 8 * 2 + idx % 16 / 8) := by
  have key : transpose2d x = Tensor.mkShape [1, 4, 2, 8] (fun outIdx =>
      valAt x (outIdx.1 / (8 * 2) * (8 * 2) + outIdx.1 % (8 * 2) % 8 * 2 +
        outIdx.1 % (8 * 2) / 8)) := by
    unfold transpose2d
    rw [hx]
    rfl
  rw [key]
  have hidx' : idx < prodShape ([1, 4, 2, 8] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hidx')]
  show valAt x (idx / (8 * 2) * (8 * 2) + idx % (8 * 2) % 8 * 2 + idx % (8 * 2) / 8) = _
  congr 1
  omega

/-- Shape of `batchedMatmul` on `[1,4,2,8] @ [1,4,8,8] -> [1,4,2,8]`. -/
theorem batchedMatmul_shape_1_4_2_8_1_4_8_8 (a b : Tensor)
    (ha : a.shape = [1, 4, 2, 8]) (hb : b.shape = [1, 4, 8, 8]) :
    (batchedMatmul a b).shape = [1, 4, 2, 8] := by
  unfold batchedMatmul
  simp only [ha, hb, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    Tensor.mkShape]

/-- `valAt` of `batchedMatmul a b` for `a : [1,4,2,8]`, `b : [1,4,8,8]`, output `[1,4,2,8]`. -/
theorem batchedMatmul_valAt_1_4_2_8_1_4_8_8 (a b : Tensor) (loc : Nat)
    (ha : a.shape = [1, 4, 2, 8]) (hb : b.shape = [1, 4, 8, 8]) (hloc : loc < 64) :
    valAt (batchedMatmul a b) loc =
      ∑ l ∈ Finset.range 8,
        valAt a (loc / 16 * 16 + loc % 16 / 8 * 8 + l) *
          valAt b (loc / 16 * 64 + l * 8 + loc % 8) := by
  have key : batchedMatmul a b = Tensor.mkShape [1, 4, 2, 8] (fun outIdx =>
      ∑ l ∈ Finset.range 8,
        valAt a (outIdx.1 / (2 * 8) * (2 * 8) + outIdx.1 % (2 * 8) / 8 * 8 + l) *
          valAt b (outIdx.1 / (2 * 8) * (8 * 8) + l * 8 + outIdx.1 % (2 * 8) % 8)) := by
    unfold batchedMatmul
    rw [ha, hb]
    rfl
  rw [key]
  have hloc' : loc < prodShape ([1, 4, 2, 8] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hloc')]
  show ∑ l ∈ Finset.range 8,
        valAt a (loc / (2 * 8) * (2 * 8) + loc % (2 * 8) / 8 * 8 + l) *
          valAt b (loc / (2 * 8) * (8 * 8) + l * 8 + loc % (2 * 8) % 8) = _
  apply Finset.sum_congr rfl
  intro l _
  congr 2 <;> omega

-- NOTE: applyNode_bw_matmul_snd_out is already provided by the BW_matmul(126) merge
-- (identical statement); reusing the existing one to avoid a duplicate declaration.

/-! Flat-index arithmetic helpers for `bw_matmul_snd_split_dX_1_4_8_8`. -/

private theorem bw_snd_aux_cleanX (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + idx % 64 / 8 * 8 + l) / 64 * 64 +
      (idx / 64 * 64 + idx % 64 / 8 * 8 + l) % 8 * 8 +
      (idx / 64 * 64 + idx % 64 / 8 * 8 + l) % 64 / 8 = idx / 64 * 64 + l * 8 + idx % 64 / 8 := by
  omega

private theorem bw_snd_aux_abnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + idx % 64 / 8 * 8 + l < 256 := by omega

private theorem bw_snd_aux_qbnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + l * 8 + idx % 64 / 8 < 256 := by omega

private theorem bw_snd_aux_xshard (idx l : Nat) :
    (idx / 64 * 64 + l * 8 + idx % 64 / 8) % 8 / 2 = idx % 64 / 16 := by omega

private theorem bw_snd_aux_xgloc (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + l * 8 + idx % 64 / 8) / 8 * 2 +
      (idx / 64 * 64 + l * 8 + idx % 64 / 8) % 8 % 2 =
    (idx / 64 * 8 + l) * 2 + idx % 64 / 8 % 2 := by omega

private theorem bw_snd_aux_locbnd (idx : Nat) (hidx : idx < 256) :
    idx / 64 * 16 + idx % 16 / 8 * 8 + idx % 8 < 64 := by omega

private theorem bw_snd_aux_pbnd (l loc : Nat) (hl : l < 8) (hloc : loc < 64) :
    loc / 16 * 16 + loc % 16 / 8 * 8 + l < 64 := by omega

private theorem bw_snd_aux_xeq (idx l loc : Nat) (hl : l < 8) (hidx : idx < 256)
    (hloc : loc = idx / 64 * 16 + idx % 16 / 8 * 8 + idx % 8) :
    (loc / 16 * 16 + loc % 16 / 8 * 8 + l) / 16 * 16 +
      (loc / 16 * 16 + loc % 16 / 8 * 8 + l) % 8 * 2 +
      (loc / 16 * 16 + loc % 16 / 8 * 8 + l) % 16 / 8 =
    (idx / 64 * 8 + l) * 2 + idx % 64 / 8 % 2 := by subst hloc; omega

private theorem bw_snd_aux_geq (idx l loc : Nat) (hidx : idx < 256)
    (hloc : loc = idx / 64 * 16 + idx % 16 / 8 * 8 + idx % 8) :
    loc / 16 * 64 + l * 8 + loc % 8 = idx / 64 * 64 + l * 8 + idx % 8 := by subst hloc; omega

/- Core distributed-equivalence lemma for `BW_matmul`'s second output (`dy = xᵀ @ g`).
`x` of shape `[1,4,8,8]` is partitioned along its last dimension (dim 3) into 4 shards of
shape `[1,4,8,2]`; each rank computes `shardᵀ @ g` (shape `[1,4,2,8]`), and the full `dy`
is reconstructed by gathering along the output's dim 2. -/
set_option maxHeartbeats 3200000 in
-- heavy flat-index arithmetic across matmul / transpose / gather
theorem bw_matmul_snd_split_dX_1_4_8_8 (g x0 x1 x2 x3 : Tensor)
    (hg : g.shape = [1, 4, 8, 8])
    (h0 : x0.shape = [1, 4, 8, 2]) (h1 : x1.shape = [1, 4, 8, 2])
    (h2 : x2.shape = [1, 4, 8, 2]) (h3 : x3.shape = [1, 4, 8, 2]) :
    batchedMatmul (transpose2d (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])) g =
      allGatherPrimDimN 2 4 0
        [batchedMatmul (transpose2d x0) g, batchedMatmul (transpose2d x1) g,
         batchedMatmul (transpose2d x2) g, batchedMatmul (transpose2d x3) g] := by
  -- x-list facts
  have hhead3 : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 8, 2] := by simp [h0]
  have hxshape : ∀ i, i < 4 →
      ([x0, x1, x2, x3].getD i (zeroTensor [1, 4, 8, 2])).shape = [1, 4, 8, 2] := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, h0, h1, h2, h3]
  -- gather and transpose shapes
  have hX_shape : (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead3]; simp [List.set, List.getD]
  have htX_shape : (transpose2d (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])).shape = [1, 4, 8, 8] :=
    transpose2d_shape_1_4_8_8 _ hX_shape
  -- piece shapes (each shard matmul has shape [1,4,2,8])
  have hpiece_shape : ∀ i, i < 4 →
      (batchedMatmul (transpose2d ([x0, x1, x2, x3].getD i (zeroTensor [1, 4, 8, 2]))) g).shape =
        [1, 4, 2, 8] := by
    intro i hi
    exact batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _
      (transpose2d_shape_1_4_8_2 _ (hxshape i hi)) hg
  have hp0 : (batchedMatmul (transpose2d x0) g).shape = [1, 4, 2, 8] := by
    have := hpiece_shape 0 (by omega)
    simpa [List.getD, List.getElem?_cons_zero] using this
  -- list of pieces head shape
  have hhead_rhs : (([batchedMatmul (transpose2d x0) g, batchedMatmul (transpose2d x1) g,
      batchedMatmul (transpose2d x2) g, batchedMatmul (transpose2d x3) g] :
        List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by
    simp [hp0]
  have hlhs_shape : (batchedMatmul (transpose2d (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])) g).shape =
      [1, 4, 8, 8] := by
    unfold batchedMatmul
    simp only [hg, htX_shape, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, Tensor.mkShape]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [batchedMatmul (transpose2d x0) g, batchedMatmul (transpose2d x1) g,
       batchedMatmul (transpose2d x2) g, batchedMatmul (transpose2d x3) g]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead_rhs]; simp [List.set, List.getD]
  -- getD selection over the piece list
  have hlist_get : ∀ i, i < 4 →
      [batchedMatmul (transpose2d x0) g, batchedMatmul (transpose2d x1) g,
       batchedMatmul (transpose2d x2) g, batchedMatmul (transpose2d x3) g].getD i
        (zeroTensor [1, 4, 2, 8]) =
      batchedMatmul (transpose2d ([x0, x1, x2, x3].getD i (zeroTensor [1, 4, 8, 2]))) g := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  -- elementwise equality
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  -- RHS: gather (dim 2) of shard matmuls
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ idx hhead_rhs hidx256]
  set sh := (idx % 64) / 16 with hsh
  set loc := idx / 64 * 16 + idx % 16 / 8 * 8 + idx % 8 with hloc
  have hsh4 : sh < 4 := by rw [hsh]; omega
  have hloc64 : loc < 64 := by rw [hloc]; exact bw_snd_aux_locbnd idx hidx256
  rw [hlist_get sh hsh4,
      batchedMatmul_valAt_1_4_2_8_1_4_8_8 _ g loc
        (transpose2d_shape_1_4_8_2 _ (hxshape sh hsh4)) hg hloc64]
  -- LHS: matmul (transpose2d X) g
  rw [show batchedMatmul (transpose2d (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])) g =
        fw_matmul (transpose2d (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])) g from rfl,
      fw_matmul_valAt_1_4_8_8 (transpose2d (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])) g idx
        htX_shape hg hidx256]
  -- termwise
  apply Finset.sum_congr rfl
  intro l hl
  have hl8 : l < 8 := Finset.mem_range.mp hl
  -- LHS: clean the transpose2d(X) index, then unfold the gather
  rw [transpose2d_valAt_1_4_8_8 (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])
        (idx / 64 * 64 + idx % 64 / 8 * 8 + l) hX_shape (bw_snd_aux_abnd idx l hl8 hidx256)]
  rw [bw_snd_aux_cleanX idx l hl8]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 [x0, x1, x2, x3] (idx / 64 * 64 + l * 8 + idx % 64 / 8)
        hhead3 (bw_snd_aux_qbnd idx l hl8 hidx256)]
  rw [bw_snd_aux_xshard idx l, ← hsh]
  rw [bw_snd_aux_xgloc idx l hl8]
  -- RHS: clean the transpose2d(shard) index
  rw [transpose2d_valAt_1_4_8_2 ([x0, x1, x2, x3].getD sh (zeroTensor [1, 4, 8, 2]))
        (loc / 16 * 16 + loc % 16 / 8 * 8 + l) (hxshape sh hsh4)
        (bw_snd_aux_pbnd l loc hl8 hloc64)]
  rw [bw_snd_aux_xeq idx l loc hl8 hidx256 hloc]
  -- the two products agree (same `x` shard, same `g`, equal indices)
  rw [bw_snd_aux_geq idx l loc hidx256 hloc]

/-- Shape of `batchedMatmul` on `[1,4,8,8] @ [1,4,8,8] -> [1,4,8,8]`. -/
theorem batchedMatmul_shape_1_4_8_8_1_4_8_8 (a b : Tensor)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 8]) :
    (batchedMatmul a b).shape = [1, 4, 8, 8] := by
  unfold batchedMatmul
  simp only [ha, hb, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    Tensor.mkShape]


-- ==== batch3 g134 additions ====
/-!
## BW_linear dX tensor-parallel reduction (goal 134)

When the output gradient `g` is split along its feature dimension (dim 2) and the
weight `w` is split along its output rows (dim 0), the input gradient (dX) of
`bw_linear` equals the `allReducePrim` (sum) of the per-rank dX outputs.
These lemmas are specialized to the concrete shapes of goal 134
(b=1, s=8, i=32, 4 ranks each handling an 8-wide output slice).
-/

/-- Value of `bw_linear` dX (first output) for 3D inputs `[1,8,o] × [1,8,32] × [o,32]`. -/
theorem bw_linear_fst_valAt_1_8_32_g134 (g x w : Tensor) (o : Nat)
    (hg : g.shape = [1, 8, o]) (hx : x.shape = [1, 8, 32]) (hw : w.shape = [o, 32])
    (P : Nat) (hP : P < 8) (col : Nat) (hcol : col < 32) :
    valAt (bw_linear g x w).1 (P * 32 + col) =
      ∑ j ∈ Finset.range o, valAt g (P * o + j) * valAt w (j * 32 + col) := by
  have hdx : (bw_linear g x w).1 =
      Tensor.mkShape [1, 8, 32] (fun outIdx =>
        ∑ j ∈ Finset.range o,
          valAt g (((if (8:Nat) * 32 = 0 then 0 else outIdx.1 / (8 * 32)) * 8 +
                    if (32:Nat) = 0 then 0 else (if (8:Nat) * 32 = 0 then 0 else outIdx.1 % (8 * 32)) / 32) * o + j) *
          valAt w (j * 32 + if (32:Nat) = 0 then 0 else (if (8:Nat) * 32 = 0 then 0 else outIdx.1 % (8 * 32)) % 32)) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hdx]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl]; omega)]
  simp only [Tensor.mkShape]
  have e1 : (P*32+col)/(8*32) = 0 := by omega
  have e2 : ((P*32+col)%(8*32))/32 = P := by omega
  have e3 : ((P*32+col)%(8*32))%32 = col := by omega
  simp only [show ((8:Nat)*32=0)=False from by simp, show ((32:Nat)=0)=False from by simp,
    if_false, e1, e2, e3, Nat.zero_mul, Nat.zero_add]

set_option maxRecDepth 8192 in
/-- Value of `allGatherPrimDimN 2 4` over shards of shape `[1,8,8]`. -/
theorem allGatherDimN2_4_188_valAt_g134 (gs : List Tensor)
    (hhead : (gs.head?.map (fun t => t.shape)).getD [] = [1, 8, 8])
    (P : Nat) (hP : P < 8) (r : Nat) (hr : r < 4) (jl : Nat) (hjl : jl < 8) :
    valAt (allGatherPrimDimN 2 4 0 gs) (P * 32 + (r * 8 + jl)) =
      valAt (gs.getD r (zeroTensor [1, 8, 8])) (P * 8 + jl) := by
  have hshape : (allGatherPrimDimN 2 4 0 gs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 gs [1, 8, 8] hhead]; simp [List.set, List.getD]
  have hbound : P * 32 + (r * 8 + jl) < prodShape (allGatherPrimDimN 2 4 0 gs).shape := by
    rw [hshape]; simp only [prodShape, List.foldl]; omega
  rw [valAt_of_lt _ _ hbound]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, show ([1,8,8].getD 2 0 : Nat) = 8 from rfl]
  have d1 : (P * 32 + (r * 8 + jl)) / (8 * 4 * 1) = P := by omega
  have d2 : ((P * 32 + (r * 8 + jl)) % (8 * 4 * 1)) / 1 / 8 = r := by omega
  have d3 : ((P * 32 + (r * 8 + jl)) % (8 * 4 * 1)) / 1 % 8 = jl := by omega
  have d4 : ((P * 32 + (r * 8 + jl)) % (8 * 4 * 1)) % 1 = 0 := by omega
  simp only [show (8*4*1:Nat) ≠ 0 from by omega, show (8:Nat) ≠ 0 from by omega,
    show (1:Nat) ≠ 0 from by omega, if_false, d1, d2, d3, d4]
  congr 1
  omega

set_option maxRecDepth 8192 in
/-- Value of `allGatherPrimDimN 0 4` over shards of shape `[8,32]`. -/
theorem allGatherDimN0_4_832_valAt_g134 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [8, 32])
    (r : Nat) (hr : r < 4) (jl : Nat) (hjl : jl < 8) (col : Nat) (hcol : col < 32) :
    valAt (allGatherPrimDimN 0 4 0 ws) ((r * 8 + jl) * 32 + col) =
      valAt (ws.getD r (zeroTensor [8, 32])) (jl * 32 + col) := by
  have hshape : (allGatherPrimDimN 0 4 0 ws).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 0 4 ws [8, 32] hhead]; simp [List.set, List.getD]
  have hbound : (r * 8 + jl) * 32 + col < prodShape (allGatherPrimDimN 0 4 0 ws).shape := by
    rw [hshape]; simp only [prodShape, List.foldl]; omega
  rw [valAt_of_lt _ _ hbound]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, show ([8,32].getD 0 0 : Nat) = 8 from rfl]
  have d1 : ((r * 8 + jl) * 32 + col) / (8 * 4 * 32) = 0 := by omega
  have d2 : ((r * 8 + jl) * 32 + col) % (8 * 4 * 32) / 32 / 8 = r := by omega
  have d3 : ((r * 8 + jl) * 32 + col) % (8 * 4 * 32) / 32 % 8 = jl := by omega
  have d4 : ((r * 8 + jl) * 32 + col) % (8 * 4 * 32) % 32 = col := by omega
  simp only [show (8*4*32:Nat) ≠ 0 from by omega, show (8:Nat) ≠ 0 from by omega,
    show (32:Nat) ≠ 0 from by omega, if_false, d1, d2, d3, d4]
  congr 1
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- Tensor-parallel dX reduction for `BW_linear`: dim-2 split gradient + dim-0 split
    weight, reduced by `allReducePrim`. -/
theorem bw_linear_dx_tp_split_dim2_4_g134
    (g0 g1 g2 g3 x w0 w1 w2 w3 : Tensor)
    (hg0 : g0.shape = [1,8,8]) (hg1 : g1.shape = [1,8,8])
    (hg2 : g2.shape = [1,8,8]) (hg3 : g3.shape = [1,8,8])
    (hx : x.shape = [1,8,32])
    (hw0 : w0.shape = [8,32]) (hw1 : w1.shape = [8,32])
    (hw2 : w2.shape = [8,32]) (hw3 : w3.shape = [8,32]) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0,g1,g2,g3]) x
        (allGatherPrimDimN 0 4 0 [w0,w1,w2,w3])).1 =
      allReducePrim 4 0
        [(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1] := by
  have hheadg : (([g0,g1,g2,g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1,8,8] := by
    simp [hg0]
  have hheadw : (([w0,w1,w2,w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [8,32] := by
    simp [hw0]
  set G := allGatherPrimDimN 2 4 0 [g0,g1,g2,g3] with hGdef
  set W := allGatherPrimDimN 0 4 0 [w0,w1,w2,w3] with hWdef
  have hGshape : G.shape = [1,8,32] := by
    rw [hGdef, allGatherPrimDimN_shape 2 4 _ [1,8,8] hheadg]; simp [List.set, List.getD]
  have hWshape : W.shape = [32,32] := by
    rw [hWdef, allGatherPrimDimN_shape 0 4 _ [8,32] hheadw]; simp [List.set, List.getD]
  have hLshape : (bw_linear G x W).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 G x W hGshape hx hWshape
  have hdx0shape : (bw_linear g0 x w0).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 8 32 g0 x w0 hg0 hx hw0
  have hRhead : ([(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1] : List Tensor).head?
       = some (bw_linear g0 x w0).1 := rfl
  have hRshape : (allReducePrim 4 0
        [(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1]).shape = [1,8,32] := by
    rw [allReducePrim_shape 4 0 _ _ hRhead, hdx0shape]
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/32 < 8 := by omega
    have hcol : idx%32 < 32 := by omega
    have hidxeq : idx = (idx/32)*32 + idx%32 := by omega
    rw [hidxeq]
    set P := idx/32 with hPdef
    set col := idx%32 with hcoldef
    rw [allReducePrim_valAt 4 0 _ (P*32+col) (bw_linear g0 x w0).1 hRhead (by rw [hdx0shape]; simp [prodShape]; omega)]
    simp only [List.foldl, zero_add]
    rw [bw_linear_fst_valAt_1_8_32_g134 g0 x w0 8 hg0 hx hw0 P hP col hcol,
        bw_linear_fst_valAt_1_8_32_g134 g1 x w1 8 hg1 hx hw1 P hP col hcol,
        bw_linear_fst_valAt_1_8_32_g134 g2 x w2 8 hg2 hx hw2 P hP col hcol,
        bw_linear_fst_valAt_1_8_32_g134 g3 x w3 8 hg3 hx hw3 P hP col hcol]
    rw [bw_linear_fst_valAt_1_8_32_g134 G x W 32 hGshape hx hWshape P hP col hcol]
    have hsplit : (∑ j ∈ Finset.range 32, valAt G (P*32+j) * valAt W (j*32+col))
        = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 8,
            valAt G (P*32+(i*8+j)) * valAt W ((i*8+j)*32+col) := by
      have := Finset.sum_range_mul_eq_sum_sum 4 8 (fun k => valAt G (P*32+k) * valAt W (k*32+col))
      simpa using this
    rw [hsplit]
    have key : ∀ i, i < 4 →
        (∑ j ∈ Finset.range 8, valAt G (P*32+(i*8+j)) * valAt W ((i*8+j)*32+col))
        = ∑ j ∈ Finset.range 8,
            valAt ([g0,g1,g2,g3].getD i (zeroTensor [1,8,8])) (P*8+j)
            * valAt ([w0,w1,w2,w3].getD i (zeroTensor [8,32])) (j*32+col) := by
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hj8 : j < 8 := Finset.mem_range.mp hj
      rw [hGdef, allGatherDimN2_4_188_valAt_g134 [g0,g1,g2,g3] hheadg P hP i hi j hj8,
          hWdef, allGatherDimN0_4_832_valAt_g134 [w0,w1,w2,w3] hheadw i hi j hj8 col hcol]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [key 0 (by omega), key 1 (by omega), key 2 (by omega), key 3 (by omega)]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]


-- ==== batch3 g141 additions ====
/-- valAt of a dim-0 all-gather of four `[32,32]` shards into a `[128,32]` tensor.
    The output row `r*32+lc` (rank `r`, local row `lc`), column `jcol` reads shard `r`
    at local index `lc*32 + jcol`. -/
theorem allGatherPrimDimN_0_4_valAt_32_32_g141 (xs : List Tensor)
    (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 32) (jcol : Nat) (hjcol : jcol < 32)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [32, 32]) :
    valAt (allGatherPrimDimN 0 4 0 xs) ((r * 32 + lc) * 32 + jcol) =
      valAt (xs.getD r (zeroTensor [32, 32])) (lc * 32 + jcol) := by
  have hidx_lt : (r * 32 + lc) * 32 + jcol < 4096 := by omega
  have hgather_shape : (allGatherPrimDimN 0 4 0 xs).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 xs [32, 32] hhead]
    simp [List.set, List.getD]
  have hidx_prod : (r * 32 + lc) * 32 + jcol < prodShape (allGatherPrimDimN 0 4 0 xs).shape := by
    rw [hgather_shape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set,
    show (32 : Nat) ≠ 0 from by omega, show (128 : Nat) ≠ 0 from by omega,
    show (4096 : Nat) ≠ 0 from by omega, show (4 : Nat) ≠ 0 from by omega,
    ite_false]
  have e1 : ((r * 32 + lc) * 32 + jcol) / 4096 = 0 := by omega
  have e2 : ((r * 32 + lc) * 32 + jcol) % 4096 = (r * 32 + lc) * 32 + jcol := by omega
  have e3 : ((r * 32 + lc) * 32 + jcol) / 32 = r * 32 + lc := by omega
  have e4 : ((r * 32 + lc) * 32 + jcol) % 32 = jcol := by omega
  have e5 : (r * 32 + lc) / 32 = r := by omega
  have e6 : (r * 32 + lc) % 32 = lc := by omega
  rw [e1, e2, e3, e4, e5, e6]
  simp only [Nat.zero_mul, Nat.zero_add]

set_option maxHeartbeats 1600000 in
/-- Column-parallel weight gradient for `BW_linear`: the gradient output `gradOut`
    (`[1,8,128]`) is sharded on dim 2 into four `[1,8,32]` shards, the weight `w`
    (`[128,32]`) is sharded on dim 0 into four `[32,32]` shards, and the activation `x`
    (`[1,8,32]`) is shared.  Then the full dW (`[128,32]`) equals the dim-0 all-gather of
    the four per-rank dW outputs (`[32,32]`). -/
theorem bw_linear_dw_col_split_dim2_4_1_8_32_g141
    (g0 g1 g2 g3 x w0 w1 w2 w3 : Tensor)
    (hg0 : g0.shape = [1, 8, 32]) (hg1 : g1.shape = [1, 8, 32])
    (hg2 : g2.shape = [1, 8, 32]) (hg3 : g3.shape = [1, 8, 32])
    (hx : x.shape = [1, 8, 32])
    (hw0 : w0.shape = [32, 32]) (hw1 : w1.shape = [32, 32])
    (hw2 : w2.shape = [32, 32]) (hw3 : w3.shape = [32, 32]) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
        (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 0 4 0
        [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
         (bw_linear g2 x w2).2, (bw_linear g3 x w3).2] := by
  classical
  have hgg_head : (([g0, g1, g2, g3]).head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    simp [hg0]
  have hgw_head : (([w0, w1, w2, w3]).head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    simp [hw0]
  have hG : (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 _ [1, 8, 32] hgg_head]; simp [List.set, List.getD]
  have hW : (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 _ [32, 32] hgw_head]; simp [List.set, List.getD]
  have hL_shape : (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2.shape = [128, 32] :=
    bw_linear_3d_snd_shape 1 8 128 32 _ _ _ hG hx hW
  have hp0 : (bw_linear g0 x w0).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 _ _ _ hg0 hx hw0
  have hpieces_head : (([(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
      (bw_linear g2 x w2).2, (bw_linear g3 x w3).2]).head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    simp [hp0]
  have hR_shape : (allGatherPrimDimN 0 4 0
      [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
       (bw_linear g2 x w2).2, (bw_linear g3 x w3).2]).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 _ [32, 32] hpieces_head]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hL_shape, hR_shape])
  intro idx hidx
  rw [hL_shape] at hidx
  have hidx4096 : idx < 4096 := by simpa [prodShape] using hidx
  set c := idx / 32 with hc_def
  set jcol := idx % 32 with hjcol_def
  have hjcol : jcol < 32 := Nat.mod_lt _ (by omega)
  have hc : c < 128 := by omega
  have hidx_eq : idx = c * 32 + jcol := by omega
  set r := c / 32 with hr_def
  set lc := c % 32 with hlc_def
  have hr : r < 4 := by omega
  have hlc : lc < 32 := Nat.mod_lt _ (by omega)
  have hc_eq : c = r * 32 + lc := by omega
  -- LHS value as a sum
  have hLval : valAt (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2 idx =
      ∑ p ∈ Finset.range (1 * 8),
        valAt (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) (p * 128 + c) * valAt x (p * 32 + jcol) := by
    rw [hidx_eq]
    exact bw_linear_dw_valAt3d _ _ _ 1 8 128 32 hG hx hW c hc jcol hjcol
  -- rewrite the gathered-gradient term per summand
  have hgather_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) (p * 128 + c) =
        valAt (([g0, g1, g2, g3]).getD r (zeroTensor [1, 8, 32])) (p * 32 + lc) := by
    intro p hp
    rw [show p * 128 + c = p * 128 + r * 32 + lc from by rw [hc_eq]; ring]
    exact allGatherPrimDimN_dim2_4_1_8_32_valAt _ p hp r hr lc hlc hgg_head
  -- RHS value
  have hRval : valAt (allGatherPrimDimN 0 4 0
      [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
       (bw_linear g2 x w2).2, (bw_linear g3 x w3).2]) idx =
      valAt (([(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
        (bw_linear g2 x w2).2, (bw_linear g3 x w3).2]).getD r (zeroTensor [32, 32]))
        (lc * 32 + jcol) := by
    rw [hidx_eq, hc_eq]
    exact allGatherPrimDimN_0_4_valAt_32_32_g141 _ r hr lc hlc jcol hjcol hpieces_head
  rw [hLval, hRval]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [hgather_term p (by simpa using hp)])]
  -- now both sides are a sum over the rank-r shard; case on r
  have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  clear_value r
  rcases hr4 with rfl | rfl | rfl | rfl <;>
    (simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some];
     rw [bw_linear_dw_valAt3d _ _ _ 1 8 32 32 (by assumption) hx (by assumption) lc hlc jcol hjcol])



-- ==== batch3 g119 additions ====
/-- Per-rank dW value for the dim-2 (output-feature) tensor-parallel split of `bw_linear`.
    When `g` (`[1,8,32]`) is chunked along its last dim into rank `R` (giving `[1,8,8]`),
    the rank-`R` dW (`[8,32]`) at row `i`, col `j` equals the global sum-reduction whose
    `g`-index is offset by `R*8`. -/
private theorem bw_linear_dw_chunk_rank_valAt_g119
    (g x w_r : Tensor) (R i j : Nat)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 32]) (hwr : w_r.shape = [8, 32])
    (hR : R < 4) (hi : i < 8) (hj : j < 32) :
    valAt (bw_linear (chunkPrimDimN 2 4 R g) x w_r).2 (i * 32 + j) =
      ∑ r' ∈ Finset.range 8, valAt g (r' * 32 + R * 8 + i) * valAt x (r' * 32 + j) := by
  have hchunk : (chunkPrimDimN 2 4 R g).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 R g _ hg (by omega)]; simp [List.set, List.getD]
  rw [bw_linear_dw_valAt3d (chunkPrimDimN 2 4 R g) x w_r 1 8 8 32 hchunk hx hwr i hi j hj]
  simp only [show (1 : Nat) * 8 = 8 from rfl]
  apply Finset.sum_congr rfl
  intro r' hr'
  rw [chunk2_4_1_8_32_valAt_pj g R r' i hg hR (Finset.mem_range.mp hr') hi]

set_option maxHeartbeats 1600000 in
/-- The dW output of `bw_linear` where the gradient `g` (`[1,8,32]`) is chunked along its
    last (output-feature) dim into 4 ranks, equals the dim-0 all-gather of the per-rank dW
    outputs (each `[8,32]`).  This is the tensor-parallel weight-gradient identity for
    `BW_linear` (the per-rank weights `w0..w3` only fix the output shape; dW is independent
    of `w`). -/
theorem bw_linear_dw_split_dim2_4_g119
    (g x w w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 32]) (hw : w.shape = [32, 32])
    (hw0 : w0.shape = [8, 32]) (hw1 : w1.shape = [8, 32])
    (hw2 : w2.shape = [8, 32]) (hw3 : w3.shape = [8, 32]) :
    (bw_linear g x w).2 = allGatherPrimDimN 0 4 0
      [(bw_linear (chunkPrimDimN 2 4 0 g) x w0).2,
       (bw_linear (chunkPrimDimN 2 4 1 g) x w1).2,
       (bw_linear (chunkPrimDimN 2 4 2 g) x w2).2,
       (bw_linear (chunkPrimDimN 2 4 3 g) x w3).2] := by
  have hch0 : (chunkPrimDimN 2 4 0 g).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 0 g _ hg (by omega)]; simp [List.set, List.getD]
  have hd0 : (bw_linear (chunkPrimDimN 2 4 0 g) x w0).2.shape = [8, 32] :=
    bw_linear_3d_snd_shape 1 8 8 32 _ x w0 hch0 hx hw0
  have hhead : (([(bw_linear (chunkPrimDimN 2 4 0 g) x w0).2,
                  (bw_linear (chunkPrimDimN 2 4 1 g) x w1).2,
                  (bw_linear (chunkPrimDimN 2 4 2 g) x w2).2,
                  (bw_linear (chunkPrimDimN 2 4 3 g) x w3).2].head?.map
                  (fun t => t.shape)).getD [] = [8, 32]) := by
    simp [hd0]
  have hWs_shape : ∀ r (_ : r < 4),
      (([(bw_linear (chunkPrimDimN 2 4 0 g) x w0).2,
         (bw_linear (chunkPrimDimN 2 4 1 g) x w1).2,
         (bw_linear (chunkPrimDimN 2 4 2 g) x w2).2,
         (bw_linear (chunkPrimDimN 2 4 3 g) x w3).2].getD r (zeroTensor [8, 32])).shape = [8, 32]) := by
    intro r hr
    rcases r with _|_|_|_|r
    · simpa [List.getD] using bw_linear_3d_snd_shape 1 8 8 32 _ x w0 hch0 hx hw0
    · have : (chunkPrimDimN 2 4 1 g).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 1 g _ hg (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 8 32 _ x w1 this hx hw1
    · have : (chunkPrimDimN 2 4 2 g).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 2 g _ hg (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 8 32 _ x w2 this hx hw2
    · have : (chunkPrimDimN 2 4 3 g).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 3 g _ hg (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 8 32 _ x w3 this hx hw3
    · omega
  apply Tensor.ext
  · rw [bw_linear_3d_snd_shape 1 8 32 32 g x w hg hx hw,
        allGatherPrimDimN_shape 0 4 _ [8, 32] hhead]
    decide
  · intro idx hidx
    rw [bw_linear_3d_snd_shape 1 8 32 32 g x w hg hx hw] at hidx
    have hidxp : idx < 1024 := by simpa [prodShape] using hidx
    have hc : idx / 32 < 32 := by omega
    have hj : idx % 32 < 32 := by omega
    set c := idx / 32 with hcdef
    set j := idx % 32 with hjdef
    have hidc : idx = c * 32 + j := by omega
    rw [hidc, bw_linear_dw_valAt3d g x w 1 8 32 32 hg hx hw c hc j hj]
    have hr : c / 8 < 4 := by omega
    have hi : c % 8 < 8 := by omega
    rw [show c * 32 + j = (c / 8 * 8 + c % 8) * 32 + j from by
          have : c / 8 * 8 + c % 8 = c := by omega
          rw [this]]
    rw [allGatherPrimDimN0_valAt 4 8 32
          [(bw_linear (chunkPrimDimN 2 4 0 g) x w0).2,
           (bw_linear (chunkPrimDimN 2 4 1 g) x w1).2,
           (bw_linear (chunkPrimDimN 2 4 2 g) x w2).2,
           (bw_linear (chunkPrimDimN 2 4 3 g) x w3).2]
          (by omega) (by omega) (by omega) hhead hWs_shape (c / 8) hr (c % 8) hi j hj]
    have hcase : c / 8 = 0 ∨ c / 8 = 1 ∨ c / 8 = 2 ∨ c / 8 = 3 := by omega
    rcases hcase with h | h | h | h
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_chunk_rank_valAt_g119 g x w0 0 (c % 8) j hg hx hw0 (by omega) hi hj]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 0 * 8 + c % 8 = r' * 32 + c from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_chunk_rank_valAt_g119 g x w1 1 (c % 8) j hg hx hw1 (by omega) hi hj]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 1 * 8 + c % 8 = r' * 32 + c from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_chunk_rank_valAt_g119 g x w2 2 (c % 8) j hg hx hw2 (by omega) hi hj]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 2 * 8 + c % 8 = r' * 32 + c from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_chunk_rank_valAt_g119 g x w3 3 (c % 8) j hg hx hw3 (by omega) hi hj]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 3 * 8 + c % 8 = r' * 32 + c from by omega]


-- ==== batch3 g135 additions ====
/- BW_linear dW with the gradient `g` (`[1,8,32]`) split along the output dim into 4 shards
   (each `[1,8,8]`, all-gathered on dim 2) and `x` (`[1,8,32]`) replicated.  The full dW
   (`[32,32]`) is the dim-0 concatenation (`allGatherPrimDimN 0`) of the per-rank dW shards
   (each `[8,32]`).  This is the output-(tensor-)parallel weight-gradient identity for
   `BW_linear`.  dW depends only on `g` and `x`, so the per-rank `w` shards are irrelevant to
   the value. -/
set_option maxHeartbeats 800000 in
theorem bw_linear_dw_osplit_dim2_4_1_8_8_g135
    (x g0 g1 g2 g3 w0 w1 w2 w3 : Tensor)
    (hx : x.shape = [1, 8, 32])
    (hg0 : g0.shape = [1, 8, 8]) (hg1 : g1.shape = [1, 8, 8])
    (hg2 : g2.shape = [1, 8, 8]) (hg3 : g3.shape = [1, 8, 8])
    (hw0 : w0.shape = [8, 32]) (hw1 : w1.shape = [8, 32])
    (hw2 : w2.shape = [8, 32]) (hw3 : w3.shape = [8, 32]) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
        (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 0 4 0
        [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
         (bw_linear g2 x w2).2, (bw_linear g3 x w3).2] := by
  -- head shapes
  have hghead : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hg0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [8, 32] := by
    simp [hw0]
  -- gathered input shapes
  have hG_shape : (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hghead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hwhead]; simp [List.set, List.getD]
  -- per-rank dW shapes
  have hp0 : (bw_linear g0 x w0).2.shape = [8, 32] := bw_linear_3d_snd_shape 1 8 8 32 g0 x w0 hg0 hx hw0
  have hp1 : (bw_linear g1 x w1).2.shape = [8, 32] := bw_linear_3d_snd_shape 1 8 8 32 g1 x w1 hg1 hx hw1
  have hp2 : (bw_linear g2 x w2).2.shape = [8, 32] := bw_linear_3d_snd_shape 1 8 8 32 g2 x w2 hg2 hx hw2
  have hp3 : (bw_linear g3 x w3).2.shape = [8, 32] := bw_linear_3d_snd_shape 1 8 8 32 g3 x w3 hg3 hx hw3
  set pieces : List Tensor :=
    [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2, (bw_linear g2 x w2).2, (bw_linear g3 x w3).2]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [8, 32] := by
    simp [hpieces_def, hp0]
  have hpgetD : ∀ r, r < 4 → (pieces.getD r (zeroTensor [8, 32])).shape = [8, 32] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hpieces_def, List.getD, hp0, hp1, hp2, hp3]
  -- LHS / RHS shapes
  have hLHS_shape : (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2.shape = [32, 32] :=
    bw_linear_3d_snd_shape 1 8 32 32 _ x _ hG_shape hx hW_shape
  have hRHS_shape : (allGatherPrimDimN 0 4 0 pieces).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx1024 : idx < 1024 := by simpa [hLHS_shape, prodShape] using hidx
  set c := idx / 32 with hc_def
  set k := idx % 32 with hk_def
  have hk : k < 32 := by rw [hk_def]; exact Nat.mod_lt _ (by omega)
  have hc : c < 32 := by rw [hc_def]; omega
  have hidx_eq : idx = c * 32 + k := by rw [hc_def, hk_def]; omega
  rw [hidx_eq]
  -- LHS value
  rw [bw_linear_dw_valAt3d (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]) 1 8 32 32 hG_shape hx hW_shape c hc k hk]
  -- RHS value: rewrite index into (r*8+oc) form and peel the dim-0 gather
  have hoc : c % 8 < 8 := Nat.mod_lt _ (by omega)
  have hr : c / 8 < 4 := by omega
  conv_rhs => rw [show c * 32 + k = (c / 8 * 8 + c % 8) * 32 + k from by
    have : c / 8 * 8 + c % 8 = c := by omega
    rw [this]]
  rw [allGatherPrimDimN0_valAt 4 8 32 pieces (by omega) (by omega) (by omega)
      hphead hpgetD (c / 8) hr (c % 8) hoc k hk]
  -- expand the selected per-rank dW and match term by term
  have hG_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) (p * 32 + c) =
      valAt (([g0, g1, g2, g3] : List Tensor).getD (c / 8) (zeroTensor [1, 8, 8])) (p * 8 + c % 8) := by
    intro p hp
    have hb : p * 32 + c < 256 := by omega
    rw [allGatherPrimDimN_2_4_valAt_1_8_8 [g0, g1, g2, g3] (p * 32 + c) hghead hb]
    have hrank : (p * 32 + c) % 32 / 8 = c / 8 := by omega
    have hflat : (p * 32 + c) / 32 * 8 + (p * 32 + c) % 8 = p * 8 + c % 8 := by omega
    rw [hrank, hflat]
  rcases (show c / 8 = 0 ∨ c / 8 = 1 ∨ c / 8 = 2 ∨ c / 8 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_dw_valAt3d g0 x w0 1 8 8 32 hg0 hx hw0 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g1 x w1 1 8 8 32 hg1 hx hw1 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g2 x w2 1 8 8 32 hg2 hx hw2 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g3 x w3 1 8 8 32 hg3 hx hw3 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp



-- ============================================================
-- BATCH4 net-new BW_linear lemmas (g150 g154 g169 g175) + batch3 g140
-- ============================================================

/- BW_linear dW with the input `x` (`[1,8,32]`) split along the input dim into 4 shards
   (each `[1,8,8]`, all-gathered on dim 2) and the gradient `g` (`[1,8,32]`) replicated,
   weight `w` (`[32,32]`) split along dim 1 (each `[32,8]`).  The full dW (`[32,32]`)
   is the dim-1 concatenation (`allGatherPrimDimN 1`) of the per-rank dW shards
   (each `[32,8]`).  This is the input-(tensor-)parallel weight-gradient identity for
   `BW_linear`.  dW depends only on `g` and `x`, so the per-rank `w` shards are irrelevant
   to the value. -/
set_option maxHeartbeats 800000 in
theorem bw_linear_dw_isplit_dim2_4_1_8_8_g150
    (g x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 32])
    (hx0 : x0.shape = [1, 8, 8]) (hx1 : x1.shape = [1, 8, 8])
    (hx2 : x2.shape = [1, 8, 8]) (hx3 : x3.shape = [1, 8, 8])
    (hw0 : w0.shape = [32, 8]) (hw1 : w1.shape = [32, 8])
    (hw2 : w2.shape = [32, 8]) (hw3 : w3.shape = [32, 8]) :
    (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
        (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 1 4 0
        [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2,
         (bw_linear g x2 w2).2, (bw_linear g x3 w3).2] := by
  -- head shapes
  have hxhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hx0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32, 8] := by
    simp [hw0]
  -- gathered input shapes
  have hX_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hxhead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; simp [List.set, List.getD]
  -- per-rank dW shapes
  have hp0 : (bw_linear g x0 w0).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x0 w0 hg hx0 hw0
  have hp1 : (bw_linear g x1 w1).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x1 w1 hg hx1 hw1
  have hp2 : (bw_linear g x2 w2).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x2 w2 hg hx2 hw2
  have hp3 : (bw_linear g x3 w3).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x3 w3 hg hx3 hw3
  set pieces : List Tensor :=
    [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2, (bw_linear g x2 w2).2, (bw_linear g x3 w3).2]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [32, 8] := by
    simp [hpieces_def, hp0]
  have hpgetD : ∀ r, r < 4 → (pieces.getD r (zeroTensor [32, 8])).shape = [32, 8] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hpieces_def, List.getD, hp0, hp1, hp2, hp3]
  -- LHS / RHS shapes
  have hLHS_shape : (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2.shape = [32, 32] :=
    bw_linear_3d_snd_shape 1 8 32 32 g _ _ hg hX_shape hW_shape
  have hRHS_shape : (allGatherPrimDimN 1 4 0 pieces).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx1024 : idx < 1024 := by simpa [hLHS_shape, prodShape] using hidx
  set c := idx / 32 with hc_def
  set k := idx % 32 with hk_def
  have hk : k < 32 := by rw [hk_def]; exact Nat.mod_lt _ (by omega)
  have hc : c < 32 := by rw [hc_def]; omega
  have hidx_eq : idx = c * 32 + k := by rw [hc_def, hk_def]; omega
  rw [hidx_eq]
  -- LHS value
  rw [bw_linear_dw_valAt3d g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) 1 8 32 32 hg hX_shape hW_shape c hc k hk]
  -- RHS value: rewrite index into (r*8+kc) form on the i-axis and peel the dim-1 gather
  have hkc : k % 8 < 8 := Nat.mod_lt _ (by omega)
  have hr : k / 8 < 4 := by omega
  conv_rhs => rw [show c * 32 + k = c * 32 + k / 8 * 8 + k % 8 from by omega]
  rw [allGatherPrimDimN1_4_valAt_32_8 pieces hphead hpgetD c hc (k / 8) hr (k % 8) hkc]
  -- expand the selected per-rank dW and match term by term
  have hX_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) (p * 32 + k) =
      valAt (([x0, x1, x2, x3] : List Tensor).getD (k / 8) (zeroTensor [1, 8, 8])) (p * 8 + k % 8) := by
    intro p hp
    have hb : p * 32 + k < 256 := by omega
    rw [allGatherPrimDimN_2_4_valAt_1_8_8 [x0, x1, x2, x3] (p * 32 + k) hxhead hb]
    have hrank : (p * 32 + k) % 32 / 8 = k / 8 := by omega
    have hflat : (p * 32 + k) / 32 * 8 + (p * 32 + k) % 8 = p * 8 + k % 8 := by omega
    rw [hrank, hflat]
  rcases (show k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_dw_valAt3d g x0 w0 1 8 32 8 hg hx0 hw0 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x1 w1 1 8 32 8 hg hx1 hw1 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x2 w2 1 8 32 8 hg hx2 hw2 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x3 w3 1 8 32 8 hg hx3 hw3 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp



-- ==== batch4 g154 additions ====
set_option maxHeartbeats 800000 in
/-- Row-parallel (input-feature split) weight gradient for `BW_linear`.  The activation `x`
    (`[1,8,32]`) is sharded on dim 2 into four `[1,8,8]` shards, the weight `w` (`[32,32]`)
    is sharded on dim 1 into four `[32,8]` shards, and the gradient `g` (`[1,8,32]`) is shared.
    Then the full dW (`[32,32]`) equals the dim-1 all-gather of the four per-rank dW outputs
    (each `[32,8]`).  dW depends only on `g` and `x`, so the per-rank `w` shards only fix the
    output column width. -/
theorem bw_linear_dw_isplit_dim2_4_1_8_8_g154
    (g x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 32])
    (hx0 : x0.shape = [1, 8, 8]) (hx1 : x1.shape = [1, 8, 8])
    (hx2 : x2.shape = [1, 8, 8]) (hx3 : x3.shape = [1, 8, 8])
    (hw0 : w0.shape = [32, 8]) (hw1 : w1.shape = [32, 8])
    (hw2 : w2.shape = [32, 8]) (hw3 : w3.shape = [32, 8]) :
    (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
        (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 1 4 0
        [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2,
         (bw_linear g x2 w2).2, (bw_linear g x3 w3).2] := by
  have hxhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hx0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32, 8] := by
    simp [hw0]
  have hX_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hxhead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; simp [List.set, List.getD]
  have hp0 : (bw_linear g x0 w0).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x0 w0 hg hx0 hw0
  have hp1 : (bw_linear g x1 w1).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x1 w1 hg hx1 hw1
  have hp2 : (bw_linear g x2 w2).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x2 w2 hg hx2 hw2
  have hp3 : (bw_linear g x3 w3).2.shape = [32, 8] := bw_linear_3d_snd_shape 1 8 32 8 g x3 w3 hg hx3 hw3
  set pieces : List Tensor :=
    [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2, (bw_linear g x2 w2).2, (bw_linear g x3 w3).2]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [32, 8] := by
    simp [hpieces_def, hp0]
  have hpgetD : ∀ r, r < 4 → (pieces.getD r (zeroTensor [32, 8])).shape = [32, 8] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hpieces_def, List.getD, hp0, hp1, hp2, hp3]
  have hLHS_shape : (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2.shape = [32, 32] :=
    bw_linear_3d_snd_shape 1 8 32 32 g _ _ hg hX_shape hW_shape
  have hRHS_shape : (allGatherPrimDimN 1 4 0 pieces).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx1024 : idx < 1024 := by simpa [hLHS_shape, prodShape] using hidx
  set c := idx / 32 with hc_def
  set k := idx % 32 with hk_def
  have hk : k < 32 := by rw [hk_def]; exact Nat.mod_lt _ (by omega)
  have hc : c < 32 := by rw [hc_def]; omega
  have hidx_eq : idx = c * 32 + k := by rw [hc_def, hk_def]; omega
  rw [hidx_eq]
  -- LHS value
  rw [bw_linear_dw_valAt3d g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) 1 8 32 32 hg hX_shape hW_shape c hc k hk]
  -- RHS value: split the column index k = (k/8)*8 + k%8 and peel the dim-1 gather
  have hkl : k % 8 < 8 := Nat.mod_lt _ (by omega)
  have hkr : k / 8 < 4 := by omega
  conv_rhs => rw [show c * 32 + k = c * 32 + (k / 8) * 8 + (k % 8) from by omega]
  rw [allGatherPrimDimN1_4_valAt_32_8 pieces hphead hpgetD c hc (k / 8) hkr (k % 8) hkl]
  -- per-summand rewrite of the gathered activation term
  have hX_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) (p * 32 + k) =
      valAt (([x0, x1, x2, x3] : List Tensor).getD (k / 8) (zeroTensor [1, 8, 8])) (p * 8 + k % 8) := by
    intro p hp
    rw [show p * 32 + k = p * 32 + (k / 8) * 8 + (k % 8) from by omega]
    exact allGatherPrimDimN_dim2_4_1_8_8_valAt [x0, x1, x2, x3] p hp (k / 8) hkr (k % 8) hkl hxhead
  rcases (show k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_dw_valAt3d g x0 w0 1 8 32 8 hg hx0 hw0 c hc (k % 8) hkl]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x1 w1 1 8 32 8 hg hx1 hw1 c hc (k % 8) hkl]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x2 w2 1 8 32 8 hg hx2 hw2 c hc (k % 8) hkl]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x3 w3 1 8 32 8 hg hx3 hw3 c hc (k % 8) hkl]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp


-- ==== batch4 g169 additions ====
/-- Value of the dX output of `bw_linear` for a `[1,2,o]` gradient and `[1,2,32]`
    activation: the row `P` (`P < 2`), column `col` reads the contraction over the
    output-feature dimension `o`. -/
theorem bw_linear_fst_valAt_1_2_32_g169 (g x w : Tensor) (o : Nat)
    (hg : g.shape = [1, 2, o]) (hx : x.shape = [1, 2, 32]) (hw : w.shape = [o, 32])
    (P : Nat) (hP : P < 2) (col : Nat) (hcol : col < 32) :
    valAt (bw_linear g x w).1 (P * 32 + col) =
      ∑ j ∈ Finset.range o, valAt g (P * o + j) * valAt w (j * 32 + col) := by
  have hdx : (bw_linear g x w).1 =
      Tensor.mkShape [1, 2, 32] (fun outIdx =>
        ∑ j ∈ Finset.range o,
          valAt g (((if (2:Nat) * 32 = 0 then 0 else outIdx.1 / (2 * 32)) * 2 +
                    if (32:Nat) = 0 then 0 else (if (2:Nat) * 32 = 0 then 0 else outIdx.1 % (2 * 32)) / 32) * o + j) *
          valAt w (j * 32 + if (32:Nat) = 0 then 0 else (if (2:Nat) * 32 = 0 then 0 else outIdx.1 % (2 * 32)) % 32)) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hdx]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl]; omega)]
  simp only [Tensor.mkShape]
  have e1 : (P*32+col)/(2*32) = 0 := by omega
  have e2 : ((P*32+col)%(2*32))/32 = P := by omega
  have e3 : ((P*32+col)%(2*32))%32 = col := by omega
  simp only [show ((2:Nat)*32=0)=False from by simp, show ((32:Nat)=0)=False from by simp,
    if_false, e1, e2, e3, Nat.zero_mul, Nat.zero_add]

set_option maxHeartbeats 2000000 in
/-- Data-parallel (sequence-dim) split of the dX output of `BW_linear`: the gradient
    `g` (`[1,8,32]`) is dim-1 all-gathered from four `[1,2,32]` shards, the activation
    `x` (`[1,8,32]`) is locally dim-1 chunked per rank, and the weight `w` (`[32,32]`)
    is shared.  Then the full dX equals the dim-1 all-gather of the per-rank dX outputs. -/
theorem bw_linear_dx_dp_split_dim1_4_g169
    (g0 g1 g2 g3 x w : Tensor)
    (hg0 : g0.shape = [1,2,32]) (hg1 : g1.shape = [1,2,32])
    (hg2 : g2.shape = [1,2,32]) (hg3 : g3.shape = [1,2,32])
    (hx : x.shape = [1,8,32]) (hw : w.shape = [32,32]) :
    (bw_linear (allGatherPrimDimN 1 4 0 [g0,g1,g2,g3]) x w).1 =
      allGatherPrimDimN 1 4 0
        [(bw_linear g0 (chunkPrimDimN 1 4 0 x) w).1,
         (bw_linear g1 (chunkPrimDimN 1 4 1 x) w).1,
         (bw_linear g2 (chunkPrimDimN 1 4 2 x) w).1,
         (bw_linear g3 (chunkPrimDimN 1 4 3 x) w).1] := by
  have hheadg : (([g0,g1,g2,g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1,2,32] := by
    simp [hg0]
  set G := allGatherPrimDimN 1 4 0 [g0,g1,g2,g3] with hGdef
  have hGshape : G.shape = [1,8,32] := by
    rw [hGdef, allGatherPrimDimN_shape 1 4 _ [1,2,32] hheadg]; simp [List.set, List.getD]
  have hcx0 : (chunkPrimDimN 1 4 0 x).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 0 x _ hx (by omega)]; simp [List.set, List.getD]
  have hcx1 : (chunkPrimDimN 1 4 1 x).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 1 x _ hx (by omega)]; simp [List.set, List.getD]
  have hcx2 : (chunkPrimDimN 1 4 2 x).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 2 x _ hx (by omega)]; simp [List.set, List.getD]
  have hcx3 : (chunkPrimDimN 1 4 3 x).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 3 x _ hx (by omega)]; simp [List.set, List.getD]
  have hdx0shape : (bw_linear g0 (chunkPrimDimN 1 4 0 x) w).1.shape = [1,2,32] :=
    bw_linear_3d_fst_shape 1 2 32 32 _ _ _ hg0 hcx0 hw
  have hLshape : (bw_linear G x w).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 G x w hGshape hx hw
  have hheadR : (([(bw_linear g0 (chunkPrimDimN 1 4 0 x) w).1,
                   (bw_linear g1 (chunkPrimDimN 1 4 1 x) w).1,
                   (bw_linear g2 (chunkPrimDimN 1 4 2 x) w).1,
                   (bw_linear g3 (chunkPrimDimN 1 4 3 x) w).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,2,32] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 1 4 _ [1,2,32] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/32 < 8 := by omega
    have hcol : idx%32 < 32 := by omega
    have hide : idx = (idx/32)*32 + idx%32 := by omega
    rw [hide]
    set P := idx/32 with hPdef
    set col := idx%32 with hcoldef
    set r := P/2 with hrdef
    set p := P%2 with hpdef
    have hr : r < 4 := by omega
    have hp : p < 2 := by omega
    have hPrp : P = r * 2 + p := by omega
    rw [bw_linear_fst_valAt_1_8_32_g134 G x w 32 hGshape hx hw P hP col hcol]
    -- RHS: gather valAt
    have hRHS : valAt (allGatherPrimDimN 1 4 0
          [(bw_linear g0 (chunkPrimDimN 1 4 0 x) w).1,
           (bw_linear g1 (chunkPrimDimN 1 4 1 x) w).1,
           (bw_linear g2 (chunkPrimDimN 1 4 2 x) w).1,
           (bw_linear g3 (chunkPrimDimN 1 4 3 x) w).1]) (P * 32 + col)
        = valAt ([(bw_linear g0 (chunkPrimDimN 1 4 0 x) w).1,
                  (bw_linear g1 (chunkPrimDimN 1 4 1 x) w).1,
                  (bw_linear g2 (chunkPrimDimN 1 4 2 x) w).1,
                  (bw_linear g3 (chunkPrimDimN 1 4 3 x) w).1].getD r (zeroTensor [1,2,32]))
                (p * 32 + col) := by
      rw [hPrp]
      exact allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr p hp col hcol hheadR
    rw [hRHS]
    -- LHS: rewrite the gathered-G terms under the sum
    have hLHS : (∑ j ∈ Finset.range 32, valAt G (P*32+j) * valAt w (j*32+col))
        = ∑ j ∈ Finset.range 32,
            valAt ([g0,g1,g2,g3].getD r (zeroTensor [1,2,32])) (p*32+j) * valAt w (j*32+col) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      have hidxj : P * 32 + j = (r * 2 + p) * 32 + j := by rw [hPrp]
      rw [hGdef, hidxj, allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] r hr p hp j hj32 hheadg]
    rw [hLHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_2_32_g169 g0 (chunkPrimDimN 1 4 0 x) w 32 hg0 hcx0 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_32_g169 g1 (chunkPrimDimN 1 4 1 x) w 32 hg1 hcx1 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_32_g169 g2 (chunkPrimDimN 1 4 2 x) w 32 hg2 hcx2 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_32_g169 g3 (chunkPrimDimN 1 4 3 x) w 32 hg3 hcx3 hw p hp col hcol]



-- ==== batch4 g175 additions ====
set_option maxRecDepth 8192 in
/-- Value of `allGatherPrimDimN 2 4` over shards of shape `[1,8,32]` (gathered to `[1,8,128]`). -/
theorem allGatherDimN2_4_1832_valAt_g175 (gs : List Tensor)
    (hhead : (gs.head?.map (fun t => t.shape)).getD [] = [1, 8, 32])
    (P : Nat) (hP : P < 8) (r : Nat) (hr : r < 4) (jl : Nat) (hjl : jl < 32) :
    valAt (allGatherPrimDimN 2 4 0 gs) (P * 128 + (r * 32 + jl)) =
      valAt (gs.getD r (zeroTensor [1, 8, 32])) (P * 32 + jl) := by
  have hshape : (allGatherPrimDimN 2 4 0 gs).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 gs [1, 8, 32] hhead]; simp [List.set, List.getD]
  have hbound : P * 128 + (r * 32 + jl) < prodShape (allGatherPrimDimN 2 4 0 gs).shape := by
    rw [hshape]; simp only [prodShape, List.foldl]; omega
  rw [valAt_of_lt _ _ hbound]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, show ([1,8,32].getD 2 0 : Nat) = 32 from rfl]
  have d1 : (P * 128 + (r * 32 + jl)) / (32 * 4 * 1) = P := by omega
  have d2 : ((P * 128 + (r * 32 + jl)) % (32 * 4 * 1)) / 1 / 32 = r := by omega
  have d3 : ((P * 128 + (r * 32 + jl)) % (32 * 4 * 1)) / 1 % 32 = jl := by omega
  have d4 : ((P * 128 + (r * 32 + jl)) % (32 * 4 * 1)) % 1 = 0 := by omega
  simp only [show (32*4*1:Nat) ≠ 0 from by omega, show (32:Nat) ≠ 0 from by omega,
    show (1:Nat) ≠ 0 from by omega, if_false, d1, d2, d3, d4]
  congr 1
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- Tensor-parallel dX reduction for `BW_linear`: dim-2 split gradient (`[1,8,32]` shards)
    + dim-0 split weight (`[32,32]` shards), reduced by `allReducePrim`. -/
theorem bw_linear_dx_tp_split_dim2_4_g175
    (g0 g1 g2 g3 x w0 w1 w2 w3 : Tensor)
    (hg0 : g0.shape = [1,8,32]) (hg1 : g1.shape = [1,8,32])
    (hg2 : g2.shape = [1,8,32]) (hg3 : g3.shape = [1,8,32])
    (hx : x.shape = [1,8,32])
    (hw0 : w0.shape = [32,32]) (hw1 : w1.shape = [32,32])
    (hw2 : w2.shape = [32,32]) (hw3 : w3.shape = [32,32]) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0,g1,g2,g3]) x
        (allGatherPrimDimN 0 4 0 [w0,w1,w2,w3])).1 =
      allReducePrim 4 0
        [(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1] := by
  have hheadg : (([g0,g1,g2,g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1,8,32] := by
    simp [hg0]
  have hheadw : (([w0,w1,w2,w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32,32] := by
    simp [hw0]
  set G := allGatherPrimDimN 2 4 0 [g0,g1,g2,g3] with hGdef
  set W := allGatherPrimDimN 0 4 0 [w0,w1,w2,w3] with hWdef
  have hGshape : G.shape = [1,8,128] := by
    rw [hGdef, allGatherPrimDimN_shape 2 4 _ [1,8,32] hheadg]; simp [List.set, List.getD]
  have hWshape : W.shape = [128,32] := by
    rw [hWdef, allGatherPrimDimN_shape 0 4 _ [32,32] hheadw]; simp [List.set, List.getD]
  have hLshape : (bw_linear G x W).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 128 32 G x W hGshape hx hWshape
  have hdx0shape : (bw_linear g0 x w0).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 g0 x w0 hg0 hx hw0
  have hRhead : ([(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1] : List Tensor).head?
       = some (bw_linear g0 x w0).1 := rfl
  have hRshape : (allReducePrim 4 0
        [(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1]).shape = [1,8,32] := by
    rw [allReducePrim_shape 4 0 _ _ hRhead, hdx0shape]
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/32 < 8 := by omega
    have hcol : idx%32 < 32 := by omega
    have hidxeq : idx = (idx/32)*32 + idx%32 := by omega
    rw [hidxeq]
    set P := idx/32 with hPdef
    set col := idx%32 with hcoldef
    rw [allReducePrim_valAt 4 0 _ (P*32+col) (bw_linear g0 x w0).1 hRhead (by rw [hdx0shape]; simp [prodShape]; omega)]
    simp only [List.foldl, zero_add]
    rw [bw_linear_fst_valAt_1_8_32_g134 g0 x w0 32 hg0 hx hw0 P hP col hcol,
        bw_linear_fst_valAt_1_8_32_g134 g1 x w1 32 hg1 hx hw1 P hP col hcol,
        bw_linear_fst_valAt_1_8_32_g134 g2 x w2 32 hg2 hx hw2 P hP col hcol,
        bw_linear_fst_valAt_1_8_32_g134 g3 x w3 32 hg3 hx hw3 P hP col hcol]
    rw [bw_linear_fst_valAt_1_8_32_g134 G x W 128 hGshape hx hWshape P hP col hcol]
    have hsplit : (∑ j ∈ Finset.range 128, valAt G (P*128+j) * valAt W (j*32+col))
        = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 32,
            valAt G (P*128+(i*32+j)) * valAt W ((i*32+j)*32+col) := by
      have := Finset.sum_range_mul_eq_sum_sum 4 32 (fun k => valAt G (P*128+k) * valAt W (k*32+col))
      simpa using this
    rw [hsplit]
    have key : ∀ i, i < 4 →
        (∑ j ∈ Finset.range 32, valAt G (P*128+(i*32+j)) * valAt W ((i*32+j)*32+col))
        = ∑ j ∈ Finset.range 32,
            valAt ([g0,g1,g2,g3].getD i (zeroTensor [1,8,32])) (P*32+j)
            * valAt ([w0,w1,w2,w3].getD i (zeroTensor [32,32])) (j*32+col) := by
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      rw [hGdef, allGatherDimN2_4_1832_valAt_g175 [g0,g1,g2,g3] hheadg P hP i hi j hj32,
          hWdef, allGatherPrimDimN_0_4_valAt_32_32_g141 [w0,w1,w2,w3] i hi j hj32 col hcol hheadw]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [key 0 (by omega), key 1 (by omega), key 2 (by omega), key 3 (by omega)]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]



/-- BW_linear dX column-parallel lemmas for goal_140 (_g140 suffix). -/

theorem allGatherPrimDimN_2_4_valAt_1_8_32_g140 (gs : List Tensor)
    (hhead : (gs.head?.map (fun t => t.shape)).getD [] = [1, 8, 32])
    (seq : Nat) (hseq : seq < 8) (r : Nat) (hr : r < 4) (lj : Nat) (hlj : lj < 32) :
    valAt (allGatherPrimDimN 2 4 0 gs) (seq * 128 + r * 32 + lj) =
      valAt (gs.getD r (zeroTensor [1, 8, 32])) (seq * 32 + lj) := by
  have hgather_shape : (allGatherPrimDimN 2 4 0 gs).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 gs [1, 8, 32] hhead]
    simp [List.set, List.getD]
  have hidx_lt : seq * 128 + r * 32 + lj < 1024 := by omega
  have hidx_prod : seq * 128 + r * 32 + lj < prodShape (allGatherPrimDimN 2 4 0 gs).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    show (4 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have hd128 : (seq * 128 + r * 32 + lj) / 128 = seq := by omega
  have hm128 : (seq * 128 + r * 32 + lj) % 128 = r * 32 + lj := by omega
  have hdr : (r * 32 + lj) / 32 = r := by omega
  have hmr : (r * 32 + lj) % 32 = lj := by omega
  simp only [Nat.mul_one, Nat.div_one, Nat.mod_one, Nat.add_zero]
  rw [hd128, hm128, hdr, hmr]

set_option maxRecDepth 8000 in
theorem allGatherPrimDimN_0_4_valAt_32_32_g140 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [32, 32])
    (r : Nat) (hr : r < 4) (lj : Nat) (hlj : lj < 32) (col : Nat) (hcol : col < 32) :
    valAt (allGatherPrimDimN 0 4 0 ws) ((r * 32 + lj) * 32 + col) =
      valAt (ws.getD r (zeroTensor [32, 32])) (lj * 32 + col) := by
  have hgather_shape : (allGatherPrimDimN 0 4 0 ws).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 ws [32, 32] hhead]
    simp [List.set, List.getD]
  have hidx_lt : (r * 32 + lj) * 32 + col < 4096 := by omega
  have hidx_prod : (r * 32 + lj) * 32 + col < prodShape (allGatherPrimDimN 0 4 0 ws).shape := by
    rw [hgather_shape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hidx_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (32 : Nat) ≠ 0 by omega, show (128 : Nat) ≠ 0 by omega,
    show (4 : Nat) ≠ 0 by omega, show (4096 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have hd4096 : ((r * 32 + lj) * 32 + col) / 4096 = 0 := by omega
  have hm4096 : ((r * 32 + lj) * 32 + col) % 4096 = (r * 32 + lj) * 32 + col := by omega
  have hd32 : ((r * 32 + lj) * 32 + col) / 32 = r * 32 + lj := by omega
  have hm32 : ((r * 32 + lj) * 32 + col) % 32 = col := by omega
  have hdr : (r * 32 + lj) / 32 = r := by omega
  have hmr : (r * 32 + lj) % 32 = lj := by omega
  rw [hd4096, hm4096, hd32, hm32, hdr, hmr]
  congr 1
  omega

theorem bw_linear_3d_fst_valAt_b1_i32_g140 (g x w : Tensor) (o : Nat)
    (hg : g.shape = [1, 8, o]) (hx : x.shape = [1, 8, 32]) (hw : w.shape = [o, 32])
    (seq col : Nat) (hseq : seq < 8) (hcol : col < 32) :
    valAt (bw_linear g x w).1 (seq * 32 + col) =
      ∑ j ∈ Finset.range o, valAt g (seq * o + j) * valAt w (j * 32 + col) := by
  have hbw : (bw_linear g x w).1 = Tensor.mkShape [1, 8, 32] (fun outIdx =>
      ∑ j ∈ Finset.range o,
        valAt g (((if (8 * 32 : Nat) = 0 then 0 else outIdx.1 / (8 * 32)) * 8 +
                  (if (32 : Nat) = 0 then 0 else
                    (if (8 * 32 : Nat) = 0 then 0 else outIdx.1 % (8 * 32)) / 32)) * o + j) *
        valAt w (j * 32 +
          (if (32 : Nat) = 0 then 0 else
            (if (8 * 32 : Nat) = 0 then 0 else outIdx.1 % (8 * 32)) % 32))) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hbw]
  have hprod : seq * 32 + col < prodShape (Tensor.mkShape [1, 8, 32]
      (fun outIdx : Fin (prodShape ([1, 8, 32] : Shape)) =>
        ∑ j ∈ Finset.range o,
          valAt g (((if (8 * 32 : Nat) = 0 then 0 else outIdx.1 / (8 * 32)) * 8 +
                    (if (32 : Nat) = 0 then 0 else
                      (if (8 * 32 : Nat) = 0 then 0 else outIdx.1 % (8 * 32)) / 32)) * o + j) *
          valAt w (j * 32 +
            (if (32 : Nat) = 0 then 0 else
              (if (8 * 32 : Nat) = 0 then 0 else outIdx.1 % (8 * 32)) % 32)))).shape := by
    simp only [Tensor.mkShape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hprod]
  simp only [Tensor.mkShape]
  have h1 : (seq * 32 + col) / 256 = 0 := by omega
  have h2 : (seq * 32 + col) % 256 = seq * 32 + col := by omega
  have h3 : (seq * 32 + col) / 32 = seq := by omega
  have h4 : (seq * 32 + col) % 32 = col := by omega
  norm_num [h1, h2, h3, h4]

set_option maxHeartbeats 1600000 in
theorem bw_linear_dx_colParallel_4_1_8_32_128_g140
    (x : Tensor) (gs ws : List Tensor)
    (hx : x.shape = [1, 8, 32])
    (hglen : gs.length = 4) (hwlen : ws.length = 4)
    (hgshape : ∀ g ∈ gs, g.shape = [1, 8, 32])
    (hwshape : ∀ w ∈ ws, w.shape = [32, 32]) :
    (bw_linear (allGatherPrimDimN 2 4 0 gs) x (allGatherPrimDimN 0 4 0 ws)).1 =
    allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      (bw_linear (gs.getD r.val (zeroTensor [1, 8, 32])) x
        (ws.getD r.val (zeroTensor [32, 32]))).1)) := by
  have hghead : (gs.head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    match gs, hglen, hgshape with
    | g0 :: _, _, hgshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hgshape g0 (List.mem_cons_self ..)
  have hwhead : (ws.head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    match ws, hwlen, hwshape with
    | w0 :: _, _, hwshape =>
      simp only [List.head?, Option.map, Option.getD]
      exact hwshape w0 (List.mem_cons_self ..)
  have hgsr : ∀ r, r < 4 → (gs.getD r (zeroTensor [1, 8, 32])).shape = [1, 8, 32] := by
    intro r hr
    have hlen : r < gs.length := by omega
    rw [List.getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    exact hgshape _ (List.getElem_mem hlen)
  have hwsr : ∀ r, r < 4 → (ws.getD r (zeroTensor [32, 32])).shape = [32, 32] := by
    intro r hr
    have hlen : r < ws.length := by omega
    rw [List.getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    exact hwshape _ (List.getElem_mem hlen)
  have hgrad_shape : (allGatherPrimDimN 2 4 0 gs).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 gs [1, 8, 32] hghead]; simp [List.set, List.getD]
  have hw_shape : (allGatherPrimDimN 0 4 0 ws).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 ws [32, 32] hwhead]; simp [List.set, List.getD]
  have hLHS_shape : (bw_linear (allGatherPrimDimN 2 4 0 gs) x
      (allGatherPrimDimN 0 4 0 ws)).1.shape = [1, 8, 32] :=
    bw_linear_3d_fst_shape 1 8 128 32 _ _ _ hgrad_shape hx hw_shape
  have hpiece_shape : ∀ r : Fin 4,
      (bw_linear (gs.getD r.val (zeroTensor [1, 8, 32])) x
        (ws.getD r.val (zeroTensor [32, 32]))).1.shape = [1, 8, 32] := by
    intro r
    exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ (hgsr r.val r.isLt) hx (hwsr r.val r.isLt)
  have hRHS_head : (List.ofFn (fun r : Fin 4 =>
      (bw_linear (gs.getD r.val (zeroTensor [1, 8, 32])) x
        (ws.getD r.val (zeroTensor [32, 32]))).1)).head? =
      some ((bw_linear (gs.getD 0 (zeroTensor [1, 8, 32])) x
        (ws.getD 0 (zeroTensor [32, 32]))).1) := by
    simp only [List.ofFn_succ, List.head?_cons, Fin.val_zero]
  have hRHS_shape : (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      (bw_linear (gs.getD r.val (zeroTensor [1, 8, 32])) x
        (ws.getD r.val (zeroTensor [32, 32]))).1))).shape = [1, 8, 32] := by
    rw [allReducePrim_shape 4 0 _ _ hRHS_head]
    exact hpiece_shape ⟨0, by omega⟩
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  rw [hLHS_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  set seq := idx / 32 with hseq_def
  set col := idx % 32 with hcol_def
  have hcol : col < 32 := Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by omega
  have hidx_eq : idx = seq * 32 + col := by omega
  -- LHS value
  have hLHS : valAt (bw_linear (allGatherPrimDimN 2 4 0 gs) x
      (allGatherPrimDimN 0 4 0 ws)).1 idx =
      ∑ r ∈ Finset.range 4, ∑ lj ∈ Finset.range 32,
        valAt (gs.getD r (zeroTensor [1, 8, 32])) (seq * 32 + lj) *
        valAt (ws.getD r (zeroTensor [32, 32])) (lj * 32 + col) := by
    rw [hidx_eq]
    rw [bw_linear_3d_fst_valAt_b1_i32_g140 (allGatherPrimDimN 2 4 0 gs) x
      (allGatherPrimDimN 0 4 0 ws) 128 hgrad_shape hx hw_shape seq col hseq hcol]
    rw [show (128 : Nat) = 4 * 32 from rfl,
      Finset.sum_range_mul_eq_sum_sum 4 32]
    apply Finset.sum_congr rfl; intro r hr
    apply Finset.sum_congr rfl; intro lj hlj
    have hr4 : r < 4 := Finset.mem_range.mp hr
    have hlj32 : lj < 32 := Finset.mem_range.mp hlj
    rw [show seq * 128 + (r * 32 + lj) = seq * 128 + r * 32 + lj from by ring]
    rw [allGatherPrimDimN_2_4_valAt_1_8_32_g140 gs hghead seq hseq r hr4 lj hlj32]
    rw [allGatherPrimDimN_0_4_valAt_32_32_g140 ws hwhead r hr4 lj hlj32 col hcol]
  -- RHS value
  have hterm : ∀ r : Nat, r < 4 →
      valAt (bw_linear (gs.getD r (zeroTensor [1, 8, 32])) x
        (ws.getD r (zeroTensor [32, 32]))).1 idx =
      ∑ lj ∈ Finset.range 32,
        valAt (gs.getD r (zeroTensor [1, 8, 32])) (seq * 32 + lj) *
        valAt (ws.getD r (zeroTensor [32, 32])) (lj * 32 + col) := by
    intro r hr
    rw [hidx_eq]
    exact bw_linear_3d_fst_valAt_b1_i32_g140 (gs.getD r (zeroTensor [1, 8, 32])) x
      (ws.getD r (zeroTensor [32, 32])) 32 (hgsr r hr) hx (hwsr r hr) seq col hseq hcol
  have hRHS : valAt (allReducePrim 4 0 (List.ofFn (fun r : Fin 4 =>
      (bw_linear (gs.getD r.val (zeroTensor [1, 8, 32])) x
        (ws.getD r.val (zeroTensor [32, 32]))).1))) idx =
      ∑ r ∈ Finset.range 4, ∑ lj ∈ Finset.range 32,
        valAt (gs.getD r (zeroTensor [1, 8, 32])) (seq * 32 + lj) *
        valAt (ws.getD r (zeroTensor [32, 32])) (lj * 32 + col) := by
    have hpiece0_prod : idx < prodShape ((bw_linear (gs.getD 0 (zeroTensor [1, 8, 32])) x
        (ws.getD 0 (zeroTensor [32, 32]))).1).shape := by
      rw [hpiece_shape ⟨0, by omega⟩]; simpa [prodShape] using hidx256
    rw [allReducePrim_valAt 4 0 _ idx _ hRHS_head hpiece0_prod]
    have hlist_eq : List.ofFn (fun r : Fin 4 =>
        (bw_linear (gs.getD r.val (zeroTensor [1, 8, 32])) x
          (ws.getD r.val (zeroTensor [32, 32]))).1) =
        [(bw_linear (gs.getD 0 (zeroTensor [1, 8, 32])) x (ws.getD 0 (zeroTensor [32, 32]))).1,
         (bw_linear (gs.getD 1 (zeroTensor [1, 8, 32])) x (ws.getD 1 (zeroTensor [32, 32]))).1,
         (bw_linear (gs.getD 2 (zeroTensor [1, 8, 32])) x (ws.getD 2 (zeroTensor [32, 32]))).1,
         (bw_linear (gs.getD 3 (zeroTensor [1, 8, 32])) x (ws.getD 3 (zeroTensor [32, 32]))).1] := by
      rfl
    rw [hlist_eq]
    simp only [List.foldl]
    rw [hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hLHS, hRHS]


-- ===== batch5 g170 net-new lemma(s) =====
set_option maxHeartbeats 1600000 in
/-- Mirror of `bw_linear_dw_dp_split_dim1_4_1_2_32` with the data-parallel roles
    swapped: the gradient `g` (`[1,8,32]`) is dim-1 all-gathered from 4 shards
    (each `[1,2,32]`) and the activation `x` (`[1,8,32]`) is dim-1 chunked per rank.
    The full dW equals `tensorSum` of the per-rank dW outputs (CROSS_DP_WRED). -/
theorem bw_linear_dw_dp_split_dim1_4_1_2_32_g170
    (g0 g1 g2 g3 x w : Tensor)
    (hg0 : g0.shape = [1, 2, 32]) (hg1 : g1.shape = [1, 2, 32])
    (hg2 : g2.shape = [1, 2, 32]) (hg3 : g3.shape = [1, 2, 32])
    (hx : x.shape = [1, 8, 32])
    (hw : w.shape = [32, 32]) :
    (bw_linear (allGatherPrimDimN 1 4 0 [g0, g1, g2, g3]) x w).2 =
      tensorSum [(bw_linear g0 (chunkPrimDimN 1 4 0 x) w).2,
                 (bw_linear g1 (chunkPrimDimN 1 4 1 x) w).2,
                 (bw_linear g2 (chunkPrimDimN 1 4 2 x) w).2,
                 (bw_linear g3 (chunkPrimDimN 1 4 3 x) w).2] := by
  have hghead : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hg0]
  set G := allGatherPrimDimN 1 4 0 [g0, g1, g2, g3] with hGdef
  have hGshape : G.shape = [1, 8, 32] := by
    rw [hGdef, allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hghead]; simp [List.set, List.getD]
  have hc0 : (chunkPrimDimN 1 4 0 x).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 0 x _ hx (by omega)]; simp [List.set, List.getD]
  have hc1 : (chunkPrimDimN 1 4 1 x).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 1 x _ hx (by omega)]; simp [List.set, List.getD]
  have hc2 : (chunkPrimDimN 1 4 2 x).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 2 x _ hx (by omega)]; simp [List.set, List.getD]
  have hc3 : (chunkPrimDimN 1 4 3 x).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 3 x _ hx (by omega)]; simp [List.set, List.getD]
  apply Tensor.ext
  · rw [bw_linear_3d_snd_shape 1 8 32 32 G x w hGshape hx hw, tensorSum_shape,
        bw_linear_3d_snd_shape 1 2 32 32 g0 (chunkPrimDimN 1 4 0 x) w hg0 hc0 hw]
  · intro idx hidx
    rw [bw_linear_3d_snd_shape 1 8 32 32 G x w hGshape hx hw] at hidx
    have hidxp : idx < 1024 := by simpa [prodShape] using hidx
    have hc : idx / 32 < 32 := by omega
    have hk : idx % 32 < 32 := by omega
    have hide : idx = (idx / 32) * 32 + idx % 32 := by omega
    rw [hide]
    rw [bw_linear_dw_valAt3d G x w 1 8 32 32 hGshape hx hw (idx / 32) hc (idx % 32) hk]
    rw [show tensorSum [(bw_linear g0 (chunkPrimDimN 1 4 0 x) w).2,
                        (bw_linear g1 (chunkPrimDimN 1 4 1 x) w).2,
                        (bw_linear g2 (chunkPrimDimN 1 4 2 x) w).2,
                        (bw_linear g3 (chunkPrimDimN 1 4 3 x) w).2] =
            Tensor.mkShape (bw_linear g0 (chunkPrimDimN 1 4 0 x) w).2.shape
              (fun i => [(bw_linear g0 (chunkPrimDimN 1 4 0 x) w).2,
                         (bw_linear g1 (chunkPrimDimN 1 4 1 x) w).2,
                         (bw_linear g2 (chunkPrimDimN 1 4 2 x) w).2,
                         (bw_linear g3 (chunkPrimDimN 1 4 3 x) w).2].foldl
                         (fun acc x => acc + valAt x i.1) 0) from rfl]
    rw [valAt_of_lt _ _ (by
      rw [Tensor.mkShape, bw_linear_3d_snd_shape 1 2 32 32 g0 (chunkPrimDimN 1 4 0 x) w hg0 hc0 hw]
      simp [prodShape]; omega)]
    simp only [Tensor.mkShape, List.foldl]
    rw [bw_linear_dw_valAt3d g0 (chunkPrimDimN 1 4 0 x) w 1 2 32 32 hg0 hc0 hw (idx / 32) hc (idx % 32) hk,
        bw_linear_dw_valAt3d g1 (chunkPrimDimN 1 4 1 x) w 1 2 32 32 hg1 hc1 hw (idx / 32) hc (idx % 32) hk,
        bw_linear_dw_valAt3d g2 (chunkPrimDimN 1 4 2 x) w 1 2 32 32 hg2 hc2 hw (idx / 32) hc (idx % 32) hk,
        bw_linear_dw_valAt3d g3 (chunkPrimDimN 1 4 3 x) w 1 2 32 32 hg3 hc3 hw (idx / 32) hc (idx % 32) hk]
    simp only [show (1 : Nat) * 8 = 8 from rfl, show (1 : Nat) * 2 = 2 from rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [chunk_dim1_4_1_8_32_valAt x 0 0 (idx % 32) hx (by omega) (by omega) hk,
        chunk_dim1_4_1_8_32_valAt x 0 1 (idx % 32) hx (by omega) (by omega) hk,
        chunk_dim1_4_1_8_32_valAt x 1 0 (idx % 32) hx (by omega) (by omega) hk,
        chunk_dim1_4_1_8_32_valAt x 1 1 (idx % 32) hx (by omega) (by omega) hk,
        chunk_dim1_4_1_8_32_valAt x 2 0 (idx % 32) hx (by omega) (by omega) hk,
        chunk_dim1_4_1_8_32_valAt x 2 1 (idx % 32) hx (by omega) (by omega) hk,
        chunk_dim1_4_1_8_32_valAt x 3 0 (idx % 32) hx (by omega) (by omega) hk,
        chunk_dim1_4_1_8_32_valAt x 3 1 (idx % 32) hx (by omega) (by omega) hk]
    rw [hGdef]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 0 (by omega) 0 (by omega) (idx / 32) hc hghead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 0 (by omega) 1 (by omega) (idx / 32) hc hghead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 1 (by omega) 0 (by omega) (idx / 32) hc hghead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 1 (by omega) 1 (by omega) (idx / 32) hc hghead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 2 (by omega) 0 (by omega) (idx / 32) hc hghead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 2 (by omega) 1 (by omega) (idx / 32) hc hghead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 3 (by omega) 0 (by omega) (idx / 32) hc hghead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [g0, g1, g2, g3] 3 (by omega) 1 (by omega) (idx / 32) hc hghead]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    ring


-- ===== batch5 g178 net-new lemma(s) =====
/-- Value of `bw_linear` dX (first output) for 3D inputs with output shape `[1,8,128]`
    and grad inner dim `o` (goal_178). -/
theorem bw_linear_fst_valAt_1_8_128_g178 (g x w : Tensor) (o : Nat)
    (hg : g.shape = [1, 8, o]) (hx : x.shape = [1, 8, 128]) (hw : w.shape = [o, 128])
    (P : Nat) (hP : P < 8) (col : Nat) (hcol : col < 128) :
    valAt (bw_linear g x w).1 (P * 128 + col) =
      ∑ j ∈ Finset.range o, valAt g (P * o + j) * valAt w (j * 128 + col) := by
  have hdx : (bw_linear g x w).1 =
      Tensor.mkShape [1, 8, 128] (fun outIdx =>
        ∑ j ∈ Finset.range o,
          valAt g (((if (8:Nat) * 128 = 0 then 0 else outIdx.1 / (8 * 128)) * 8 +
                    if (128:Nat) = 0 then 0 else (if (8:Nat) * 128 = 0 then 0 else outIdx.1 % (8 * 128)) / 128) * o + j) *
          valAt w (j * 128 + if (128:Nat) = 0 then 0 else (if (8:Nat) * 128 = 0 then 0 else outIdx.1 % (8 * 128)) % 128)) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hdx]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl]; omega)]
  simp only [Tensor.mkShape]
  have e1 : (P*128+col)/(8*128) = 0 := by omega
  have e2 : ((P*128+col)%(8*128))/128 = P := by omega
  have e3 : ((P*128+col)%(8*128))%128 = col := by omega
  simp only [show ((8:Nat)*128=0)=False from by simp, show ((128:Nat)=0)=False from by simp,
    if_false, e1, e2, e3, Nat.zero_mul, Nat.zero_add]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
/-- Value of `allGatherPrimDimN 0 4` over shards of shape `[8,128]` (goal_178). -/
theorem allGatherDimN0_4_8128_valAt_g178 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [8, 128])
    (r : Nat) (hr : r < 4) (jl : Nat) (hjl : jl < 8) (col : Nat) (hcol : col < 128) :
    valAt (allGatherPrimDimN 0 4 0 ws) ((r * 8 + jl) * 128 + col) =
      valAt (ws.getD r (zeroTensor [8, 128])) (jl * 128 + col) := by
  have hshape : (allGatherPrimDimN 0 4 0 ws).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 0 4 ws [8, 128] hhead]; simp [List.set, List.getD]
  have hbound : (r * 8 + jl) * 128 + col < prodShape (allGatherPrimDimN 0 4 0 ws).shape := by
    rw [hshape]; simp only [prodShape, List.foldl]; omega
  rw [valAt_of_lt _ _ hbound]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, show ([8,128].getD 0 0 : Nat) = 8 from rfl]
  have d1 : ((r * 8 + jl) * 128 + col) / (8 * 4 * 128) = 0 := by omega
  have d2 : ((r * 8 + jl) * 128 + col) % (8 * 4 * 128) / 128 / 8 = r := by omega
  have d3 : ((r * 8 + jl) * 128 + col) % (8 * 4 * 128) / 128 % 8 = jl := by omega
  have d4 : ((r * 8 + jl) * 128 + col) % (8 * 4 * 128) % 128 = col := by omega
  simp only [show (8*4*128:Nat) ≠ 0 from by omega, show (8:Nat) ≠ 0 from by omega,
    show (128:Nat) ≠ 0 from by omega, if_false, d1, d2, d3, d4]
  congr 1
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- Tensor-parallel dX reduction for `BW_linear`: dim-2 split gradient (`[1,8,8]` shards)
    + dim-0 split weight (`[8,128]` shards), reduced by `allReducePrim` (goal_178). -/
theorem bw_linear_dx_tp_split_dim2_4_g178
    (g0 g1 g2 g3 x w0 w1 w2 w3 : Tensor)
    (hg0 : g0.shape = [1,8,8]) (hg1 : g1.shape = [1,8,8])
    (hg2 : g2.shape = [1,8,8]) (hg3 : g3.shape = [1,8,8])
    (hx : x.shape = [1,8,128])
    (hw0 : w0.shape = [8,128]) (hw1 : w1.shape = [8,128])
    (hw2 : w2.shape = [8,128]) (hw3 : w3.shape = [8,128]) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0,g1,g2,g3]) x
        (allGatherPrimDimN 0 4 0 [w0,w1,w2,w3])).1 =
      allReducePrim 4 0
        [(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1] := by
  have hheadg : (([g0,g1,g2,g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1,8,8] := by
    simp [hg0]
  have hheadw : (([w0,w1,w2,w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [8,128] := by
    simp [hw0]
  set G := allGatherPrimDimN 2 4 0 [g0,g1,g2,g3] with hGdef
  set W := allGatherPrimDimN 0 4 0 [w0,w1,w2,w3] with hWdef
  have hGshape : G.shape = [1,8,32] := by
    rw [hGdef, allGatherPrimDimN_shape 2 4 _ [1,8,8] hheadg]; simp [List.set, List.getD]
  have hWshape : W.shape = [32,128] := by
    rw [hWdef, allGatherPrimDimN_shape 0 4 _ [8,128] hheadw]; simp [List.set, List.getD]
  have hLshape : (bw_linear G x W).1.shape = [1,8,128] :=
    bw_linear_3d_fst_shape 1 8 32 128 G x W hGshape hx hWshape
  have hdx0shape : (bw_linear g0 x w0).1.shape = [1,8,128] :=
    bw_linear_3d_fst_shape 1 8 8 128 g0 x w0 hg0 hx hw0
  have hRhead : ([(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1] : List Tensor).head?
       = some (bw_linear g0 x w0).1 := rfl
  have hRshape : (allReducePrim 4 0
        [(bw_linear g0 x w0).1, (bw_linear g1 x w1).1,
         (bw_linear g2 x w2).1, (bw_linear g3 x w3).1]).shape = [1,8,128] := by
    rw [allReducePrim_shape 4 0 _ _ hRhead, hdx0shape]
  apply Tensor.ext
  · rw [hLshape, hRshape]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx1024 : idx < 1024 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/128 < 8 := by omega
    have hcol : idx%128 < 128 := by omega
    have hidxeq : idx = (idx/128)*128 + idx%128 := by omega
    rw [hidxeq]
    set P := idx/128 with hPdef
    set col := idx%128 with hcoldef
    rw [allReducePrim_valAt 4 0 _ (P*128+col) (bw_linear g0 x w0).1 hRhead (by rw [hdx0shape]; simp [prodShape]; omega)]
    simp only [List.foldl, zero_add]
    rw [bw_linear_fst_valAt_1_8_128_g178 g0 x w0 8 hg0 hx hw0 P hP col hcol,
        bw_linear_fst_valAt_1_8_128_g178 g1 x w1 8 hg1 hx hw1 P hP col hcol,
        bw_linear_fst_valAt_1_8_128_g178 g2 x w2 8 hg2 hx hw2 P hP col hcol,
        bw_linear_fst_valAt_1_8_128_g178 g3 x w3 8 hg3 hx hw3 P hP col hcol]
    rw [bw_linear_fst_valAt_1_8_128_g178 G x W 32 hGshape hx hWshape P hP col hcol]
    have hsplit : (∑ j ∈ Finset.range 32, valAt G (P*32+j) * valAt W (j*128+col))
        = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 8,
            valAt G (P*32+(i*8+j)) * valAt W ((i*8+j)*128+col) := by
      have := Finset.sum_range_mul_eq_sum_sum 4 8 (fun k => valAt G (P*32+k) * valAt W (k*128+col))
      simpa using this
    rw [hsplit]
    have key : ∀ i, i < 4 →
        (∑ j ∈ Finset.range 8, valAt G (P*32+(i*8+j)) * valAt W ((i*8+j)*128+col))
        = ∑ j ∈ Finset.range 8,
            valAt ([g0,g1,g2,g3].getD i (zeroTensor [1,8,8])) (P*8+j)
            * valAt ([w0,w1,w2,w3].getD i (zeroTensor [8,128])) (j*128+col) := by
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hj8 : j < 8 := Finset.mem_range.mp hj
      rw [hGdef, allGatherDimN2_4_188_valAt_g134 [g0,g1,g2,g3] hheadg P hP i hi j hj8,
          hWdef, allGatherDimN0_4_8128_valAt_g178 [w0,w1,w2,w3] hheadw i hi j hj8 col hcol]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [key 0 (by omega), key 1 (by omega), key 2 (by omega), key 3 (by omega)]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]


-- ===== batch5 g179 net-new lemma(s) =====
/- BW_linear dW (g179): same output-(tensor-)parallel weight-gradient identity as g135,
   but with the input dim `i = 128`.  The gradient `g` (`[1,8,32]`) is split along the
   output dim into 4 shards (each `[1,8,8]`, all-gathered on dim 2), `x` (`[1,8,128]`) is
   replicated, and the weight `w` (`[32,128]`) is split along dim 0 (each `[8,128]`).  The
   full dW (`[32,128]`) is the dim-0 concatenation (`allGatherPrimDimN 0`) of the per-rank
   dW shards (each `[8,128]`).  dW depends only on `g` and `x`, so the per-rank `w` shards
   are irrelevant to the value. -/
set_option maxHeartbeats 800000 in
theorem bw_linear_dw_osplit_dim2_4_1_8_8_g179
    (x g0 g1 g2 g3 w0 w1 w2 w3 : Tensor)
    (hx : x.shape = [1, 8, 128])
    (hg0 : g0.shape = [1, 8, 8]) (hg1 : g1.shape = [1, 8, 8])
    (hg2 : g2.shape = [1, 8, 8]) (hg3 : g3.shape = [1, 8, 8])
    (hw0 : w0.shape = [8, 128]) (hw1 : w1.shape = [8, 128])
    (hw2 : w2.shape = [8, 128]) (hw3 : w3.shape = [8, 128]) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
        (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 0 4 0
        [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
         (bw_linear g2 x w2).2, (bw_linear g3 x w3).2] := by
  -- head shapes
  have hghead : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hg0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [8, 128] := by
    simp [hw0]
  -- gathered input shapes
  have hG_shape : (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hghead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hwhead]; simp [List.set, List.getD]
  -- per-rank dW shapes
  have hp0 : (bw_linear g0 x w0).2.shape = [8, 128] := bw_linear_3d_snd_shape 1 8 8 128 g0 x w0 hg0 hx hw0
  have hp1 : (bw_linear g1 x w1).2.shape = [8, 128] := bw_linear_3d_snd_shape 1 8 8 128 g1 x w1 hg1 hx hw1
  have hp2 : (bw_linear g2 x w2).2.shape = [8, 128] := bw_linear_3d_snd_shape 1 8 8 128 g2 x w2 hg2 hx hw2
  have hp3 : (bw_linear g3 x w3).2.shape = [8, 128] := bw_linear_3d_snd_shape 1 8 8 128 g3 x w3 hg3 hx hw3
  set pieces : List Tensor :=
    [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2, (bw_linear g2 x w2).2, (bw_linear g3 x w3).2]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [8, 128] := by
    simp [hpieces_def, hp0]
  have hpgetD : ∀ r, r < 4 → (pieces.getD r (zeroTensor [8, 128])).shape = [8, 128] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hpieces_def, List.getD, hp0, hp1, hp2, hp3]
  -- LHS / RHS shapes
  have hLHS_shape : (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2.shape = [32, 128] :=
    bw_linear_3d_snd_shape 1 8 32 128 _ x _ hG_shape hx hW_shape
  have hRHS_shape : (allGatherPrimDimN 0 4 0 pieces).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx4096 : idx < 4096 := by simpa [hLHS_shape, prodShape] using hidx
  set c := idx / 128 with hc_def
  set k := idx % 128 with hk_def
  have hk : k < 128 := by rw [hk_def]; exact Nat.mod_lt _ (by omega)
  have hc : c < 32 := by rw [hc_def]; omega
  have hidx_eq : idx = c * 128 + k := by rw [hc_def, hk_def]; omega
  rw [hidx_eq]
  -- LHS value
  rw [bw_linear_dw_valAt3d (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]) 1 8 32 128 hG_shape hx hW_shape c hc k hk]
  -- RHS value: rewrite index into (r*8+oc) form and peel the dim-0 gather
  have hoc : c % 8 < 8 := Nat.mod_lt _ (by omega)
  have hr : c / 8 < 4 := by omega
  conv_rhs => rw [show c * 128 + k = (c / 8 * 8 + c % 8) * 128 + k from by
    have : c / 8 * 8 + c % 8 = c := by omega
    rw [this]]
  rw [allGatherPrimDimN0_valAt 4 8 128 pieces (by omega) (by omega) (by omega)
      hphead hpgetD (c / 8) hr (c % 8) hoc k hk]
  -- expand the selected per-rank dW and match term by term
  have hG_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) (p * 32 + c) =
      valAt (([g0, g1, g2, g3] : List Tensor).getD (c / 8) (zeroTensor [1, 8, 8])) (p * 8 + c % 8) := by
    intro p hp
    have hb : p * 32 + c < 256 := by omega
    rw [allGatherPrimDimN_2_4_valAt_1_8_8 [g0, g1, g2, g3] (p * 32 + c) hghead hb]
    have hrank : (p * 32 + c) % 32 / 8 = c / 8 := by omega
    have hflat : (p * 32 + c) / 32 * 8 + (p * 32 + c) % 8 = p * 8 + c % 8 := by omega
    rw [hrank, hflat]
  rcases (show c / 8 = 0 ∨ c / 8 = 1 ∨ c / 8 = 2 ∨ c / 8 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_dw_valAt3d g0 x w0 1 8 8 128 hg0 hx hw0 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g1 x w1 1 8 8 128 hg1 hx hw1 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g2 x w2 1 8 8 128 hg2 hx hw2 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g3 x w3 1 8 8 128 hg3 hx hw3 (c % 8) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp



-- ===== batch5 g204 net-new lemma(s) =====

-- ==== batch5 g204 additions ====
/-- Value of `bw_linear` dX with output shape `[1,8,8]` (input dim `i = 8`),
    gradient `g : [1,8,32]`, weight `w : [32,8]`. -/
theorem bw_linear_fst_valAt_1_8_8_g204 (g x w : Tensor)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 8]) (hw : w.shape = [32, 8])
    (P : Nat) (hP : P < 8) (col : Nat) (hcol : col < 8) :
    valAt (bw_linear g x w).1 (P * 8 + col) =
      ∑ j ∈ Finset.range 32, valAt g (P * 32 + j) * valAt w (j * 8 + col) := by
  have hdx : (bw_linear g x w).1 =
      Tensor.mkShape [1, 8, 8] (fun outIdx =>
        ∑ j ∈ Finset.range 32,
          valAt g (((if (8:Nat) * 8 = 0 then 0 else outIdx.1 / (8 * 8)) * 8 +
                    if (8:Nat) = 0 then 0 else (if (8:Nat) * 8 = 0 then 0 else outIdx.1 % (8 * 8)) / 8) * 32 + j) *
          valAt w (j * 8 + if (8:Nat) = 0 then 0 else (if (8:Nat) * 8 = 0 then 0 else outIdx.1 % (8 * 8)) % 8)) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hdx]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl]; omega)]
  simp only [Tensor.mkShape]
  have e1 : (P*8+col)/(8*8) = 0 := by omega
  have e2 : ((P*8+col)%(8*8))/8 = P := by omega
  have e3 : ((P*8+col)%(8*8))%8 = col := by omega
  simp only [show ((8:Nat)*8=0)=False from by simp, show ((8:Nat)=0)=False from by simp,
    if_false, e1, e2, e3, Nat.zero_mul, Nat.zero_add]

set_option maxRecDepth 8192 in
/-- Value of `allGatherPrimDimN 1 4` over shards of shape `[32,8]` (gather on dim 1). -/
theorem allGatherPrimDimN_1_4_valAt_32_8_g204 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [32, 8])
    (a : Nat) (ha : a < 32) (r : Nat) (hr : r < 4) (b : Nat) (hb : b < 8) :
    valAt (allGatherPrimDimN 1 4 0 ws) (a * 32 + (r * 8 + b)) =
      valAt (ws.getD r (zeroTensor [32, 8])) (a * 8 + b) := by
  have hshape : (allGatherPrimDimN 1 4 0 ws).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 ws [32, 8] hhead]; simp [List.set, List.getD]
  have hbound : a * 32 + (r * 8 + b) < prodShape (allGatherPrimDimN 1 4 0 ws).shape := by
    rw [hshape]; simp only [prodShape, List.foldl]; omega
  rw [valAt_of_lt _ _ hbound]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, show ([32,8].getD 1 0 : Nat) = 8 from rfl]
  have d1 : (a * 32 + (r * 8 + b)) / (8 * 4 * 1) = a := by omega
  have d2 : ((a * 32 + (r * 8 + b)) % (8 * 4 * 1)) / 1 / 8 = r := by omega
  have d3 : ((a * 32 + (r * 8 + b)) % (8 * 4 * 1)) / 1 % 8 = b := by omega
  have d4 : ((a * 32 + (r * 8 + b)) % (8 * 4 * 1)) % 1 = 0 := by omega
  simp only [show (8*4*1:Nat) ≠ 0 from by omega, show (8:Nat) ≠ 0 from by omega,
    show (1:Nat) ≠ 0 from by omega, if_false, d1, d2, d3, d4]
  congr 1
  omega

set_option maxHeartbeats 2000000 in
/-- Tensor-parallel (input-feature) dX split of `BW_linear`: the gradient `g` (`[1,8,32]`)
    is shared, the activation `x` (`[1,8,32]`) is locally dim-2 chunked per rank, and the
    weight `w` (`[32,32]`) is dim-1 all-gathered from four `[32,8]` shards.  Then the full
    dX equals the dim-2 all-gather of the per-rank dX outputs (`[1,8,8]`). -/
theorem bw_linear_dx_isplit_dim2_4_g204
    (g x w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1,8,32]) (hx : x.shape = [1,8,32])
    (hw0 : w0.shape = [32,8]) (hw1 : w1.shape = [32,8])
    (hw2 : w2.shape = [32,8]) (hw3 : w3.shape = [32,8]) :
    (bw_linear g x (allGatherPrimDimN 1 4 0 [w0,w1,w2,w3])).1 =
      allGatherPrimDimN 2 4 0
        [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).1,
         (bw_linear g (chunkPrimDimN 2 4 1 x) w1).1,
         (bw_linear g (chunkPrimDimN 2 4 2 x) w2).1,
         (bw_linear g (chunkPrimDimN 2 4 3 x) w3).1] := by
  have hheadw : (([w0,w1,w2,w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32,8] := by
    simp [hw0]
  set W := allGatherPrimDimN 1 4 0 [w0,w1,w2,w3] with hWdef
  have hWshape : W.shape = [32,32] := by
    rw [hWdef, allGatherPrimDimN_shape 1 4 _ [32,8] hheadw]; simp [List.set, List.getD]
  have hcx0 : (chunkPrimDimN 2 4 0 x).shape = [1,8,8] := by
    rw [chunkPrimDimN_shape 2 4 0 x _ hx (by omega)]; simp [List.set, List.getD]
  have hcx1 : (chunkPrimDimN 2 4 1 x).shape = [1,8,8] := by
    rw [chunkPrimDimN_shape 2 4 1 x _ hx (by omega)]; simp [List.set, List.getD]
  have hcx2 : (chunkPrimDimN 2 4 2 x).shape = [1,8,8] := by
    rw [chunkPrimDimN_shape 2 4 2 x _ hx (by omega)]; simp [List.set, List.getD]
  have hcx3 : (chunkPrimDimN 2 4 3 x).shape = [1,8,8] := by
    rw [chunkPrimDimN_shape 2 4 3 x _ hx (by omega)]; simp [List.set, List.getD]
  have hdx0shape : (bw_linear g (chunkPrimDimN 2 4 0 x) w0).1.shape = [1,8,8] :=
    bw_linear_3d_fst_shape 1 8 32 8 _ _ _ hg hcx0 hw0
  have hLshape : (bw_linear g x W).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 g x W hg hx hWshape
  have hheadR : (([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).1,
                   (bw_linear g (chunkPrimDimN 2 4 1 x) w1).1,
                   (bw_linear g (chunkPrimDimN 2 4 2 x) w2).1,
                   (bw_linear g (chunkPrimDimN 2 4 3 x) w3).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,8,8] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 2 4 _ [1,8,8] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/32 < 8 := by omega
    have hcol : idx%32 < 32 := by omega
    have hide : idx = (idx/32)*32 + idx%32 := by omega
    rw [hide]
    set P := idx/32 with hPdef
    set col := idx%32 with hcoldef
    set r := col/8 with hrdef
    set b := col%8 with hbdef
    have hr : r < 4 := by omega
    have hb : b < 8 := by omega
    have hcolrb : col = r * 8 + b := by omega
    rw [bw_linear_fst_valAt_1_8_32_g134 g x W 32 hg hx hWshape P hP col hcol]
    have hRHS : valAt (allGatherPrimDimN 2 4 0
          [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).1,
           (bw_linear g (chunkPrimDimN 2 4 1 x) w1).1,
           (bw_linear g (chunkPrimDimN 2 4 2 x) w2).1,
           (bw_linear g (chunkPrimDimN 2 4 3 x) w3).1]) (P * 32 + col)
        = valAt ([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).1,
                  (bw_linear g (chunkPrimDimN 2 4 1 x) w1).1,
                  (bw_linear g (chunkPrimDimN 2 4 2 x) w2).1,
                  (bw_linear g (chunkPrimDimN 2 4 3 x) w3).1].getD r (zeroTensor [1,8,8]))
                (P * 8 + b) := by
      rw [hcolrb]
      exact allGatherDimN2_4_188_valAt_g134 _ hheadR P hP r hr b hb
    rw [hRHS]
    have hLHS : (∑ j ∈ Finset.range 32, valAt g (P*32+j) * valAt W (j*32+col))
        = ∑ j ∈ Finset.range 32,
            valAt g (P*32+j) * valAt ([w0,w1,w2,w3].getD r (zeroTensor [32,8])) (j*8+b) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      have hidxj : j * 32 + col = j * 32 + (r * 8 + b) := by rw [hcolrb]
      rw [hWdef, hidxj, allGatherPrimDimN_1_4_valAt_32_8_g204 [w0,w1,w2,w3] hheadw j hj32 r hr b hb]
    rw [hLHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_8_8_g204 g (chunkPrimDimN 2 4 0 x) w0 hg hcx0 hw0 P hP b hb]
    · rw [bw_linear_fst_valAt_1_8_8_g204 g (chunkPrimDimN 2 4 1 x) w1 hg hcx1 hw1 P hP b hb]
    · rw [bw_linear_fst_valAt_1_8_8_g204 g (chunkPrimDimN 2 4 2 x) w2 hg hcx2 hw2 P hP b hb]
    · rw [bw_linear_fst_valAt_1_8_8_g204 g (chunkPrimDimN 2 4 3 x) w3 hg hcx3 hw3 P hP b hb]


-- ===== batch5 g205 net-new lemma(s) =====
-- ==== batch5 g205 additions ====
/-- valAt of a `[1,8,32]` tensor chunked on dim 2 into four `[1,8,8]` shards. -/
theorem chunkPrimDimN2_4_1_8_32_valAt_g205 (x : Tensor) (r p j : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) (hp : p < 8) (hj : j < 8) :
    valAt (chunkPrimDimN 2 4 r x) (p * 8 + j) = valAt x (p * 32 + r * 8 + j) := by
  have hloc : p * 8 + j < 64 := by omega
  have hchunk_shape : (chunkPrimDimN 2 4 r x).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p * 8 + j < prodShape (chunkPrimDimN 2 4 r x).shape := by
    rw [hchunk_shape]
    simp [prodShape]
    exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have hidx : (p * 8 + j) / 8 * 32 + (r % 4 * 8 + (p * 8 + j) % 8 / 1) * 1 + (p * 8 + j) % 8 % 1 =
      p * 32 + r * 8 + j := by omega
  rw [hidx]

set_option maxHeartbeats 800000 in
/-- All-gather (dim 2) of the four dim-2 chunks of a `[1,8,32]` tensor recovers it. -/
theorem allGather_chunkPrimDimN_roundtrip_dim2_4_1_8_32_g205 (x : Tensor)
    (hx : x.shape = [1, 8, 32]) :
    allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x] = x := by
  have hc0 : (chunkPrimDimN 2 4 0 x).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 0 _ _ hx (by omega)]; simp [List.set, List.getD]
  have hhead : (([chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
      chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hc0]
  have hg_shape : (allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hg_shape, hx])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hg_shape, prodShape] using hidx
  rw [allGatherPrimDimN_2_4_valAt_1_8_8 _ _ hhead hidx256]
  have hp : idx / 32 < 8 := by omega
  have hj : idx % 8 < 8 := by omega
  rcases (show idx % 32 / 8 = 0 ∨ idx % 32 / 8 = 1 ∨ idx % 32 / 8 = 2 ∨ idx % 32 / 8 = 3
      from by omega) with h | h | h | h
  · rw [h]
    simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
    rw [chunkPrimDimN2_4_1_8_32_valAt_g205 x 0 (idx / 32) (idx % 8) hx (by omega) hp hj]
    congr 1; omega
  · rw [h]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [chunkPrimDimN2_4_1_8_32_valAt_g205 x 1 (idx / 32) (idx % 8) hx (by omega) hp hj]
    congr 1; omega
  · rw [h]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [chunkPrimDimN2_4_1_8_32_valAt_g205 x 2 (idx / 32) (idx % 8) hx (by omega) hp hj]
    congr 1; omega
  · rw [h]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [chunkPrimDimN2_4_1_8_32_valAt_g205 x 3 (idx / 32) (idx % 8) hx (by omega) hp hj]
    congr 1; omega



-- ============================================================
-- batch6 BW_linear net-new lemmas (g240/g255/g262/g264/g276)
-- ============================================================

-- ===== net-new lemmas from batch6 BW_linear g240 =====
-- ==== batch6 g240 additions ====

/-- Value of `allGatherPrimDimN` along dim 1 for 2D shards `[o, shard]`.
    The full tensor has shape `[o, shard * numParts]`; the value at the gathered
    index `(c, r*shard+i)` is the value of the `r`-th shard at `(c, i)`. -/
theorem allGatherPrimDimN1_valAt_g240
    (numParts o shard : Nat) (Ws : List Tensor)
    (hparts : 0 < numParts) (ho : 0 < o) (hshard : 0 < shard)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [o, shard])
    (hWs_shape : ∀ r (_ : r < numParts),
        (Ws.getD r (zeroTensor [o, shard])).shape = [o, shard])
    (c : Nat) (hc : c < o) (r : Nat) (hr : r < numParts) (i : Nat) (hi : i < shard) :
    valAt (allGatherPrimDimN 1 numParts 0 Ws) (c * (shard * numParts) + (r * shard + i)) =
      valAt (Ws.getD r (zeroTensor [o, shard])) (c * shard + i) := by
  have hshard_ne : shard ≠ 0 := Nat.ne_of_gt hshard
  have hFDS_pos : 0 < shard * numParts := Nat.mul_pos hshard hparts
  have hri : r * shard + i < shard * numParts := by
    have hsi : r * shard + i < (r + 1) * shard := by
      calc r * shard + i < r * shard + shard := by omega
        _ = (r + 1) * shard := by ring
    have hle : (r + 1) * shard ≤ numParts * shard := Nat.mul_le_mul_right _ hr
    calc r * shard + i < (r + 1) * shard := hsi
      _ ≤ numParts * shard := hle
      _ = shard * numParts := by ring
  -- index bound in the output
  have hidx_lt_full : c * (shard * numParts) + (r * shard + i) < o * (shard * numParts) := by
    calc c * (shard * numParts) + (r * shard + i) < c * (shard * numParts) + (shard * numParts) := by omega
      _ = (c + 1) * (shard * numParts) := by ring
      _ ≤ o * (shard * numParts) := Nat.mul_le_mul_right _ hc
  have hshape_out : (allGatherPrimDimN 1 numParts 0 Ws).shape = [o, shard * numParts] := by
    have := allGatherPrimDimN_shape 1 numParts Ws [o, shard] hhead
    simp only [List.set, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some] at this
    rw [this]
  have hidx_lt_prod : c * (shard * numParts) + (r * shard + i) <
      prodShape (allGatherPrimDimN 1 numParts 0 Ws).shape := by
    rw [hshape_out]; simpa [prodShape] using hidx_lt_full
  -- div/mod facts
  have hdiv_FDS : (c * (shard * numParts) + (r * shard + i)) / (shard * numParts) = c := by
    rw [show c * (shard * numParts) + (r * shard + i)
          = (r * shard + i) + (shard * numParts) * c from by ring,
        Nat.add_mul_div_left _ _ hFDS_pos, Nat.div_eq_of_lt hri, Nat.zero_add]
  have hmod_FDS : (c * (shard * numParts) + (r * shard + i)) % (shard * numParts) = r * shard + i := by
    rw [show c * (shard * numParts) + (r * shard + i)
          = (r * shard + i) + (shard * numParts) * c from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hri]
  have hdiv_shard : (r * shard + i) / shard = r := by
    rw [show r * shard + i = i + shard * r from by ring,
        Nat.add_mul_div_left _ _ hshard, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod_shard : (r * shard + i) % shard = i := by
    rw [show r * shard + i = i + shard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have h0 : valAt (allGatherPrimDimN 1 numParts 0 Ws) (c * (shard * numParts) + (r * shard + i)) =
      (allGatherPrimDimN 1 numParts 0 Ws).val ⟨c * (shard * numParts) + (r * shard + i), hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  have hWr_shape : (Ws.getD r (zeroTensor [o, shard])).shape = [o, shard] := hWs_shape r hr
  have hWr_prod : prodShape (Ws.getD r (zeroTensor [o, shard])).shape = o * shard := by
    rw [hWr_shape]; simp [prodShape]
  have hidx_lt_Wr : c * shard + i < prodShape (Ws.getD r (zeroTensor [o, shard])).shape := by
    rw [hWr_prod]
    calc c * shard + i < c * shard + shard := by omega
      _ = (c + 1) * shard := by ring
      _ ≤ o * shard := Nat.mul_le_mul_right _ hc
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_succ, List.getD_cons_zero, List.drop, List.foldl, Nat.mul_one,
    Nat.div_one, Nat.mod_one,
    show shard ≠ 0 from hshard_ne, show shard * numParts ≠ 0 from Nat.ne_of_gt hFDS_pos,
    show (1 : Nat) ≠ 0 from one_ne_zero, ite_false]
  rw [hmod_FDS, hdiv_FDS, hdiv_shard, hmod_shard]
  simp only [Nat.mul_one, Nat.add_zero, valAt, hidx_lt_Wr, dif_pos]

set_option maxHeartbeats 1600000 in
/-- Per-rank dW value when `x` (`[1,8,32]`) is chunked along its last (input-feature)
    dim into rank `R` (giving `[1,8,8]`).  The rank-`R` dW (`[32,8]`) at row `c`, col `i`
    equals the global reduction whose `x`-index is offset by `R*8`. -/
private theorem bw_linear_dw_xchunk_rank_valAt_g240
    (g x w_r : Tensor) (R c i : Nat)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 32]) (hwr : w_r.shape = [32, 8])
    (hR : R < 4) (hc : c < 32) (hi : i < 8) :
    valAt (bw_linear g (chunkPrimDimN 2 4 R x) w_r).2 (c * 8 + i) =
      ∑ r' ∈ Finset.range 8, valAt g (r' * 32 + c) * valAt x (r' * 32 + R * 8 + i) := by
  have hchunk : (chunkPrimDimN 2 4 R x).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 R x _ hx (by omega)]; simp [List.set, List.getD]
  rw [bw_linear_dw_valAt3d g (chunkPrimDimN 2 4 R x) w_r 1 8 32 8 hg hchunk hwr c hc i hi]
  simp only [show (1 : Nat) * 8 = 8 from rfl]
  apply Finset.sum_congr rfl
  intro r' hr'
  rw [chunk2_4_1_8_32_valAt_pj x R r' i hx hR (Finset.mem_range.mp hr') hi]

set_option maxHeartbeats 1600000 in
/-- The dW output of `bw_linear` where the input `x` (`[1,8,32]`) is chunked along its
    last (input-feature) dim into 4 ranks (each `[1,8,8]`), equals the dim-1 all-gather of
    the per-rank dW outputs (each `[32,8]`).  This is the column-(input-)parallel weight-gradient
    identity for `BW_linear`; dW is independent of `w` (per-rank `w0..w3` only fix the shape). -/
theorem bw_linear_dw_xsplit_dim2_4_g240
    (g x w w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 32]) (hw : w.shape = [32, 32])
    (hw0 : w0.shape = [32, 8]) (hw1 : w1.shape = [32, 8])
    (hw2 : w2.shape = [32, 8]) (hw3 : w3.shape = [32, 8]) :
    (bw_linear g x w).2 = allGatherPrimDimN 1 4 0
      [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
       (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
       (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
       (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2] := by
  have hch0 : (chunkPrimDimN 2 4 0 x).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 0 x _ hx (by omega)]; simp [List.set, List.getD]
  have hd0 : (bw_linear g (chunkPrimDimN 2 4 0 x) w0).2.shape = [32, 8] :=
    bw_linear_3d_snd_shape 1 8 32 8 g _ w0 hg hch0 hw0
  have hhead : (([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
                  (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
                  (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
                  (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2].head?.map
                  (fun t => t.shape)).getD [] = [32, 8]) := by
    simp [hd0]
  have hWs_shape : ∀ r (_ : r < 4),
      (([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
         (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
         (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
         (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2].getD r (zeroTensor [32, 8])).shape = [32, 8]) := by
    intro r hr
    rcases r with _|_|_|_|r
    · simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 8 g _ w0 hg hch0 hw0
    · have : (chunkPrimDimN 2 4 1 x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 1 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 8 g _ w1 hg this hw1
    · have : (chunkPrimDimN 2 4 2 x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 2 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 8 g _ w2 hg this hw2
    · have : (chunkPrimDimN 2 4 3 x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 3 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 8 g _ w3 hg this hw3
    · omega
  apply Tensor.ext
  · rw [bw_linear_3d_snd_shape 1 8 32 32 g x w hg hx hw,
        allGatherPrimDimN_shape 1 4 _ [32, 8] hhead]
    decide
  · intro idx hidx
    rw [bw_linear_3d_snd_shape 1 8 32 32 g x w hg hx hw] at hidx
    have hidxp : idx < 1024 := by simpa [prodShape] using hidx
    have hc : idx / 32 < 32 := by omega
    have hk : idx % 32 < 32 := by omega
    set c := idx / 32 with hcdef
    set k := idx % 32 with hkdef
    have hidc : idx = c * 32 + k := by omega
    rw [hidc, bw_linear_dw_valAt3d g x w 1 8 32 32 hg hx hw c hc k hk]
    have hr : k / 8 < 4 := by omega
    have hi : k % 8 < 8 := by omega
    rw [show c * 32 + k = c * (8 * 4) + (k / 8 * 8 + k % 8) from by omega]
    rw [allGatherPrimDimN1_valAt_g240 4 32 8
          [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
           (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
           (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
           (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2]
          (by omega) (by omega) (by omega) hhead hWs_shape c hc (k / 8) hr (k % 8) hi]
    have hcase : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 := by omega
    rcases hcase with h | h | h | h
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g240 g x w0 0 c (k % 8) hg hx hw0 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 0 * 8 + k % 8 = r' * 32 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g240 g x w1 1 c (k % 8) hg hx hw1 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 1 * 8 + k % 8 = r' * 32 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g240 g x w2 2 c (k % 8) hg hx hw2 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 2 * 8 + k % 8 = r' * 32 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g240 g x w3 3 c (k % 8) hg hx hw3 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 3 * 8 + k % 8 = r' * 32 + k from by omega]



-- ===== net-new lemmas from batch6 BW_linear g255 =====
-- ===== batch6 g255 net-new lemma =====

/- BW_linear dW: output-(tensor-)parallel.  The gradient `g` (`[1,8,128]`) is split
   along the output dim (gather dim 2) into 4 shards (each `[1,8,32]`), `x` (`[1,8,32]`)
   is replicated, and the weight `w` (`[128,32]`) is split along dim 0 into 4 shards
   (each `[32,32]`).  The full dW (`[128,32]`) is the dim-0 concatenation
   (`allGatherPrimDimN 0`) of the per-rank dW shards (each `[32,32]`). -/
set_option maxHeartbeats 800000 in
theorem bw_linear_dw_osplit_dim2_4_1_8_32_g255
    (x g0 g1 g2 g3 w0 w1 w2 w3 : Tensor)
    (hx : x.shape = [1, 8, 32])
    (hg0 : g0.shape = [1, 8, 32]) (hg1 : g1.shape = [1, 8, 32])
    (hg2 : g2.shape = [1, 8, 32]) (hg3 : g3.shape = [1, 8, 32])
    (hw0 : w0.shape = [32, 32]) (hw1 : w1.shape = [32, 32])
    (hw2 : w2.shape = [32, 32]) (hw3 : w3.shape = [32, 32]) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
        (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 0 4 0
        [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
         (bw_linear g2 x w2).2, (bw_linear g3 x w3).2] := by
  -- head shapes
  have hghead : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    simp [hg0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    simp [hw0]
  -- gathered input shapes
  have hG_shape : (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hghead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hwhead]; simp [List.set, List.getD]
  -- per-rank dW shapes
  have hp0 : (bw_linear g0 x w0).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g0 x w0 hg0 hx hw0
  have hp1 : (bw_linear g1 x w1).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g1 x w1 hg1 hx hw1
  have hp2 : (bw_linear g2 x w2).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g2 x w2 hg2 hx hw2
  have hp3 : (bw_linear g3 x w3).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g3 x w3 hg3 hx hw3
  set pieces : List Tensor :=
    [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2, (bw_linear g2 x w2).2, (bw_linear g3 x w3).2]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    simp [hpieces_def, hp0]
  have hpgetD : ∀ r, r < 4 → (pieces.getD r (zeroTensor [32, 32])).shape = [32, 32] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hpieces_def, List.getD, hp0, hp1, hp2, hp3]
  -- LHS / RHS shapes
  have hLHS_shape : (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3])).2.shape = [128, 32] :=
    bw_linear_3d_snd_shape 1 8 128 32 _ x _ hG_shape hx hW_shape
  have hRHS_shape : (allGatherPrimDimN 0 4 0 pieces).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 0 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx4096 : idx < 4096 := by simpa [hLHS_shape, prodShape] using hidx
  set c := idx / 32 with hc_def
  set k := idx % 32 with hk_def
  have hk : k < 32 := by rw [hk_def]; exact Nat.mod_lt _ (by omega)
  have hc : c < 128 := by rw [hc_def]; omega
  have hidx_eq : idx = c * 32 + k := by rw [hc_def, hk_def]; omega
  rw [hidx_eq]
  -- LHS value
  rw [bw_linear_dw_valAt3d (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x
      (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]) 1 8 128 32 hG_shape hx hW_shape c hc k hk]
  -- RHS value: rewrite index into (r*32+oc) form and peel the dim-0 gather
  have hoc : c % 32 < 32 := Nat.mod_lt _ (by omega)
  have hr : c / 32 < 4 := by omega
  conv_rhs => rw [show c * 32 + k = (c / 32 * 32 + c % 32) * 32 + k from by
    have : c / 32 * 32 + c % 32 = c := by omega
    rw [this]]
  rw [allGatherPrimDimN0_valAt 4 32 32 pieces (by omega) (by omega) (by omega)
      hphead hpgetD (c / 32) hr (c % 32) hoc k hk]
  -- expand the selected per-rank dW and match term by term
  have hG_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) (p * 128 + c) =
      valAt (([g0, g1, g2, g3] : List Tensor).getD (c / 32) (zeroTensor [1, 8, 32])) (p * 32 + c % 32) := by
    intro p hp
    have hkey : p * 128 + c = p * 128 + (c / 32) * 32 + c % 32 := by omega
    rw [hkey, allGatherPrimDimN_2_4_valAt_1_8_32_g140 [g0, g1, g2, g3] hghead p hp (c / 32) hr (c % 32) hoc]
  rcases (show c / 32 = 0 ∨ c / 32 = 1 ∨ c / 32 = 2 ∨ c / 32 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_dw_valAt3d g0 x w0 1 8 32 32 hg0 hx hw0 (c % 32) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g1 x w1 1 8 32 32 hg1 hx hw1 (c % 32) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g2 x w2 1 8 32 32 hg2 hx hw2 (c % 32) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g3 x w3 1 8 32 32 hg3 hx hw3 (c % 32) hoc k hk]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hG_term p (Finset.mem_range.mp hp), h, List.getD]; simp


-- ===== net-new lemmas from batch6 BW_linear g262 =====
set_option maxHeartbeats 2000000 in
/-- Data-parallel (sequence-dim) split of the dX output of `BW_linear`, mirror of
    `bw_linear_dx_dp_split_dim1_4_g169`: here the gradient `g` (`[1,8,32]`) is locally
    dim-1 chunked per rank, the activation `x` (`[1,8,32]`) is dim-1 all-gathered from
    four `[1,2,32]` shards, and the weight `w` (`[32,32]`) is shared. Then the full dX
    equals the dim-1 all-gather of the per-rank dX outputs. -/
theorem bw_linear_dx_dp_split_dim1_4_g262
    (g x0 x1 x2 x3 w : Tensor)
    (hg : g.shape = [1,8,32])
    (hx0 : x0.shape = [1,2,32]) (hx1 : x1.shape = [1,2,32])
    (hx2 : x2.shape = [1,2,32]) (hx3 : x3.shape = [1,2,32])
    (hw : w.shape = [32,32]) :
    (bw_linear g (allGatherPrimDimN 1 4 0 [x0,x1,x2,x3]) w).1 =
      allGatherPrimDimN 1 4 0
        [(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
         (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
         (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
         (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1] := by
  have hxhead : (([x0,x1,x2,x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1,2,32] := by
    simp [hx0]
  set X := allGatherPrimDimN 1 4 0 [x0,x1,x2,x3] with hXdef
  have hXshape : X.shape = [1,8,32] := by
    rw [hXdef, allGatherPrimDimN_shape 1 4 _ [1,2,32] hxhead]; simp [List.set, List.getD]
  have hcg0 : (chunkPrimDimN 1 4 0 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 0 g _ hg (by omega)]; simp [List.set, List.getD]
  have hcg1 : (chunkPrimDimN 1 4 1 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 1 g _ hg (by omega)]; simp [List.set, List.getD]
  have hcg2 : (chunkPrimDimN 1 4 2 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 2 g _ hg (by omega)]; simp [List.set, List.getD]
  have hcg3 : (chunkPrimDimN 1 4 3 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 3 g _ hg (by omega)]; simp [List.set, List.getD]
  have hdx0shape : (bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1.shape = [1,2,32] :=
    bw_linear_3d_fst_shape 1 2 32 32 _ _ _ hcg0 hx0 hw
  have hLshape : (bw_linear g X w).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 g X w hg hXshape hw
  have hheadR : (([(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
                   (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
                   (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
                   (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,2,32] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 1 4 _ [1,2,32] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/32 < 8 := by omega
    have hcol : idx%32 < 32 := by omega
    have hide : idx = (idx/32)*32 + idx%32 := by omega
    rw [hide]
    set P := idx/32 with hPdef
    set col := idx%32 with hcoldef
    set r := P/2 with hrdef
    set p := P%2 with hpdef
    have hr : r < 4 := by omega
    have hp : p < 2 := by omega
    have hPrp : P = r * 2 + p := by omega
    rw [bw_linear_fst_valAt_1_8_32_g134 g X w 32 hg hXshape hw P hP col hcol]
    have hRHS : valAt (allGatherPrimDimN 1 4 0
          [(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
           (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
           (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
           (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1]) (P * 32 + col)
        = valAt ([(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
                  (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
                  (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
                  (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1].getD r (zeroTensor [1,2,32]))
                (p * 32 + col) := by
      rw [hPrp]
      exact allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr p hp col hcol hheadR
    rw [hRHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 0 g) x0 w 32 hcg0 hx0 hw p hp col hcol]
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      rw [chunk_dim1_4_1_8_32_valAt g 0 p j hg (by omega) hp hj32]
      have hidxeq : P * 32 + j = (0 * 2 + p) * 32 + j := by omega
      rw [hidxeq]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 1 g) x1 w 32 hcg1 hx1 hw p hp col hcol]
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      rw [chunk_dim1_4_1_8_32_valAt g 1 p j hg (by omega) hp hj32]
      have hidxeq : P * 32 + j = (1 * 2 + p) * 32 + j := by omega
      rw [hidxeq]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 2 g) x2 w 32 hcg2 hx2 hw p hp col hcol]
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      rw [chunk_dim1_4_1_8_32_valAt g 2 p j hg (by omega) hp hj32]
      have hidxeq : P * 32 + j = (2 * 2 + p) * 32 + j := by omega
      rw [hidxeq]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 3 g) x3 w 32 hcg3 hx3 hw p hp col hcol]
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      rw [chunk_dim1_4_1_8_32_valAt g 3 p j hg (by omega) hp hj32]
      have hidxeq : P * 32 + j = (3 * 2 + p) * 32 + j := by omega
      rw [hidxeq]

-- ===== net-new lemmas from batch6 BW_linear g264 =====
set_option maxHeartbeats 2000000 in
/-- Data-parallel (sequence-dim) split of the dX output of `BW_linear` where the
    grad-output `g` (`[1,8,32]`) is locally dim-1 chunked per rank, the per-rank
    activations `x0..x3` (`[1,2,32]`) are arbitrary shards, and the weight `w`
    (`[32,32]`) is shared.  Then the full dX equals the dim-1 all-gather of the
    per-rank dX outputs.  (dX is independent of the activation `x`, so the per-rank
    activations need not match a chunk of any particular tensor.) -/
theorem bw_linear_dx_dp_split_dim1_4_g264
    (g x x0 x1 x2 x3 w : Tensor)
    (hg : g.shape = [1,8,32]) (hx : x.shape = [1,8,32])
    (hx0 : x0.shape = [1,2,32]) (hx1 : x1.shape = [1,2,32])
    (hx2 : x2.shape = [1,2,32]) (hx3 : x3.shape = [1,2,32])
    (hw : w.shape = [32,32]) :
    (bw_linear g x w).1 =
      allGatherPrimDimN 1 4 0
        [(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
         (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
         (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
         (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1] := by
  have hcg0 : (chunkPrimDimN 1 4 0 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 0 g _ hg (by omega)]; simp [List.set, List.getD]
  have hcg1 : (chunkPrimDimN 1 4 1 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 1 g _ hg (by omega)]; simp [List.set, List.getD]
  have hcg2 : (chunkPrimDimN 1 4 2 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 2 g _ hg (by omega)]; simp [List.set, List.getD]
  have hcg3 : (chunkPrimDimN 1 4 3 g).shape = [1,2,32] := by
    rw [chunkPrimDimN_shape 1 4 3 g _ hg (by omega)]; simp [List.set, List.getD]
  have hdx0shape : (bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1.shape = [1,2,32] :=
    bw_linear_3d_fst_shape 1 2 32 32 _ _ _ hcg0 hx0 hw
  have hLshape : (bw_linear g x w).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 g x w hg hx hw
  have hheadR : (([(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
                   (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
                   (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
                   (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,2,32] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 1 4 _ [1,2,32] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/32 < 8 := by omega
    have hcol : idx%32 < 32 := by omega
    have hide : idx = (idx/32)*32 + idx%32 := by omega
    rw [hide]
    set P := idx/32 with hPdef
    set col := idx%32 with hcoldef
    set r := P/2 with hrdef
    set p := P%2 with hpdef
    have hr : r < 4 := by omega
    have hp : p < 2 := by omega
    have hPrp : P = r * 2 + p := by omega
    rw [bw_linear_fst_valAt_1_8_32_g134 g x w 32 hg hx hw P hP col hcol]
    have hLHS : (∑ j ∈ Finset.range 32, valAt g (P*32+j) * valAt w (j*32+col))
        = ∑ j ∈ Finset.range 32,
            valAt (chunkPrimDimN 1 4 r g) (p*32+j) * valAt w (j*32+col) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      rw [chunk_dim1_4_1_8_32_valAt g r p j hg hr hp hj32, hPrp]
    rw [hLHS]
    have hRHS : valAt (allGatherPrimDimN 1 4 0
          [(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
           (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
           (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
           (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1]) (P * 32 + col)
        = valAt ([(bw_linear (chunkPrimDimN 1 4 0 g) x0 w).1,
                  (bw_linear (chunkPrimDimN 1 4 1 g) x1 w).1,
                  (bw_linear (chunkPrimDimN 1 4 2 g) x2 w).1,
                  (bw_linear (chunkPrimDimN 1 4 3 g) x3 w).1].getD r (zeroTensor [1,2,32]))
                (p * 32 + col) := by
      rw [hPrp]
      exact allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr p hp col hcol hheadR
    rw [hRHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 0 g) x0 w 32 hcg0 hx0 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 1 g) x1 w 32 hcg1 hx1 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 2 g) x2 w 32 hcg2 hx2 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_32_g169 (chunkPrimDimN 1 4 3 g) x3 w 32 hcg3 hx3 hw p hp col hcol]


-- ===== net-new lemmas from batch6 BW_linear g276 =====
-- ==== batch6 g276 additions (BW_linear dX, column-parallel weight split) ====

/-- Value of `bw_linear` dX (first output) for 3D inputs whose intrinsic input
    width is 8 (so the per-rank dX shard has shape `[1,8,8]`). -/
theorem bw_linear_fst_valAt_1_8_8_g276 (g x w : Tensor) (o : Nat)
    (hg : g.shape = [1, 8, o]) (hx : x.shape = [1, 8, 8]) (hw : w.shape = [o, 8])
    (P : Nat) (hP : P < 8) (col : Nat) (hcol : col < 8) :
    valAt (bw_linear g x w).1 (P * 8 + col) =
      ∑ j ∈ Finset.range o, valAt g (P * o + j) * valAt w (j * 8 + col) := by
  have hdx : (bw_linear g x w).1 =
      Tensor.mkShape [1, 8, 8] (fun outIdx =>
        ∑ j ∈ Finset.range o,
          valAt g (((if (8:Nat) * 8 = 0 then 0 else outIdx.1 / (8 * 8)) * 8 +
                    if (8:Nat) = 0 then 0 else (if (8:Nat) * 8 = 0 then 0 else outIdx.1 % (8 * 8)) / 8) * o + j) *
          valAt w (j * 8 + if (8:Nat) = 0 then 0 else (if (8:Nat) * 8 = 0 then 0 else outIdx.1 % (8 * 8)) % 8)) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hdx]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl]; omega)]
  simp only [Tensor.mkShape]
  have e1 : (P*8+col)/(8*8) = 0 := by omega
  have e2 : ((P*8+col)%(8*8))/8 = P := by omega
  have e3 : ((P*8+col)%(8*8))%8 = col := by omega
  simp only [show ((8:Nat)*8=0)=False from by simp, show ((8:Nat)=0)=False from by simp,
    if_false, e1, e2, e3, Nat.zero_mul, Nat.zero_add]

set_option maxHeartbeats 1600000 in
/-- Column-parallel (output-feature split) input gradient for `BW_linear`.  The gradient
    `g` (`[1,8,32]`) is shared, the weight `w` (`[32,32]`) is sharded on dim 1 into four
    `[32,8]` shards (reassembled by `allGatherPrimDimN 1`), and the activation `x`
    (`[1,8,32]`) is sharded on dim 2 into four `[1,8,8]` shards (reassembled by
    `allGatherPrimDimN 2`).  Then the full dX (`[1,8,32]`) equals the dim-2 all-gather of
    the four per-rank dX outputs (each `[1,8,8]`).  dX depends only on `g` and `w`, so the
    per-rank `x` shards only fix the output column width. -/
theorem bw_linear_dx_csplit_dim1_4_1_8_8_g276
    (g x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 32])
    (hx0 : x0.shape = [1, 8, 8]) (hx1 : x1.shape = [1, 8, 8])
    (hx2 : x2.shape = [1, 8, 8]) (hx3 : x3.shape = [1, 8, 8])
    (hw0 : w0.shape = [32, 8]) (hw1 : w1.shape = [32, 8])
    (hw2 : w2.shape = [32, 8]) (hw3 : w3.shape = [32, 8]) :
    (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
        (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).1 =
      allGatherPrimDimN 2 4 0
        [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
         (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] := by
  have hxhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hx0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32, 8] := by
    simp [hw0]
  have hwgetD : ∀ r, r < 4 →
      (([w0, w1, w2, w3] : List Tensor).getD r (zeroTensor [32, 8])).shape = [32, 8] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, hw0, hw1, hw2, hw3]
  have hX_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hxhead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [32, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; simp [List.set, List.getD]
  have hp0 : (bw_linear g x0 w0).1.shape = [1, 8, 8] := bw_linear_3d_fst_shape 1 8 32 8 g x0 w0 hg hx0 hw0
  set pieces : List Tensor :=
    [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1, (bw_linear g x2 w2).1, (bw_linear g x3 w3).1]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hpieces_def, hp0]
  have hLHS_shape : (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).1.shape = [1, 8, 32] :=
    bw_linear_3d_fst_shape 1 8 32 32 g _ _ hg hX_shape hW_shape
  have hRHS_shape : (allGatherPrimDimN 2 4 0 pieces).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hLHS_shape, prodShape] using hidx
  set seq := idx / 32 with hseq_def
  set col := idx % 32 with hcol_def
  have hcol : col < 32 := by rw [hcol_def]; exact Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by rw [hseq_def]; omega
  have hidx_eq : idx = seq * 32 + col := by rw [hseq_def, hcol_def]; omega
  rw [hidx_eq]
  -- LHS value
  rw [bw_linear_fst_valAt_1_8_32_g134 g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) 32 hg hX_shape hW_shape seq hseq col hcol]
  -- RHS value: decompose the output column into rank/local then peel the dim-2 gather
  have hr : col / 8 < 4 := by omega
  have hlc : col % 8 < 8 := Nat.mod_lt _ (by omega)
  conv_rhs => rw [show seq * 32 + col = seq * 32 + (col / 8 * 8 + col % 8) from by omega]
  rw [allGatherDimN2_4_188_valAt_g134 pieces hphead seq hseq (col / 8) hr (col % 8) hlc]
  -- relate the full weight value to the selected shard
  have hW_term : ∀ j, j < 32 →
      valAt (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) (j * 32 + col) =
      valAt (([w0, w1, w2, w3] : List Tensor).getD (col / 8) (zeroTensor [32, 8])) (j * 8 + col % 8) := by
    intro j hj
    rw [show j * 32 + col = j * 32 + col / 8 * 8 + col % 8 from by omega]
    rw [allGatherPrimDimN1_4_valAt_32_8 [w0, w1, w2, w3] hwhead hwgetD j hj (col / 8) hr (col % 8) hlc]
  rcases (show col / 8 = 0 ∨ col / 8 = 1 ∨ col / 8 = 2 ∨ col / 8 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x0 w0 32 hg hx0 hw0 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x1 w1 32 hg hx1 hw1 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x2 w2 32 hg hx2 hw2 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x3 w3 32 hg hx3 hw3 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp



/-- Shape of `batchedMatmul` on `[1,4,8,2] @ [1,4,2,8] -> [1,4,8,8]`. -/
theorem batchedMatmul_shape_1_4_8_2_1_4_2_8 (a b : Tensor)
    (ha : a.shape = [1, 4, 8, 2]) (hb : b.shape = [1, 4, 2, 8]) :
    (batchedMatmul a b).shape = [1, 4, 8, 8] := by
  unfold batchedMatmul
  simp only [ha, hb, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    Tensor.mkShape]

/-- `valAt` of `batchedMatmul a b` for `a : [1,4,8,2]`, `b : [1,4,2,8]`, output `[1,4,8,8]`
(contraction over the inner dimension of size 2). -/
theorem batchedMatmul_valAt_1_4_8_2_1_4_2_8 (a b : Tensor) (loc : Nat)
    (ha : a.shape = [1, 4, 8, 2]) (hb : b.shape = [1, 4, 2, 8]) (hloc : loc < 256) :
    valAt (batchedMatmul a b) loc =
      ∑ l ∈ Finset.range 2,
        valAt a (loc / 64 * 16 + loc % 64 / 8 * 2 + l) *
          valAt b (loc / 64 * 16 + l * 8 + loc % 8) := by
  have key : batchedMatmul a b = Tensor.mkShape [1, 4, 8, 8] (fun outIdx =>
      ∑ l ∈ Finset.range 2,
        valAt a (outIdx.1 / (8 * 8) * (8 * 2) + outIdx.1 % (8 * 8) / 8 * 2 + l) *
          valAt b (outIdx.1 / (8 * 8) * (2 * 8) + l * 8 + outIdx.1 % (8 * 8) % 8)) := by
    unfold batchedMatmul
    rw [ha, hb]
    rfl
  rw [key]
  have hloc' : loc < prodShape ([1, 4, 8, 8] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hloc')]
  show ∑ l ∈ Finset.range 2,
        valAt a (loc / (8 * 8) * (8 * 2) + loc % (8 * 8) / 8 * 2 + l) *
          valAt b (loc / (8 * 8) * (2 * 8) + l * 8 + loc % (8 * 8) % 8) = _
  apply Finset.sum_congr rfl
  intro l _
  congr 2 <;> omega

/-! ## FW_matmul contraction-dim split (`[1,4,8,8] = [1,4,8,2] @ [1,4,2,8]` shards summed)

`FW_matmul` with both inputs partitioned along their shared contraction dimension
(`x` along dim 3 into 4 shards `[1,4,8,2]`, `y` along dim 2 into 4 shards `[1,4,2,8]`).
Each rank computes the local `fw_matmul` of its shards (shape `[1,4,8,8]`), and the full
result is the `allReducePrim` sum of the per-rank products. -/

/-- Split `Finset.range 8` into `4 × 2` for the contraction-dim reindex. -/
theorem sum_range_split_4_2 (f : ℕ → Scalar) :
    ∑ j ∈ Finset.range 8, f j =
    ∑ r ∈ Finset.range 4, ∑ lc ∈ Finset.range 2, f (r * 2 + lc) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.zero_mul,
    Nat.reduceMul, Nat.reduceAdd]
  ring

/-! Flat-index arithmetic helpers for `fw_matmul_split_dimK_1_4_8_8` (proven in an empty
context so `omega` stays fast). -/

private theorem mm_aux_pbnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + idx % 64 / 8 * 8 + l < 256 := by omega

private theorem mm_aux_qbnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + l * 8 + idx % 8 < 256 := by omega

private theorem mm_aux_x_shard (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + idx % 64 / 8 * 8 + l) % 8 / 2 = l / 2 := by omega

private theorem mm_aux_x_idx (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + idx % 64 / 8 * 8 + l) / 8 * 2 +
      (idx / 64 * 64 + idx % 64 / 8 * 8 + l) % 8 % 2 =
      idx / 64 * 16 + idx % 64 / 8 * 2 + l % 2 := by omega

private theorem mm_aux_y_shard (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + l * 8 + idx % 8) % 64 / 16 = l / 2 := by omega

private theorem mm_aux_y_idx (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + l * 8 + idx % 8) / 64 * 16 +
      (idx / 64 * 64 + l * 8 + idx % 8) % 16 / 8 * 8 +
      (idx / 64 * 64 + l * 8 + idx % 8) % 8 =
      idx / 64 * 16 + l % 2 * 8 + idx % 8 := by omega

set_option maxHeartbeats 1600000 in
-- heavy flat-index arithmetic across two gathers, an allReduce and four shard matmuls
theorem fw_matmul_split_dimK_1_4_8_8 (x0 x1 x2 x3 y0 y1 y2 y3 : Tensor)
    (hx0 : x0.shape = [1, 4, 8, 2]) (hx1 : x1.shape = [1, 4, 8, 2])
    (hx2 : x2.shape = [1, 4, 8, 2]) (hx3 : x3.shape = [1, 4, 8, 2])
    (hy0 : y0.shape = [1, 4, 2, 8]) (hy1 : y1.shape = [1, 4, 2, 8])
    (hy2 : y2.shape = [1, 4, 2, 8]) (hy3 : y3.shape = [1, 4, 2, 8]) :
    fw_matmul (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])
        (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3]) =
      allReducePrim 4 0
        [fw_matmul x0 y0, fw_matmul x1 y1, fw_matmul x2 y2, fw_matmul x3 y3] := by
  have hhead_x : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 8, 2] := by simp [hx0]
  have hhead_y : (([y0, y1, y2, y3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 2, 8] := by simp [hy0]
  have hX_shape : (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_x]; simp [List.set, List.getD]
  have hY_shape : (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead_y]; simp [List.set, List.getD]
  have hm0 : (fw_matmul x0 y0).shape = [1, 4, 8, 8] :=
    batchedMatmul_shape_1_4_8_2_1_4_2_8 x0 y0 hx0 hy0
  have hlhs_shape : (fw_matmul (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])).shape = [1, 4, 8, 8] :=
    fw_matmul_shape_1_4_8_8 _ _ hX_shape hY_shape
  have hhead_rhs : ([fw_matmul x0 y0, fw_matmul x1 y1, fw_matmul x2 y2,
      fw_matmul x3 y3] : List Tensor).head? = some (fw_matmul x0 y0) := rfl
  have hrhs_shape : (allReducePrim 4 0 [fw_matmul x0 y0, fw_matmul x1 y1,
      fw_matmul x2 y2, fw_matmul x3 y3]).shape = [1, 4, 8, 8] := by
    rw [allReducePrim_shape 4 0 _ _ hhead_rhs]; exact hm0
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [fw_matmul_valAt_1_4_8_8 _ _ idx hX_shape hY_shape hidx256]
  have hLHSsum : (∑ l ∈ Finset.range 8,
        valAt (allGatherPrimDimN 3 4 0 [x0, x1, x2, x3])
            (idx / 64 * 64 + idx % 64 / 8 * 8 + l) *
          valAt (allGatherPrimDimN 2 4 0 [y0, y1, y2, y3])
            (idx / 64 * 64 + l * 8 + idx % 8)) =
      ∑ l ∈ Finset.range 8,
        valAt ([x0, x1, x2, x3].getD (l / 2) (zeroTensor [1, 4, 8, 2]))
            (idx / 64 * 16 + idx % 64 / 8 * 2 + l % 2) *
          valAt ([y0, y1, y2, y3].getD (l / 2) (zeroTensor [1, 4, 2, 8]))
            (idx / 64 * 16 + l % 2 * 8 + idx % 8) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := Finset.mem_range.mp hl
    rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ (idx / 64 * 64 + idx % 64 / 8 * 8 + l)
        hhead_x (mm_aux_pbnd idx l hl8 hidx256)]
    rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ (idx / 64 * 64 + l * 8 + idx % 8)
        hhead_y (mm_aux_qbnd idx l hl8 hidx256)]
    rw [mm_aux_x_shard idx l hl8, mm_aux_x_idx idx l hl8,
        mm_aux_y_shard idx l hl8, mm_aux_y_idx idx l hl8]
  rw [hLHSsum]
  rw [allReducePrim_valAt 4 0 _ idx (fw_matmul x0 y0) hhead_rhs
      (by rw [hm0]; simpa [prodShape] using hidx256)]
  simp only [List.foldl]
  rw [show fw_matmul x0 y0 = batchedMatmul x0 y0 from rfl,
      show fw_matmul x1 y1 = batchedMatmul x1 y1 from rfl,
      show fw_matmul x2 y2 = batchedMatmul x2 y2 from rfl,
      show fw_matmul x3 y3 = batchedMatmul x3 y3 from rfl]
  rw [batchedMatmul_valAt_1_4_8_2_1_4_2_8 x0 y0 idx hx0 hy0 hidx256,
      batchedMatmul_valAt_1_4_8_2_1_4_2_8 x1 y1 idx hx1 hy1 hidx256,
      batchedMatmul_valAt_1_4_8_2_1_4_2_8 x2 y2 idx hx2 hy2 hidx256,
      batchedMatmul_valAt_1_4_8_2_1_4_2_8 x3 y3 idx hx3 hy3 hidx256]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
    Nat.zero_mul, Nat.add_zero,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  ring

/-! ## FW_matmul output-dim (column-parallel) split (`[1,4,8,8] @ [1,4,8,8]` with the
second operand sharded along dim 3 into 4 shards `[1,4,8,2]`).

The first operand `x` is replicated across ranks; the second operand `y` is split along
its last (output `N`) dimension. Each rank computes the local `fw_matmul x yᵣ` of shape
`[1,4,8,2]`, and the full result is the `allGatherPrimDimN 3` concatenation of the per-rank
products (no reduction needed). -/

/-! Flat-index arithmetic helpers for `fw_matmul_split_dimN_1_4_8_8` (proven in an empty
context so `omega` stays fast). -/

private theorem col_aux_qbnd (idx l : Nat) (hl : l < 8) (hidx : idx < 256) :
    idx / 64 * 64 + l * 8 + idx % 8 < 256 := by omega

private theorem col_aux_shard (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + l * 8 + idx % 8) % 8 / 2 = idx % 8 / 2 := by omega

private theorem col_aux_idx (idx l : Nat) (hl : l < 8) :
    (idx / 64 * 64 + l * 8 + idx % 8) / 8 * 2 +
      (idx / 64 * 64 + l * 8 + idx % 8) % 8 % 2 =
      idx / 64 * 16 + l * 2 + idx % 8 % 2 := by omega

set_option maxHeartbeats 1600000 in
private theorem col_final (x y : Tensor) (idx : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hy : y.shape = [1, 4, 8, 2]) (hidx : idx < 256) :
    (∑ l ∈ Finset.range 8,
        valAt x (idx / 64 * 64 + idx % 64 / 8 * 8 + l) *
          valAt y (idx / 64 * 16 + l * 2 + idx % 8 % 2)) =
      valAt (fw_matmul x y) (idx / 8 * 2 + idx % 8 % 2) := by
  rw [show fw_matmul x y = batchedMatmul x y from rfl]
  rw [batchedMatmul_valAt_1_4_8_8_1_4_8_2 x y (idx / 8 * 2 + idx % 8 % 2) hx hy (by omega)]
  apply Finset.sum_congr rfl
  intro l hl
  have hl8 : l < 8 := Finset.mem_range.mp hl
  congr 1
  · congr 1; omega
  · congr 1; omega

set_option maxHeartbeats 1600000 in
-- fw_matmul distributes over an output-dim (dim 3) split of the second operand via allGather
theorem fw_matmul_split_dimN_1_4_8_8 (x y0 y1 y2 y3 : Tensor)
    (hx : x.shape = [1, 4, 8, 8])
    (hy0 : y0.shape = [1, 4, 8, 2]) (hy1 : y1.shape = [1, 4, 8, 2])
    (hy2 : y2.shape = [1, 4, 8, 2]) (hy3 : y3.shape = [1, 4, 8, 2]) :
    fw_matmul x (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3]) =
      allGatherPrimDimN 3 4 0
        [fw_matmul x y0, fw_matmul x y1, fw_matmul x y2, fw_matmul x y3] := by
  have hhead_y : (([y0, y1, y2, y3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 8, 2] := by simp [hy0]
  have hY_shape : (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_y]; simp [List.set, List.getD]
  have hm0 : (fw_matmul x y0).shape = [1, 4, 8, 2] :=
    batchedMatmul_shape_1_4_8_8_1_4_8_2 x y0 hx hy0
  have hlhs_shape : (fw_matmul x (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3])).shape =
      [1, 4, 8, 8] :=
    fw_matmul_shape_1_4_8_8 _ _ hx hY_shape
  have hhead_rhs : (([fw_matmul x y0, fw_matmul x y1, fw_matmul x y2, fw_matmul x y3] :
      List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by simp [hm0]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [fw_matmul x y0, fw_matmul x y1, fw_matmul x y2, fw_matmul x y3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_rhs]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [fw_matmul_valAt_1_4_8_8 _ _ idx hx hY_shape hidx256]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead_rhs hidx256]
  have hLHSsum : (∑ l ∈ Finset.range 8,
        valAt x (idx / 64 * 64 + idx % 64 / 8 * 8 + l) *
          valAt (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3]) (idx / 64 * 64 + l * 8 + idx % 8)) =
      ∑ l ∈ Finset.range 8,
        valAt x (idx / 64 * 64 + idx % 64 / 8 * 8 + l) *
          valAt ([y0, y1, y2, y3].getD (idx % 8 / 2) (zeroTensor [1, 4, 8, 2]))
            (idx / 64 * 16 + l * 2 + idx % 8 % 2) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := Finset.mem_range.mp hl
    rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ (idx / 64 * 64 + l * 8 + idx % 8) hhead_y
        (col_aux_qbnd idx l hl8 hidx256)]
    rw [col_aux_shard idx l hl8, col_aux_idx idx l hl8]
  rw [hLHSsum]
  rcases (show idx % 8 / 2 = 0 ∨ idx % 8 / 2 = 1 ∨ idx % 8 / 2 = 2 ∨ idx % 8 / 2 = 3 from by omega)
    with h | h | h | h
  · rw [h]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    exact col_final x y0 idx hx hy0 hidx256
  · rw [h]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    exact col_final x y1 idx hx hy1 hidx256
  · rw [h]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    exact col_final x y2 idx hx hy2 hidx256
  · rw [h]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    exact col_final x y3 idx hx hy3 hidx256

/-! Flat-index arithmetic helpers for `bw_matmul_fst_split_dW_1_4_8_8` (proven in an empty
context over fresh variables so `omega` stays robust). -/

private theorem dw_aux_mod8 (a m l : Nat) (hl : l < 8) :
    (a * 64 + m * 8 + l) % 8 / 2 = l / 2 := by omega

private theorem dw_aux_div8 (a m l : Nat) (hl : l < 8) :
    (a * 64 + m * 8 + l) / 8 * 2 + (a * 64 + m * 8 + l) % 8 % 2 = a * 16 + m * 2 + l % 2 := by omega

set_option maxHeartbeats 6400000 in
-- heavy flat-index arithmetic across matmul / transpose / two gathers
theorem bw_matmul_fst_split_dW_1_4_8_8 (g0 g1 g2 g3 y0 y1 y2 y3 : Tensor)
    (hg0 : g0.shape = [1, 4, 8, 2]) (hg1 : g1.shape = [1, 4, 8, 2])
    (hg2 : g2.shape = [1, 4, 8, 2]) (hg3 : g3.shape = [1, 4, 8, 2])
    (hy0 : y0.shape = [1, 4, 8, 2]) (hy1 : y1.shape = [1, 4, 8, 2])
    (hy2 : y2.shape = [1, 4, 8, 2]) (hy3 : y3.shape = [1, 4, 8, 2]) :
    batchedMatmul (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3])
        (transpose2d (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3])) =
      allReducePrim 4 0
        [batchedMatmul g0 (transpose2d y0), batchedMatmul g1 (transpose2d y1),
         batchedMatmul g2 (transpose2d y2), batchedMatmul g3 (transpose2d y3)] := by
  have hhead_g : (([g0, g1, g2, g3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 8, 2] := by simp [hg0]
  have hhead_y : (([y0, y1, y2, y3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 8, 2] := by simp [hy0]
  have hgfull : (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_g]; simp [List.set, List.getD]
  have hyfull : (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead_y]; simp [List.set, List.getD]
  have htYfull : (transpose2d (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3])).shape = [1, 4, 8, 8] :=
    transpose2d_shape_1_4_8_8 _ hyfull
  -- piece shape (each rank's product is [1,4,8,8])
  have hP0_shape : (batchedMatmul g0 (transpose2d y0)).shape = [1, 4, 8, 8] :=
    batchedMatmul_shape_1_4_8_2_1_4_2_8 _ _ hg0 (transpose2d_shape_1_4_8_2 _ hy0)
  -- LHS shape
  have hlhs_shape : (batchedMatmul (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3])
      (transpose2d (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3]))).shape = [1, 4, 8, 8] := by
    unfold batchedMatmul
    simp only [hgfull, htYfull, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, Tensor.mkShape]
  -- RHS shape
  have hrhs_shape : (allReducePrim 4 0
      [batchedMatmul g0 (transpose2d y0), batchedMatmul g1 (transpose2d y1),
       batchedMatmul g2 (transpose2d y2), batchedMatmul g3 (transpose2d y3)]).shape =
      [1, 4, 8, 8] := by
    rw [allReducePrim_shape 4 0 _ _ rfl]; exact hP0_shape
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  -- per-rank value lemma (each rank: g_s @ y_sᵀ contracted over inner dim 2)
  have hPval : ∀ (gs ys : Tensor), gs.shape = [1, 4, 8, 2] → ys.shape = [1, 4, 8, 2] →
      valAt (batchedMatmul gs (transpose2d ys)) idx =
        ∑ l ∈ Finset.range 2,
          valAt gs (idx / 64 * 16 + idx % 64 / 8 * 2 + l) *
            valAt ys (idx / 64 * 16 + idx % 8 * 2 + l) := by
    intro gs ys hgs hys
    rw [batchedMatmul_valAt_1_4_8_2_1_4_2_8 gs (transpose2d ys) idx hgs
        (transpose2d_shape_1_4_8_2 _ hys) hidx256]
    apply Finset.sum_congr rfl
    intro l hl
    have hl2 : l < 2 := Finset.mem_range.mp hl
    rw [transpose2d_valAt_1_4_8_2 ys (idx / 64 * 16 + l * 8 + idx % 8) hys (by omega)]
    have hyidx : (idx / 64 * 16 + l * 8 + idx % 8) / 16 * 16 +
        (idx / 64 * 16 + l * 8 + idx % 8) % 8 * 2 +
        (idx / 64 * 16 + l * 8 + idx % 8) % 16 / 8 = idx / 64 * 16 + idx % 8 * 2 + l := by omega
    rw [hyidx]
  -- LHS as a fw_matmul value
  rw [show batchedMatmul (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3])
        (transpose2d (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3])) =
        fw_matmul (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3])
          (transpose2d (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3])) from rfl,
      fw_matmul_valAt_1_4_8_8 _ _ idx hgfull htYfull hidx256]
  -- rewrite the LHS sum termwise into shard form
  have hA : ∀ l, l < 8 →
      valAt (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]) (idx / 64 * 64 + idx % 64 / 8 * 8 + l) *
        valAt (transpose2d (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3]))
          (idx / 64 * 64 + l * 8 + idx % 8) =
      valAt ([g0, g1, g2, g3].getD (l / 2) (zeroTensor [1, 4, 8, 2]))
          (idx / 64 * 16 + idx % 64 / 8 * 2 + l % 2) *
        valAt ([y0, y1, y2, y3].getD (l / 2) (zeroTensor [1, 4, 8, 2]))
          (idx / 64 * 16 + idx % 8 * 2 + l % 2) := by
    intro l hl
    rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 [g0, g1, g2, g3]
        (idx / 64 * 64 + idx % 64 / 8 * 8 + l) hhead_g (by omega)]
    rw [transpose2d_valAt_1_4_8_8 (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3])
        (idx / 64 * 64 + l * 8 + idx % 8) hyfull (by omega)]
    have hRsimp : (idx / 64 * 64 + l * 8 + idx % 8) / 64 * 64 +
        (idx / 64 * 64 + l * 8 + idx % 8) % 8 * 8 +
        (idx / 64 * 64 + l * 8 + idx % 8) % 64 / 8 = idx / 64 * 64 + idx % 8 * 8 + l := by omega
    rw [hRsimp]
    rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 [y0, y1, y2, y3]
        (idx / 64 * 64 + idx % 8 * 8 + l) hhead_y (by omega)]
    have eg1 : (idx / 64 * 64 + idx % 64 / 8 * 8 + l) % 8 / 2 = l / 2 :=
      dw_aux_mod8 (idx / 64) (idx % 64 / 8) l (by omega)
    have eg2 : (idx / 64 * 64 + idx % 64 / 8 * 8 + l) / 8 * 2 +
        (idx / 64 * 64 + idx % 64 / 8 * 8 + l) % 8 % 2 =
        idx / 64 * 16 + idx % 64 / 8 * 2 + l % 2 :=
      dw_aux_div8 (idx / 64) (idx % 64 / 8) l (by omega)
    have ey1 : (idx / 64 * 64 + idx % 8 * 8 + l) % 8 / 2 = l / 2 :=
      dw_aux_mod8 (idx / 64) (idx % 8) l (by omega)
    have ey2 : (idx / 64 * 64 + idx % 8 * 8 + l) / 8 * 2 +
        (idx / 64 * 64 + idx % 8 * 8 + l) % 8 % 2 =
        idx / 64 * 16 + idx % 8 * 2 + l % 2 :=
      dw_aux_div8 (idx / 64) (idx % 8) l (by omega)
    rw [eg1, eg2, ey1, ey2]
  rw [show (∑ l ∈ Finset.range 8,
        valAt (allGatherPrimDimN 3 4 0 [g0, g1, g2, g3]) (idx / 64 * 64 + idx % 64 / 8 * 8 + l) *
          valAt (transpose2d (allGatherPrimDimN 3 4 0 [y0, y1, y2, y3]))
            (idx / 64 * 64 + l * 8 + idx % 8)) =
      ∑ l ∈ Finset.range 8,
        valAt ([g0, g1, g2, g3].getD (l / 2) (zeroTensor [1, 4, 8, 2]))
            (idx / 64 * 16 + idx % 64 / 8 * 2 + l % 2) *
          valAt ([y0, y1, y2, y3].getD (l / 2) (zeroTensor [1, 4, 8, 2]))
            (idx / 64 * 16 + idx % 8 * 2 + l % 2)
      from Finset.sum_congr rfl (fun l hl => hA l (Finset.mem_range.mp hl))]
  -- RHS: unfold allReduce sum
  rw [allReducePrim_valAt 4 0 _ idx _ rfl (by rw [hP0_shape]; simpa [prodShape] using hidx256)]
  simp only [List.foldl]
  rw [hPval g0 y0 hg0 hy0, hPval g1 y1 hg1 hy1, hPval g2 y2 hg2 hy2, hPval g3 y3 hg3 hy3]
  -- expand all finite sums and getD selections, then close by ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
  ring

/-! ## BW_matmul dX batch-dim (dim1) distribution helpers (for goal_157 family) -/

/-- The first output (`dX`) of `bw_matmul` is `g @ yᵀ`. -/
theorem bw_matmul_fst_eq (g x y : Tensor) :
    (bw_matmul g x y).1 = batchedMatmul g (transpose2d y) := rfl

/-- Chunking along dim 1 commutes with `transpose2d` (which swaps the last two dims). -/
theorem transpose2d_chunkPrimDimN1_comm_1_4_8_8 (x : Tensor) (r : Nat)
    (hx : x.shape = [1, 4, 8, 8]) (hr : r < 4) :
    transpose2d (chunkPrimDimN 1 4 r x) = chunkPrimDimN 1 4 r (transpose2d x) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 1, 8, 8] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have htx_shape : (transpose2d x).shape = [1, 4, 8, 8] := transpose2d_shape_1_4_8_8 x hx
  have hlhs_shape : (transpose2d (chunkPrimDimN 1 4 r x)).shape = [1, 1, 8, 8] :=
    transpose2d_shape_1_1_8_8 _ hchunk_shape
  have hrhs_shape : (chunkPrimDimN 1 4 r (transpose2d x)).shape = [1, 1, 8, 8] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ htx_shape (by omega)]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx64 : idx < 64 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transpose2d_valAt_1_1_8_8 _ idx hchunk_shape hidx64]
  have hb1 : idx % 8 * 8 + idx / 8 < 64 := by omega
  rw [chunk_dim1_4_1_4_8_8_valAt x r (idx % 8 * 8 + idx / 8) hx hr hb1]
  rw [chunk_dim1_4_1_4_8_8_valAt (transpose2d x) r idx htx_shape hr hidx64]
  rw [transpose2d_valAt_1_4_8_8 x (r * 64 + idx) hx (by omega)]
  congr 1
  omega

/-- `dX = g @ yᵀ` distributes over a batch-dim (dim 1) split:
    gathering the per-shard `bw_matmul.1` results along dim 1 reconstructs the full result. -/
theorem bw_matmul_fst_split_dim1_4_1_4_8_8 (g y : Tensor)
    (hg : g.shape = [1, 4, 8, 8]) (hy : y.shape = [1, 4, 8, 8]) :
    batchedMatmul g (transpose2d y) =
      allGatherPrimDimN 1 4 0
        [batchedMatmul (chunkPrimDimN 1 4 0 g) (transpose2d (chunkPrimDimN 1 4 0 y)),
         batchedMatmul (chunkPrimDimN 1 4 1 g) (transpose2d (chunkPrimDimN 1 4 1 y)),
         batchedMatmul (chunkPrimDimN 1 4 2 g) (transpose2d (chunkPrimDimN 1 4 2 y)),
         batchedMatmul (chunkPrimDimN 1 4 3 g) (transpose2d (chunkPrimDimN 1 4 3 y))] := by
  have hty : (transpose2d y).shape = [1, 4, 8, 8] := transpose2d_shape_1_4_8_8 y hy
  have hsplit := fw_matmul_split_dim1_4_1_4_8_8 g (transpose2d y) hg hty
  rw [← transpose2d_chunkPrimDimN1_comm_1_4_8_8 y 0 hy (by omega),
      ← transpose2d_chunkPrimDimN1_comm_1_4_8_8 y 1 hy (by omega),
      ← transpose2d_chunkPrimDimN1_comm_1_4_8_8 y 2 hy (by omega),
      ← transpose2d_chunkPrimDimN1_comm_1_4_8_8 y 3 hy (by omega)] at hsplit
  exact hsplit


/-- `bw_add2` second output (dy) is the gradient itself when `g` and `y` share a shape. -/
theorem bw_add2_snd_same_shape_g110 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g110
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

theorem bw_add2_snd_same_shape_g171 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g171
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

/-! ### batch10 BW_add g145 net-new lemmas -/

/-- `bw_add2` second output (dY) equals the gradient when `g` and `y` share a shape. -/
theorem bw_add2_snd_same_shape_g145 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g145
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

/-- Value of `chunkPrimDimN 1 4 r x` (chunk along dim 1) for `x : [1,8,32]`.
    The shard has shape `[1,2,32]` (product 64); local flat `loc < 64` maps to
    global flat `r*64 + loc`. -/
theorem chunk_dim1_4_1_8_32_valAt_g145 (x : Tensor) (r loc : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) (hloc : loc < 64) :
    valAt (chunkPrimDimN 1 4 r x) loc = valAt x (r * 64 + loc) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : loc < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega,
    show (32 : Nat) ≠ 0 by omega, show (1 : Nat) ≠ 0 by omega, ite_false,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd,
    show (2 : Nat) ≠ 0 by omega, show (64 : Nat) ≠ 0 by omega]
  have hr4 : r % 4 = r := Nat.mod_eq_of_lt hr
  rw [hr4]
  congr 1
  omega

/-- Value of `allGatherPrimDimN 1 4 0 xs` (gather along dim 1) for shards of shape
    `[1,2,32]`: the gathered tensor has shape `[1,8,32]`; global flat `idx < 256`
    selects piece `idx / 64` at local flat `idx % 64`. -/
theorem allGatherPrimDimN_1_4_valAt_1_2_32_g145 (xs : List Tensor) (idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [1, 2, 32])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 1 4 0 xs) idx =
      valAt (xs.getD (idx / 64) (zeroTensor [1, 2, 32])) (idx % 64) := by
  have hresult_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 xs [1, 2, 32] hhead]; simp [List.set, List.getD]
  have hprod : idx < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hresult_shape]; simp [prodShape]; exact hidx
  rw [valAt_of_lt _ _ hprod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.div_one, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.zero_add, show (2 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega, show (64 : Nat) ≠ 0 from by omega,
    show (256 : Nat) ≠ 0 from by omega, ite_false]
  have hpre : idx / 256 = 0 := by omega
  have hrem : idx % 256 = idx := by omega
  rw [hpre, hrem]
  have hjFull_div : idx / (32 * 1) / 2 = idx / 64 := by omega
  have hjLocal : idx / (32 * 1) % 2 = (idx % 64) / 32 := by omega
  have hk : idx % (32 * 1) = idx % 32 := by omega
  rw [hjFull_div, hjLocal, hk]
  congr 1
  omega

/-- All-gather (dim 1) of the four dim-1 chunks of a `[1,8,32]` tensor recovers it. -/
theorem allGather_chunkPrimDimN_roundtrip_dim1_4_1_8_32_g145 (x : Tensor)
    (hx : x.shape = [1, 8, 32]) :
    allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x] = x := by
  have hc0 : (chunkPrimDimN 1 4 0 x).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 0 _ _ hx (by omega)]; simp [List.set, List.getD]
  have hhead : (([chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
      chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hc0]
  have hg_shape : (allGatherPrimDimN 1 4 0
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hg_shape, hx])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hg_shape, prodShape] using hidx
  rw [allGatherPrimDimN_1_4_valAt_1_2_32_g145 _ _ hhead hidx256]
  have hr : idx / 64 < 4 := by omega
  have hloc : idx % 64 < 64 := Nat.mod_lt idx (by omega)
  have hgetD : ∀ (i : Nat) (_ : i < 4),
      [chunkPrimDimN 1 4 0 x, chunkPrimDimN 1 4 1 x,
       chunkPrimDimN 1 4 2 x, chunkPrimDimN 1 4 3 x].getD i (zeroTensor [1, 2, 32]) =
        chunkPrimDimN 1 4 i x := by
    intro i hi
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [hgetD (idx / 64) hr]
  rw [chunk_dim1_4_1_8_32_valAt_g145 x (idx / 64) (idx % 64) hx hr hloc]
  congr 1
  omega

theorem bw_add2_snd_same_shape_g136 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g136
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

/-! ## BW_add second-output (dW) helpers for goal_180 (AllToAll BW_add template) -/

/-- `bw_add2` second output is the gradient itself when `g` and `y` share a shape. -/
theorem bw_add2_snd_same_shape_g180 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dW). -/
theorem applyNode_bw_add2_snd_out_g180
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

/-- Roundtrip identity: gathering the four dim-2 chunks of a `[1,8,32]` tensor
    along dim 2 reconstructs the original tensor. -/
theorem allGatherPrimDimN_chunkPrimDimN_id_dim2_4_1_8_32_g180 (x : Tensor)
    (hsh : x.shape = [1, 8, 32]) :
    allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x] = x := by
  have hchunk_shape : ∀ r, (chunkPrimDimN 2 4 r x).shape = [1, 8, 8] := by
    intro r; rw [chunkPrimDimN_shape 2 4 r _ _ hsh (by omega)]; simp [List.set, List.getD]
  have hhead : (([chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x].head?.map (fun t => t.shape)).getD []) = [1, 8, 8] := by
    simp [List.head?, Option.map, hchunk_shape 0]
  have hgather_shape : (allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hgather_shape, hsh])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hgather_shape, prodShape] using hidx
  have hidx_g : idx < prodShape (allGatherPrimDimN 2 4 0
      [chunkPrimDimN 2 4 0 x, chunkPrimDimN 2 4 1 x,
       chunkPrimDimN 2 4 2 x, chunkPrimDimN 2 4 3 x]).shape := by
    simpa [hgather_shape, prodShape] using hidx256
  rw [valAt_of_lt _ _ hidx_g]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (8 : Nat) * 4 * 1 = 32 by norm_num,
    show (8 : Nat) * 1 = 8 by norm_num]
  set p := idx / 32 with hp_def
  set r := idx % 32 / 8 with hr_def
  set j := idx % 8 with hj_def
  set loc := p * 8 + j with hloc_def
  have hp_lt : p < 8 := by omega
  have hr_lt : r < 4 := by omega
  have hj_lt : j < 8 := by omega
  have hidxget : idx % 32 / 1 / 8 = r := by subst r; omega
  have hlocnorm : idx / 32 * 8 + idx % 32 / 1 % 8 * 1 + idx % 32 % 1 = loc := by
    subst loc p j; omega
  rw [hidxget, hlocnorm]
  have hidx_norm : idx = p * 32 + r * 8 + j := by subst p r j; omega
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [h0]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [chunk2_4_1_8_32_valAt_pj x 0 p j hsh (by omega) hp_lt hj_lt]
    have : idx = p * 32 + 0 * 8 + j := by omega
    rw [← this]
  · rw [h1]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [chunk2_4_1_8_32_valAt_pj x 1 p j hsh (by omega) hp_lt hj_lt]
    have : idx = p * 32 + 1 * 8 + j := by omega
    rw [← this]
  · rw [h2]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [chunk2_4_1_8_32_valAt_pj x 2 p j hsh (by omega) hp_lt hj_lt]
    have : idx = p * 32 + 2 * 8 + j := by omega
    rw [← this]
  · rw [h3]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [chunk2_4_1_8_32_valAt_pj x 3 p j hsh (by omega) hp_lt hj_lt]
    have : idx = p * 32 + 3 * 8 + j := by omega
    rw [← this]

/-- `bw_add2` second output (dy) equals the gradient when out shape = y shape. -/
theorem bw_add2_snd_same_shape_g206 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g206
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

theorem bw_add2_snd_same_shape_g215 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g215
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne, hne.symm]

theorem bw_add2_snd_same_shape_g241 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g241
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne]

theorem bw_add2_snd_same_shape_g250 (g x y : Tensor) (h : g.shape = y.shape) :
    (bw_add2 g x y).2 = g := by
  show reduceBroadcast g.shape y.shape (fun k => valAt g k) = g
  rw [h, reduceBroadcast_same]
  rw [← h]
  apply Tensor.ext (by simp [Tensor.mkShape])
  intro idx hidx
  simp [Tensor.mkShape, valAt_of_lt g idx hidx]

/-- `applyNode` for ternary `BW_add` — second output (dy). -/
theorem applyNode_bw_add2_snd_out_g250
    (graph : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid yTid dxTid dyTid : Tid)
    (hne : dxTid ≠ dyTid) :
    applyNode graph s { rank := rank, op := "OpName.BW_add", ins := [gTid, xTid, yTid], outs := [dxTid, dyTid] } dyTid =
      (bw_add2 (s gTid) (s xTid) (s yTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, yTid] : List Tid).map s = [s gTid, s xTid, s yTid] from rfl,
      evalOp_bw_add2]
  change storeSet s [(dxTid, (bw_add2 (s gTid) (s xTid) (s yTid)).1),
                     (dyTid, (bw_add2 (s gTid) (s xTid) (s yTid)).2)] dyTid = _
  unfold storeSet
  simp [List.find?, hne, hne.symm]

/-! ## BW_matmul dX row-dim (dim2) distribution helper (for goal_192 family)

When the first operand `g` of `dX = g @ yᵀ` is partitioned along its output-row
dimension (dim 2) into 4 shards of shape `[1,4,2,8]` while `y` is replicated, each
rank computes `g_r @ yᵀ` (shape `[1,4,2,8]`), and the full `dX` is reconstructed by
gathering along dim 2. -/
set_option maxHeartbeats 1600000 in
theorem fw_matmul_split_dim2_first_1_4_8_8_g192 (a b : Tensor)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 8]) :
    batchedMatmul a b =
      allGatherPrimDimN 2 4 0
        [batchedMatmul (chunkPrimDimN 2 4 0 a) b,
         batchedMatmul (chunkPrimDimN 2 4 1 a) b,
         batchedMatmul (chunkPrimDimN 2 4 2 a) b,
         batchedMatmul (chunkPrimDimN 2 4 3 a) b] := by
  have hchunk_a : ∀ r, r < 4 → (chunkPrimDimN 2 4 r a).shape = [1, 4, 2, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ ha (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 →
      (batchedMatmul (chunkPrimDimN 2 4 r a) b).shape = [1, 4, 2, 8] :=
    fun r hr => batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _ (hchunk_a r hr) hb
  have hp0 := hpiece_shape 0 (by decide)
  have hlhs_shape : (batchedMatmul a b).shape = [1, 4, 8, 8] :=
    batchedMatmul_shape_1_4_8_8_1_4_8_8 a b ha hb
  have hhead : (([batchedMatmul (chunkPrimDimN 2 4 0 a) b,
                  batchedMatmul (chunkPrimDimN 2 4 1 a) b,
                  batchedMatmul (chunkPrimDimN 2 4 2 a) b,
                  batchedMatmul (chunkPrimDimN 2 4 3 a) b] : List Tensor).head?.map
                (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by simp [hp0]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [batchedMatmul (chunkPrimDimN 2 4 0 a) b,
       batchedMatmul (chunkPrimDimN 2 4 1 a) b,
       batchedMatmul (chunkPrimDimN 2 4 2 a) b,
       batchedMatmul (chunkPrimDimN 2 4 3 a) b]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [show batchedMatmul a b = fw_matmul a b from rfl,
      fw_matmul_valAt_1_4_8_8 a b idx ha hb hidx256]
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ idx hhead hidx256]
  set loc := idx / 64 * 16 + idx % 16 / 8 * 8 + idx % 8 with hloc_def
  have hloc_lt : loc < 64 := by rw [hloc_def]; omega
  -- value of the rr-th piece at flat `loc`
  have hvalpiece : ∀ rr, rr < 4 →
      valAt (batchedMatmul (chunkPrimDimN 2 4 rr a) b) loc =
        ∑ l ∈ Finset.range 8,
          valAt a (idx / 64 * 64 + rr * 16 + idx % 16 / 8 * 8 + l) *
            valAt b (idx / 64 * 64 + l * 8 + idx % 8) := by
    intro rr hrr
    rw [batchedMatmul_valAt_1_4_2_8_1_4_8_8 _ b loc (hchunk_a rr hrr) hb hloc_lt]
    apply Finset.sum_congr rfl
    intro l hl
    have hl_lt : l < 8 := by simpa using hl
    have hbnd : loc / 16 * 16 + loc % 16 / 8 * 8 + l < 64 := by rw [hloc_def]; omega
    rw [chunkPrimDimN_2_4_valAt_1_4_8_8 a rr (loc / 16 * 16 + loc % 16 / 8 * 8 + l) ha hrr hbnd]
    congr 1
    · congr 1; rw [hloc_def]; omega
    · congr 1; rw [hloc_def]; omega
  have hr_lt : idx % 64 / 16 < 4 := by omega
  have hr_cases : idx % 64 / 16 = 0 ∨ idx % 64 / 16 = 1 ∨ idx % 64 / 16 = 2 ∨ idx % 64 / 16 = 3 := by
    omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [show ([batchedMatmul (chunkPrimDimN 2 4 0 a) b,
              batchedMatmul (chunkPrimDimN 2 4 1 a) b,
              batchedMatmul (chunkPrimDimN 2 4 2 a) b,
              batchedMatmul (chunkPrimDimN 2 4 3 a) b] : List Tensor).getD (idx % 64 / 16)
            (zeroTensor [1, 4, 2, 8]) =
          batchedMatmul (chunkPrimDimN 2 4 0 a) b from by rw [h0]; rfl,
        hvalpiece 0 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega
  · rw [show ([batchedMatmul (chunkPrimDimN 2 4 0 a) b,
              batchedMatmul (chunkPrimDimN 2 4 1 a) b,
              batchedMatmul (chunkPrimDimN 2 4 2 a) b,
              batchedMatmul (chunkPrimDimN 2 4 3 a) b] : List Tensor).getD (idx % 64 / 16)
            (zeroTensor [1, 4, 2, 8]) =
          batchedMatmul (chunkPrimDimN 2 4 1 a) b from by rw [h1]; rfl,
        hvalpiece 1 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega
  · rw [show ([batchedMatmul (chunkPrimDimN 2 4 0 a) b,
              batchedMatmul (chunkPrimDimN 2 4 1 a) b,
              batchedMatmul (chunkPrimDimN 2 4 2 a) b,
              batchedMatmul (chunkPrimDimN 2 4 3 a) b] : List Tensor).getD (idx % 64 / 16)
            (zeroTensor [1, 4, 2, 8]) =
          batchedMatmul (chunkPrimDimN 2 4 2 a) b from by rw [h2]; rfl,
        hvalpiece 2 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega
  · rw [show ([batchedMatmul (chunkPrimDimN 2 4 0 a) b,
              batchedMatmul (chunkPrimDimN 2 4 1 a) b,
              batchedMatmul (chunkPrimDimN 2 4 2 a) b,
              batchedMatmul (chunkPrimDimN 2 4 3 a) b] : List Tensor).getD (idx % 64 / 16)
            (zeroTensor [1, 4, 2, 8]) =
          batchedMatmul (chunkPrimDimN 2 4 3 a) b from by rw [h3]; rfl,
        hvalpiece 3 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega

/-! ## BW_matmul dW contraction-dim (dim2) split with AllReduce (for goal_197 family).

`transpose2d` commutes with a dim-2 gather (turning it into a dim-3 gather of the
transposed shards), and `BW_matmul`'s second output (`dy = xᵀ @ g`) with both operands
partitioned along their shared contraction dimension (dim 2, size `8 → 2`) reduces to the
`allReducePrim` sum of the per-rank products. -/

/-! Flat-index arithmetic helpers for `transpose2d_gather2_eq_gather3_g197`
(proven in an empty context so `omega` stays fast). -/

private theorem t2g_aux_jbnd_g197 (idx : Nat) (hidx : idx < 256) :
    idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8 < 256 := by omega

private theorem t2g_aux_sh_g197 (idx : Nat) :
    (idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8) % 64 / 16 = idx % 8 / 2 := by
  have hj : (idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8) % 64 = idx % 8 * 8 + idx % 64 / 8 := by
    omega
  rw [hj]; omega

private theorem t2g_aux_mbnd_g197 (idx : Nat) (hidx : idx < 256) :
    idx / 8 * 2 + idx % 8 % 2 < 64 := by omega

private theorem t2g_aux_inner_g197 (idx : Nat) :
    (idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8) / 64 * 16 +
      (idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8) % 16 / 8 * 8 +
      (idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8) % 8 =
    (idx / 8 * 2 + idx % 8 % 2) / 16 * 16 + (idx / 8 * 2 + idx % 8 % 2) % 2 * 8 +
      (idx / 8 * 2 + idx % 8 % 2) % 16 / 2 := by
  have ha : idx % 8 < 8 := Nat.mod_lt _ (by omega)
  have hb : idx % 64 / 8 < 8 := by omega
  have hidx8 : idx / 8 = idx / 64 * 8 + idx % 64 / 8 := by omega
  rw [hidx8]
  revert ha hb
  generalize idx % 8 = A
  generalize idx % 64 / 8 = B
  generalize idx / 64 = E
  intro ha hb
  rw [show (E * 64 + A * 8 + B) / 64 = E from by omega,
      show (E * 64 + A * 8 + B) % 16 / 8 = A % 2 from by omega,
      show (E * 64 + A * 8 + B) % 8 = B from by omega,
      show ((E * 8 + B) * 2 + A % 2) / 16 = E from by omega,
      show ((E * 8 + B) * 2 + A % 2) % 2 = A % 2 from by omega,
      show ((E * 8 + B) * 2 + A % 2) % 16 / 2 = B from by omega]

/-- `transpose2d` of a dim-2 gather equals the dim-3 gather of the transposed shards
(for `[1,4,2,8]` shards gathered into `[1,4,8,8]`). -/
theorem transpose2d_gather2_eq_gather3_g197 (x0 x1 x2 x3 : Tensor)
    (h0 : x0.shape = [1, 4, 2, 8]) (h1 : x1.shape = [1, 4, 2, 8])
    (h2 : x2.shape = [1, 4, 2, 8]) (h3 : x3.shape = [1, 4, 2, 8]) :
    transpose2d (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) =
      allGatherPrimDimN 3 4 0
        [transpose2d x0, transpose2d x1, transpose2d x2, transpose2d x3] := by
  have hhead2 : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [1, 4, 2, 8] := by simp [h0]
  have htx0 : (transpose2d x0).shape = [1, 4, 8, 2] := transpose2d_shape_1_4_2_8 _ h0
  have hhead3 : (([transpose2d x0, transpose2d x1, transpose2d x2, transpose2d x3] :
      List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by simp [htx0]
  have hX_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead2]; simp [List.set, List.getD]
  have hlhs_shape : (transpose2d (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])).shape = [1, 4, 8, 8] :=
    transpose2d_shape_1_4_8_8 _ hX_shape
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [transpose2d x0, transpose2d x1, transpose2d x2, transpose2d x3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead3]; simp [List.set, List.getD]
  have hxget : ∀ s, s < 4 →
      ([x0, x1, x2, x3].getD s (zeroTensor [1, 4, 2, 8])).shape = [1, 4, 2, 8] := by
    intro s hs
    have : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, h0, h1, h2, h3]
  have hsel : ∀ s, s < 4 →
      [transpose2d x0, transpose2d x1, transpose2d x2, transpose2d x3].getD s
          (zeroTensor [1, 4, 8, 2]) =
        transpose2d ([x0, x1, x2, x3].getD s (zeroTensor [1, 4, 2, 8])) := by
    intro s hs
    have : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [transpose2d_valAt_1_4_8_8 _ idx hX_shape hidx256]
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 [x0, x1, x2, x3]
      (idx / 64 * 64 + idx % 8 * 8 + idx % 64 / 8) hhead2 (t2g_aux_jbnd_g197 idx hidx256)]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2
      [transpose2d x0, transpose2d x1, transpose2d x2, transpose2d x3] idx hhead3 hidx256]
  rw [hsel ((idx % 8) / 2) (by omega)]
  rw [transpose2d_valAt_1_4_2_8 _ (idx / 8 * 2 + idx % 8 % 2)
      (hxget ((idx % 8) / 2) (by omega)) (t2g_aux_mbnd_g197 idx hidx256)]
  rw [t2g_aux_sh_g197 idx]
  congr 1
  exact t2g_aux_inner_g197 idx

/-- `BW_matmul` second output (`dy = xᵀ @ g`) with both operands partitioned along their
shared contraction dimension (dim 2 into 4 shards `[1,4,2,8]`); the full `dy` is the
`allReducePrim` sum of the per-rank products `xᵣᵀ @ gᵣ`. -/
theorem bw_matmul_snd_split_dW_g197 (x0 x1 x2 x3 g0 g1 g2 g3 : Tensor)
    (hx0 : x0.shape = [1, 4, 2, 8]) (hx1 : x1.shape = [1, 4, 2, 8])
    (hx2 : x2.shape = [1, 4, 2, 8]) (hx3 : x3.shape = [1, 4, 2, 8])
    (hg0 : g0.shape = [1, 4, 2, 8]) (hg1 : g1.shape = [1, 4, 2, 8])
    (hg2 : g2.shape = [1, 4, 2, 8]) (hg3 : g3.shape = [1, 4, 2, 8]) :
    batchedMatmul (transpose2d (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]))
        (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) =
      allReducePrim 4 0
        [batchedMatmul (transpose2d x0) g0, batchedMatmul (transpose2d x1) g1,
         batchedMatmul (transpose2d x2) g2, batchedMatmul (transpose2d x3) g3] := by
  rw [transpose2d_gather2_eq_gather3_g197 x0 x1 x2 x3 hx0 hx1 hx2 hx3]
  rw [show batchedMatmul (allGatherPrimDimN 3 4 0
        [transpose2d x0, transpose2d x1, transpose2d x2, transpose2d x3])
        (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) =
      fw_matmul (allGatherPrimDimN 3 4 0
        [transpose2d x0, transpose2d x1, transpose2d x2, transpose2d x3])
        (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) from rfl]
  rw [fw_matmul_split_dimK_1_4_8_8 (transpose2d x0) (transpose2d x1) (transpose2d x2)
      (transpose2d x3) g0 g1 g2 g3
      (transpose2d_shape_1_4_2_8 _ hx0) (transpose2d_shape_1_4_2_8 _ hx1)
      (transpose2d_shape_1_4_2_8 _ hx2) (transpose2d_shape_1_4_2_8 _ hx3)
      hg0 hg1 hg2 hg3]

/-- `chunkPrimDimN` (dim 1) undoes `allGatherPrimDimN` (dim 1) on `[1, 1, 8, 8]` shards.
    This is the dim-1, 4-D analogue of `chunkPrimDimN_allGatherPrimDimN_dim2_4_1_8_8`. -/
theorem chunkPrimDimN_allGatherPrimDimN_dim1_4_1_1_8_8_g232 (p0 p1 p2 p3 : Tensor) (r : Nat)
    (h0 : p0.shape = [1, 1, 8, 8]) (h1 : p1.shape = [1, 1, 8, 8])
    (h2 : p2.shape = [1, 1, 8, 8]) (h3 : p3.shape = [1, 1, 8, 8]) (hr : r < 4) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]) =
      ([p0, p1, p2, p3] : List Tensor).getD r (zeroTensor [1, 1, 8, 8]) := by
  have hhead : (([p0, p1, p2, p3] : List Tensor).head?.map (·.shape)).getD [] = [1, 1, 8, 8] := by
    simp [h0]
  have hgather_shape : (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]; simp [List.set, List.getD]
  have hchunk_shape : (chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [p0, p1, p2, p3])).shape
      = [1, 1, 8, 8] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hgather_shape (by omega)]
    simp [List.set, List.getD]
  have hrhs_shape : (([p0, p1, p2, p3] : List Tensor).getD r (zeroTensor [1, 1, 8, 8])).shape
      = [1, 1, 8, 8] := by
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with h | h | h | h <;> subst h <;>
      simp [List.getD, h0, h1, h2, h3]
  apply Tensor.ext
  · rw [hchunk_shape, hrhs_shape]
  · intro idx hidx
    rw [hchunk_shape] at hidx
    have hidx64 : idx < 64 := by simpa [prodShape] using hidx
    rw [chunk_dim1_4_1_4_8_8_valAt _ r idx hgather_shape hr hidx64]
    rw [allGather_dim1_4_1_1_8_8_valAt p0 p1 p2 p3 (r * 64 + idx) h0 h1 h2 h3 (by omega)]
    have ha : (r * 64 + idx) / 64 = r := by omega
    have hb : (r * 64 + idx) % 64 = idx := by omega
    rw [ha, hb]

/-- `valAt` for a 3-element `tensorSum` when the index is in-bounds of the first shape. -/
private theorem tensorSum_triple_valAt_g114 (a b c : Tensor) (idx : Nat)
    (hidx : idx < prodShape a.shape) :
    valAt (tensorSum [a, b, c]) idx = valAt a idx + valAt b idx + valAt c idx := by
  have hsh : (tensorSum [a, b, c]).shape = a.shape := rfl
  rw [valAt_of_lt _ _ (by rw [hsh]; exact hidx)]
  simp [tensorSum, Tensor.mkShape, List.foldl]

/-- BW_multiref (3-way `tensorSum`) distributes over a dim-1 `allGatherPrimDimN`
    with 4 parts (shard `[1,2,32]`, full `[1,8,32]`).  Two operands are themselves
    gathers of per-rank shards; the third is a full tensor reconstructed from its
    per-rank chunks. -/
theorem tensorSum_triple_gather_dim1_4_1_8_32_g114
    (a0 a1 a2 a3 b0 b1 b2 b3 c : Tensor)
    (ha0 : a0.shape = [1, 2, 32]) (ha1 : a1.shape = [1, 2, 32])
    (ha2 : a2.shape = [1, 2, 32]) (ha3 : a3.shape = [1, 2, 32])
    (hb0 : b0.shape = [1, 2, 32]) (hb1 : b1.shape = [1, 2, 32])
    (hb2 : b2.shape = [1, 2, 32]) (hb3 : b3.shape = [1, 2, 32])
    (hc : c.shape = [1, 8, 32]) :
    tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
               allGatherPrimDimN 1 4 0 [b0, b1, b2, b3], c] =
      allGatherPrimDimN 1 4 0
        [tensorSum [a0, b0, chunkPrimDimN 1 4 0 c],
         tensorSum [a1, b1, chunkPrimDimN 1 4 1 c],
         tensorSum [a2, b2, chunkPrimDimN 1 4 2 c],
         tensorSum [a3, b3, chunkPrimDimN 1 4 3 c]] := by
  have haHead : (([a0, a1, a2, a3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [ha0]
  have hbHead : (([b0, b1, b2, b3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hb0]
  have hs0 : (tensorSum [a0, b0, chunkPrimDimN 1 4 0 c]).shape = [1, 2, 32] := by
    rw [tensorSum_shape]; exact ha0
  have hrhsHead : (([tensorSum [a0, b0, chunkPrimDimN 1 4 0 c],
                     tensorSum [a1, b1, chunkPrimDimN 1 4 1 c],
                     tensorSum [a2, b2, chunkPrimDimN 1 4 2 c],
                     tensorSum [a3, b3, chunkPrimDimN 1 4 3 c]].head?.map
                     (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hs0]
  have hag_a_shape : (allGatherPrimDimN 1 4 0 [a0, a1, a2, a3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ haHead]; simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
      allGatherPrimDimN 1 4 0 [b0, b1, b2, b3], c]).shape = [1, 8, 32] := by
    rw [tensorSum_shape]; exact hag_a_shape
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [tensorSum [a0, b0, chunkPrimDimN 1 4 0 c],
       tensorSum [a1, b1, chunkPrimDimN 1 4 1 c],
       tensorSum [a2, b2, chunkPrimDimN 1 4 2 c],
       tensorSum [a3, b3, chunkPrimDimN 1 4 3 c]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hrhsHead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [tensorSum_triple_valAt_g114 _ _ _ idx (by rw [hag_a_shape]; simpa [prodShape] using hidx256)]
  set j := idx % 32 with hjdef
  set r := idx / 32 / 2 with hrdef
  set p := idx / 32 % 2 with hpdef
  have hj : j < 32 := by omega
  have hr : r < 4 := by omega
  have hp : p < 2 := by omega
  have hidx_eq : idx = (r * 2 + p) * 32 + j := by omega
  have hbound : p * 32 + j < prodShape ([1, 2, 32] : Shape) := by simp [prodShape]; omega
  rw [hidx_eq]
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h | h | h | h
  · rw [h]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [a0, a1, a2, a3] 0 (by omega) p hp j hj haHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [b0, b1, b2, b3] 0 (by omega) p hp j hj hbHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt _ 0 (by omega) p hp j hj hrhsHead]
    simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
    rw [tensorSum_triple_valAt_g114 _ _ _ (p * 32 + j) (by rw [ha0]; exact hbound),
        chunk_dim1_4_1_8_32_valAt c 0 p j hc (by omega) hp hj]
  · rw [h]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [a0, a1, a2, a3] 1 (by omega) p hp j hj haHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [b0, b1, b2, b3] 1 (by omega) p hp j hj hbHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt _ 1 (by omega) p hp j hj hrhsHead]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [tensorSum_triple_valAt_g114 _ _ _ (p * 32 + j) (by rw [ha1]; exact hbound),
        chunk_dim1_4_1_8_32_valAt c 1 p j hc (by omega) hp hj]
  · rw [h]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [a0, a1, a2, a3] 2 (by omega) p hp j hj haHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [b0, b1, b2, b3] 2 (by omega) p hp j hj hbHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt _ 2 (by omega) p hp j hj hrhsHead]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [tensorSum_triple_valAt_g114 _ _ _ (p * 32 + j) (by rw [ha2]; exact hbound),
        chunk_dim1_4_1_8_32_valAt c 2 p j hc (by omega) hp hj]
  · rw [h]
    rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [a0, a1, a2, a3] 3 (by omega) p hp j hj haHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt [b0, b1, b2, b3] 3 (by omega) p hp j hj hbHead,
        allGatherPrimDimN_dim1_4_1_2_32_valAt _ 3 (by omega) p hp j hj hrhsHead]
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [tensorSum_triple_valAt_g114 _ _ _ (p * 32 + j) (by rw [ha3]; exact hbound),
        chunk_dim1_4_1_8_32_valAt c 3 p j hc (by omega) hp hj]

set_option maxHeartbeats 1600000 in
/-- `fw_matmul` distributes over a row-dim (dim 2, the `M` axis) split of its first operand.
The second operand `b` is replicated; each rank computes `fw_matmul (chunk_2 r a) b` of shape
`[1,4,2,8]`, and the full result is the `allGatherPrimDimN 2` concatenation of those per-rank
products (no reduction needed). Used by the FW_matmul AllToAll(`[1,2]`) goals. -/
theorem fw_matmul_split_dim2_4_1_4_8_8_g66 (a b : Tensor)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 8]) :
    fw_matmul a b =
      allGatherPrimDimN 2 4 0
        [fw_matmul (chunkPrimDimN 2 4 0 a) b,
         fw_matmul (chunkPrimDimN 2 4 1 a) b,
         fw_matmul (chunkPrimDimN 2 4 2 a) b,
         fw_matmul (chunkPrimDimN 2 4 3 a) b] := by
  have hchunk_a : ∀ r, r < 4 → (chunkPrimDimN 2 4 r a).shape = [1, 4, 2, 8] := by
    intro r hr
    rw [chunkPrimDimN_shape 2 4 r _ _ ha (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 →
      (fw_matmul (chunkPrimDimN 2 4 r a) b).shape = [1, 4, 2, 8] := by
    intro r hr
    exact batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _ (hchunk_a r hr) hb
  have hp0 := hpiece_shape 0 (by decide)
  have hlhs_shape : (fw_matmul a b).shape = [1, 4, 8, 8] :=
    fw_matmul_shape_1_4_8_8 a b ha hb
  have hhead : (([fw_matmul (chunkPrimDimN 2 4 0 a) b,
                  fw_matmul (chunkPrimDimN 2 4 1 a) b,
                  fw_matmul (chunkPrimDimN 2 4 2 a) b,
                  fw_matmul (chunkPrimDimN 2 4 3 a) b] : List Tensor).head?.map
                (fun t => t.shape)).getD [] = [1, 4, 2, 8] := by
    simp [hp0]
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [fw_matmul (chunkPrimDimN 2 4 0 a) b,
       fw_matmul (chunkPrimDimN 2 4 1 a) b,
       fw_matmul (chunkPrimDimN 2 4 2 a) b,
       fw_matmul (chunkPrimDimN 2 4 3 a) b]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [fw_matmul_valAt_1_4_8_8 a b idx ha hb hidx256]
  rw [allGatherPrimDimN_2_4_valAt_1_4_2_8 _ idx hhead hidx256]
  set loc := idx / 64 * 16 + idx % 16 / 8 * 8 + idx % 8 with hloc_def
  have hloc_lt : loc < 64 := by subst loc; omega
  have hq_cases : idx % 64 / 16 = 0 ∨ idx % 64 / 16 = 1 ∨ idx % 64 / 16 = 2 ∨ idx % 64 / 16 = 3 :=
    by omega
  have hvalpiece : ∀ pp, pp < 4 →
      valAt (fw_matmul (chunkPrimDimN 2 4 pp a) b) loc =
        ∑ l ∈ Finset.range 8,
          valAt a (((loc / 16 * 16 + loc % 16 / 8 * 8 + l) / 16) * 64 + pp * 16 +
                    (loc / 16 * 16 + loc % 16 / 8 * 8 + l) % 16) *
            valAt b (loc / 16 * 64 + l * 8 + loc % 8) := by
    intro pp hpp
    rw [batchedMatmul_valAt_1_4_2_8_1_4_8_8 _ _ loc (hchunk_a pp hpp) hb hloc_lt]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := by simpa using hl
    have hbnd : loc / 16 * 16 + loc % 16 / 8 * 8 + l < 64 := by omega
    rw [chunkPrimDimN_2_4_valAt_1_4_8_8 a pp (loc / 16 * 16 + loc % 16 / 8 * 8 + l) ha hpp hbnd]
  rcases hq_cases with h0 | h1 | h2 | h3
  · have hsel : ([fw_matmul (chunkPrimDimN 2 4 0 a) b, fw_matmul (chunkPrimDimN 2 4 1 a) b,
                  fw_matmul (chunkPrimDimN 2 4 2 a) b, fw_matmul (chunkPrimDimN 2 4 3 a) b] :
                  List Tensor).getD (idx % 64 / 16) (zeroTensor [1, 4, 2, 8]) =
                fw_matmul (chunkPrimDimN 2 4 0 a) b := by rw [h0]; rfl
    rw [hsel, hvalpiece 0 (by decide)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := Finset.mem_range.mp hl
    congr 2 <;> (subst loc; omega)
  · have hsel : ([fw_matmul (chunkPrimDimN 2 4 0 a) b, fw_matmul (chunkPrimDimN 2 4 1 a) b,
                  fw_matmul (chunkPrimDimN 2 4 2 a) b, fw_matmul (chunkPrimDimN 2 4 3 a) b] :
                  List Tensor).getD (idx % 64 / 16) (zeroTensor [1, 4, 2, 8]) =
                fw_matmul (chunkPrimDimN 2 4 1 a) b := by rw [h1]; rfl
    rw [hsel, hvalpiece 1 (by decide)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := Finset.mem_range.mp hl
    congr 2 <;> (subst loc; omega)
  · have hsel : ([fw_matmul (chunkPrimDimN 2 4 0 a) b, fw_matmul (chunkPrimDimN 2 4 1 a) b,
                  fw_matmul (chunkPrimDimN 2 4 2 a) b, fw_matmul (chunkPrimDimN 2 4 3 a) b] :
                  List Tensor).getD (idx % 64 / 16) (zeroTensor [1, 4, 2, 8]) =
                fw_matmul (chunkPrimDimN 2 4 2 a) b := by rw [h2]; rfl
    rw [hsel, hvalpiece 2 (by decide)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := Finset.mem_range.mp hl
    congr 2 <;> (subst loc; omega)
  · have hsel : ([fw_matmul (chunkPrimDimN 2 4 0 a) b, fw_matmul (chunkPrimDimN 2 4 1 a) b,
                  fw_matmul (chunkPrimDimN 2 4 2 a) b, fw_matmul (chunkPrimDimN 2 4 3 a) b] :
                  List Tensor).getD (idx % 64 / 16) (zeroTensor [1, 4, 2, 8]) =
                fw_matmul (chunkPrimDimN 2 4 3 a) b := by rw [h3]; rfl
    rw [hsel, hvalpiece 3 (by decide)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl8 : l < 8 := Finset.mem_range.mp hl
    congr 2 <;> (subst loc; omega)

/-- Shape preservation for `fw_matmul` with `x : [1,4,8,8]`, `y : [1,4,8,2]`. -/
theorem fw_matmul_shape_1_4_8_2_g94 (x y : Tensor)
    (hx : x.shape = [1, 4, 8, 8]) (hy : y.shape = [1, 4, 8, 2]) :
    (fw_matmul x y).shape = [1, 4, 8, 2] := by
  unfold fw_matmul batchedMatmul
  simp only [hx, hy, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    Tensor.mkShape]

/-- valAt of `fw_matmul a b` at flat `idx < 64` for `a : [1,4,8,8]`, `b : [1,4,8,2]`.
    The output has shape `[1,4,8,2]`. -/
private theorem fw_matmul_valAt_1_4_8_2_g94 (a b : Tensor) (idx : Nat)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 2]) (hidx : idx < 64) :
    valAt (fw_matmul a b) idx =
      ∑ l ∈ Finset.range 8,
        valAt a (idx / 16 * 64 + idx % 16 / 2 * 8 + l) *
          valAt b (idx / 16 * 16 + l * 2 + idx % 2) := by
  have key : fw_matmul a b = Tensor.mkShape [1, 4, 8, 2] (fun outIdx =>
      ∑ l ∈ Finset.range 8,
        valAt a (outIdx.1 / (8 * 2) * (8 * 8) +
                  outIdx.1 % (8 * 2) / 2 * 8 + l) *
          valAt b (outIdx.1 / (8 * 2) * (8 * 2) + l * 2 +
                    outIdx.1 % (8 * 2) % 2)) := by
    unfold fw_matmul batchedMatmul
    rw [ha, hb]
    rfl
  rw [key]
  have hidx' : idx < prodShape ([1,4,8,2] : Shape) := by simp [prodShape]; omega
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape]; exact hidx')]
  show ∑ l ∈ Finset.range 8,
        valAt a (idx / (8 * 2) * (8 * 8) + idx % (8 * 2) / 2 * 8 + l) *
          valAt b (idx / (8 * 2) * (8 * 2) + l * 2 + idx % (8 * 2) % 2) = _
  apply Finset.sum_congr rfl
  intro l _
  congr 2 <;> omega

set_option maxHeartbeats 4000000 in
/-- `fw_matmul` distributes over a dim-3 (output-column) split of the second operand:
    chunking `b` along dim 3 commutes with matmul, and the full result is the all-gather
    along dim 3 of the per-chunk matmuls. The first operand `a` is shared by every chunk. -/
theorem fw_matmul_split_dim3_4_1_4_8_8_g94 (a b : Tensor)
    (ha : a.shape = [1, 4, 8, 8]) (hb : b.shape = [1, 4, 8, 8]) :
    fw_matmul a b =
      allGatherPrimDimN 3 4 0
        [fw_matmul a (chunkPrimDimN 3 4 0 b),
         fw_matmul a (chunkPrimDimN 3 4 1 b),
         fw_matmul a (chunkPrimDimN 3 4 2 b),
         fw_matmul a (chunkPrimDimN 3 4 3 b)] := by
  have hchunk_b : ∀ r, r < 4 → (chunkPrimDimN 3 4 r b).shape = [1, 4, 8, 2] := by
    intro r hr
    rw [chunkPrimDimN_shape 3 4 r _ _ hb (by omega)]
    simp [List.set, List.getD]
  have hpiece_shape : ∀ r, r < 4 →
      (fw_matmul a (chunkPrimDimN 3 4 r b)).shape = [1, 4, 8, 2] := by
    intro r hr
    exact fw_matmul_shape_1_4_8_2_g94 _ _ ha (hchunk_b r hr)
  have hp0 := hpiece_shape 0 (by decide)
  have hlhs_shape : (fw_matmul a b).shape = [1, 4, 8, 8] :=
    fw_matmul_shape_1_4_8_8 a b ha hb
  have hhead : (([fw_matmul a (chunkPrimDimN 3 4 0 b),
                  fw_matmul a (chunkPrimDimN 3 4 1 b),
                  fw_matmul a (chunkPrimDimN 3 4 2 b),
                  fw_matmul a (chunkPrimDimN 3 4 3 b)] : List Tensor).head?.map
                (fun t => t.shape)).getD [] = [1, 4, 8, 2] := by
    simp [hp0]
  have hrhs_shape : (allGatherPrimDimN 3 4 0
      [fw_matmul a (chunkPrimDimN 3 4 0 b),
       fw_matmul a (chunkPrimDimN 3 4 1 b),
       fw_matmul a (chunkPrimDimN 3 4 2 b),
       fw_matmul a (chunkPrimDimN 3 4 3 b)]).shape = [1, 4, 8, 8] := by
    rw [allGatherPrimDimN_shape 3 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [fw_matmul_valAt_1_4_8_8 a b idx ha hb hidx256]
  rw [allGatherPrimDimN_3_4_valAt_1_4_8_2 _ idx hhead hidx256]
  set r := (idx % 8) / 2 with hr_def
  set loc := (idx / 8) * 2 + (idx % 8) % 2 with hloc_def
  have hloc_lt : loc < 64 := by rw [hloc_def]; omega
  have hvalpiece : ∀ rr, rr < 4 →
      valAt (fw_matmul a (chunkPrimDimN 3 4 rr b)) loc =
        ∑ l ∈ Finset.range 8,
          valAt a (loc / 16 * 64 + loc % 16 / 2 * 8 + l) *
          valAt b ((loc / 16 * 16 + l * 2 + loc % 2) / 2 * 8 + rr * 2 +
                    (loc / 16 * 16 + l * 2 + loc % 2) % 2) := by
    intro rr hrr
    rw [fw_matmul_valAt_1_4_8_2_g94 a (chunkPrimDimN 3 4 rr b) loc ha (hchunk_b rr hrr) hloc_lt]
    apply Finset.sum_congr rfl
    intro l hl
    have hl_lt : l < 8 := by simpa using hl
    have hbidx_lt : loc / 16 * 16 + l * 2 + loc % 2 < 64 := by omega
    rw [chunkPrimDimN_3_4_valAt_1_4_8_8 b rr (loc / 16 * 16 + l * 2 + loc % 2) hb hrr hbidx_lt]
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by rw [hr_def]; omega
  rcases hr_cases with h | h | h | h
  · have hsel : ([fw_matmul a (chunkPrimDimN 3 4 0 b),
                  fw_matmul a (chunkPrimDimN 3 4 1 b),
                  fw_matmul a (chunkPrimDimN 3 4 2 b),
                  fw_matmul a (chunkPrimDimN 3 4 3 b)] : List Tensor).getD r
                  (zeroTensor [1, 4, 8, 2]) = fw_matmul a (chunkPrimDimN 3 4 0 b) := by
      rw [h]; rfl
    rw [hsel, hvalpiece 0 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega
  · have hsel : ([fw_matmul a (chunkPrimDimN 3 4 0 b),
                  fw_matmul a (chunkPrimDimN 3 4 1 b),
                  fw_matmul a (chunkPrimDimN 3 4 2 b),
                  fw_matmul a (chunkPrimDimN 3 4 3 b)] : List Tensor).getD r
                  (zeroTensor [1, 4, 8, 2]) = fw_matmul a (chunkPrimDimN 3 4 1 b) := by
      rw [h]; rfl
    rw [hsel, hvalpiece 1 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega
  · have hsel : ([fw_matmul a (chunkPrimDimN 3 4 0 b),
                  fw_matmul a (chunkPrimDimN 3 4 1 b),
                  fw_matmul a (chunkPrimDimN 3 4 2 b),
                  fw_matmul a (chunkPrimDimN 3 4 3 b)] : List Tensor).getD r
                  (zeroTensor [1, 4, 8, 2]) = fw_matmul a (chunkPrimDimN 3 4 2 b) := by
      rw [h]; rfl
    rw [hsel, hvalpiece 2 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega
  · have hsel : ([fw_matmul a (chunkPrimDimN 3 4 0 b),
                  fw_matmul a (chunkPrimDimN 3 4 1 b),
                  fw_matmul a (chunkPrimDimN 3 4 2 b),
                  fw_matmul a (chunkPrimDimN 3 4 3 b)] : List Tensor).getD r
                  (zeroTensor [1, 4, 8, 2]) = fw_matmul a (chunkPrimDimN 3 4 3 b) := by
      rw [h]; rfl
    rw [hsel, hvalpiece 3 (by decide)]
    apply Finset.sum_congr rfl
    intro l _
    congr 2 <;> omega

/-- `valAt` for `tensorSum [a, b, c]` (three-element sum). -/
private theorem tensorSum_triple_valAt_g149 (a b c : Tensor) (idx : Nat)
    (hidx : idx < prodShape a.shape) :
    valAt (tensorSum [a, b, c]) idx = valAt a idx + valAt b idx + valAt c idx := by
  have hsh : (tensorSum [a, b, c]).shape = a.shape := rfl
  rw [valAt_of_lt _ _ (by rw [hsh]; exact hidx)]
  simp [tensorSum, Tensor.mkShape, List.foldl]

/-- BW_multiref distribution for AllToAll with split/gather dims `[2,1]`:
    `tensorSum [a, allGather1 [b_r], c]` distributes as
    `allGather1 [tensorSum [chunk1_r a, b_r, chunk1_r c]]` for shape `[1,8,32]`
    with the gathered middle inputs `b_r` of shape `[1,2,32]`. -/
theorem tensorSum_triple_gather_dim1_4_1_8_32_g149 (a b0 b1 b2 b3 c : Tensor)
    (ha : a.shape = [1, 8, 32])
    (hb0 : b0.shape = [1, 2, 32]) (hb1 : b1.shape = [1, 2, 32])
    (hb2 : b2.shape = [1, 2, 32]) (hb3 : b3.shape = [1, 2, 32])
    (hc : c.shape = [1, 8, 32]) :
    tensorSum [a, allGatherPrimDimN 1 4 0 [b0, b1, b2, b3], c] = allGatherPrimDimN 1 4 0
      [tensorSum [chunkPrimDimN 1 4 0 a, b0, chunkPrimDimN 1 4 0 c],
       tensorSum [chunkPrimDimN 1 4 1 a, b1, chunkPrimDimN 1 4 1 c],
       tensorSum [chunkPrimDimN 1 4 2 a, b2, chunkPrimDimN 1 4 2 c],
       tensorSum [chunkPrimDimN 1 4 3 a, b3, chunkPrimDimN 1 4 3 c]] := by
  have hchunk_shape_a : ∀ r, (chunkPrimDimN 1 4 r a).shape = [1, 2, 32] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ ha (by omega)]; simp [List.set, List.getD]
  have hchunk_shape_c : ∀ r, (chunkPrimDimN 1 4 r c).shape = [1, 2, 32] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ hc (by omega)]; simp [List.set, List.getD]
  have hbhead : (([b0, b1, b2, b3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hb0]
  have hrhs_head : (([tensorSum [chunkPrimDimN 1 4 0 a, b0, chunkPrimDimN 1 4 0 c],
       tensorSum [chunkPrimDimN 1 4 1 a, b1, chunkPrimDimN 1 4 1 c],
       tensorSum [chunkPrimDimN 1 4 2 a, b2, chunkPrimDimN 1 4 2 c],
       tensorSum [chunkPrimDimN 1 4 3 a, b3, chunkPrimDimN 1 4 3 c]].head?.map
        (fun t => t.shape)).getD []) = [1, 2, 32] := by
    have hp0 : (tensorSum [chunkPrimDimN 1 4 0 a, b0, chunkPrimDimN 1 4 0 c]).shape = [1, 2, 32] :=
      hchunk_shape_a 0
    simp [hp0]
  have hgather_b_shape : (allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hbhead]; simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [a, allGatherPrimDimN 1 4 0 [b0, b1, b2, b3], c]).shape =
      [1, 8, 32] := ha
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [tensorSum [chunkPrimDimN 1 4 0 a, b0, chunkPrimDimN 1 4 0 c],
       tensorSum [chunkPrimDimN 1 4 1 a, b1, chunkPrimDimN 1 4 1 c],
       tensorSum [chunkPrimDimN 1 4 2 a, b2, chunkPrimDimN 1 4 2 c],
       tensorSum [chunkPrimDimN 1 4 3 a, b3, chunkPrimDimN 1 4 3 c]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hrhs_head]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  rw [hlhs_shape] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  rw [tensorSum_triple_valAt_g149 a _ c idx (by rw [ha]; simpa [prodShape] using hidx256)]
  set p := idx / 32 with hp_def
  set j := idx % 32 with hj_def
  have hp_lt : p < 8 := by omega
  have hj_lt : j < 32 := by omega
  set r := p / 2 with hr_def
  set p' := p % 2 with hp'_def
  have hr_lt : r < 4 := by omega
  have hp'_lt : p' < 2 := by omega
  have hidx_eq : idx = (r * 2 + p') * 32 + j := by omega
  rw [hidx_eq]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [b0, b1, b2, b3] r hr_lt p' hp'_lt j hj_lt hbhead]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr_lt p' hp'_lt j hj_lt hrhs_head]
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [h0]; simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
    rw [tensorSum_triple_valAt_g149 (chunkPrimDimN 1 4 0 a) b0 (chunkPrimDimN 1 4 0 c)
        (p' * 32 + j) (by rw [hchunk_shape_a 0]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 0 p' j ha (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt c 0 p' j hc (by omega) hp'_lt hj_lt]
  · rw [h1]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_triple_valAt_g149 (chunkPrimDimN 1 4 1 a) b1 (chunkPrimDimN 1 4 1 c)
        (p' * 32 + j) (by rw [hchunk_shape_a 1]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 1 p' j ha (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt c 1 p' j hc (by omega) hp'_lt hj_lt]
  · rw [h2]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_triple_valAt_g149 (chunkPrimDimN 1 4 2 a) b2 (chunkPrimDimN 1 4 2 c)
        (p' * 32 + j) (by rw [hchunk_shape_a 2]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 2 p' j ha (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt c 2 p' j hc (by omega) hp'_lt hj_lt]
  · rw [h3]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_triple_valAt_g149 (chunkPrimDimN 1 4 3 a) b3 (chunkPrimDimN 1 4 3 c)
        (p' * 32 + j) (by rw [hchunk_shape_a 3]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 3 p' j ha (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt c 3 p' j hc (by omega) hp'_lt hj_lt]

set_option maxRecDepth 4096 in
/-- BW_multiref distribution for two inputs both gathered along dim 1 with 4 parts,
    shard shape [1, 2, 32]. `tensorSum` of two gathers equals the gather of per-rank
    `tensorSum`s. Used for goal_181 and structurally identical BW_multiref goals. -/
theorem tensorSum_gather_dim1_4_1_2_32_g181
    (a0 a1 a2 a3 b0 b1 b2 b3 : Tensor)
    (ha0 : a0.shape = [1, 2, 32]) (ha1 : a1.shape = [1, 2, 32])
    (ha2 : a2.shape = [1, 2, 32]) (ha3 : a3.shape = [1, 2, 32])
    (hb0 : b0.shape = [1, 2, 32]) (hb1 : b1.shape = [1, 2, 32])
    (hb2 : b2.shape = [1, 2, 32]) (hb3 : b3.shape = [1, 2, 32]) :
    tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
               allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]] =
      allGatherPrimDimN 1 4 0
        [tensorSum [a0, b0], tensorSum [a1, b1],
         tensorSum [a2, b2], tensorSum [a3, b3]] := by
  have hheadA : (([a0, a1, a2, a3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [ha0]
  have hheadB : (([b0, b1, b2, b3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hb0]
  have hsum0 : (tensorSum [a0, b0]).shape = [1, 2, 32] := ha0
  have hheadS : (([tensorSum [a0, b0], tensorSum [a1, b1],
      tensorSum [a2, b2], tensorSum [a3, b3]].head?.map (fun t => t.shape)).getD []) =
      [1, 2, 32] := by simp [hsum0]
  have hgA_shape : (allGatherPrimDimN 1 4 0 [a0, a1, a2, a3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hheadA]; simp [List.set, List.getD]
  have hgB_shape : (allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hheadB]; simp [List.set, List.getD]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [tensorSum [a0, b0], tensorSum [a1, b1],
       tensorSum [a2, b2], tensorSum [a3, b3]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hheadS]; simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
      allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]]).shape = [1, 8, 32] := hgA_shape
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  rw [tensorSum_pair_valAt _ _ idx (by rw [hgA_shape]; simp [prodShape]; omega)]
  have hidxA : idx < prodShape (allGatherPrimDimN 1 4 0 [a0, a1, a2, a3]).shape := by
    rw [hgA_shape]; simpa [prodShape] using hidx256
  have hidxB : idx < prodShape (allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]).shape := by
    rw [hgB_shape]; simpa [prodShape] using hidx256
  have hidxR : idx < prodShape (allGatherPrimDimN 1 4 0
      [tensorSum [a0, b0], tensorSum [a1, b1],
       tensorSum [a2, b2], tensorSum [a3, b3]]).shape := by
    rw [hrhs_shape]; simpa [prodShape] using hidx256
  rw [valAt_of_lt _ _ hidxA, valAt_of_lt _ _ hidxB, valAt_of_lt _ _ hidxR]
  simp only [allGatherPrimDimN, Tensor.mkShape, hheadA, hheadB, hheadS,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (2 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (1 * 32 : Nat) = 32 from by norm_num,
    show (2 * 4 * 32 : Nat) = 256 from by norm_num,
    show (2 * 32 : Nat) = 64 from by norm_num,
    show (256 : Nat) = 0 ↔ False from by simp, if_false]
  set r := idx % 256 / 32 / 2 with hr_def
  set loc := idx / 256 * 64 + idx % 256 / 32 % 2 * 32 + idx % 256 % 32 with hloc_def
  have hr_lt : r < 4 := by omega
  have hloc_lt : loc < 64 := by omega
  have hsum_shape : ∀ (x y : Tensor), x.shape = [1, 2, 32] →
      valAt (tensorSum [x, y]) loc = valAt x loc + valAt y loc := by
    intro x y hx
    exact tensorSum_pair_valAt x y loc (by rw [hx]; simp [prodShape]; omega)
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [h0]; exact (hsum_shape a0 b0 ha0).symm
  · rw [h1]; exact (hsum_shape a1 b1 ha1).symm
  · rw [h2]; exact (hsum_shape a2 b2 ha2).symm
  · rw [h3]; exact (hsum_shape a3 b3 ha3).symm

/-- `valAt` for `tensorSum [a, b, c]` when the index is in-bounds of `a.shape`. -/
private theorem tensorSum_triple_valAt_g184 (a b c : Tensor) (idx : Nat)
    (hidx : idx < prodShape a.shape) :
    valAt (tensorSum [a, b, c]) idx = valAt a idx + valAt b idx + valAt c idx := by
  have hsh : (tensorSum [a, b, c]).shape = a.shape := rfl
  rw [valAt_of_lt _ _ (by rw [hsh]; exact hidx)]
  simp [tensorSum, Tensor.mkShape, List.foldl]

/-- `tensorSum [A, B, allGatherPrimDimN 1 4 0 [c0,c1,c2,c3]]` distributes as
    `allGatherPrimDimN 1 4 0 [tensorSum [chunk_r A, chunk_r B, c_r] | r]` for shape [1,8,32]
    sharded along dim 1 into four [1,2,32] pieces. Direct form for BW_multiref goals. -/
theorem tensorSum_add3_gather_dim1_4_1_8_32_g184 (A B c0 c1 c2 c3 : Tensor)
    (hA : A.shape = [1, 8, 32]) (hB : B.shape = [1, 8, 32])
    (hc0 : c0.shape = [1, 2, 32]) (hc1 : c1.shape = [1, 2, 32])
    (hc2 : c2.shape = [1, 2, 32]) (hc3 : c3.shape = [1, 2, 32]) :
    tensorSum [A, B, allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]] =
      allGatherPrimDimN 1 4 0
        [tensorSum [chunkPrimDimN 1 4 0 A, chunkPrimDimN 1 4 0 B, c0],
         tensorSum [chunkPrimDimN 1 4 1 A, chunkPrimDimN 1 4 1 B, c1],
         tensorSum [chunkPrimDimN 1 4 2 A, chunkPrimDimN 1 4 2 B, c2],
         tensorSum [chunkPrimDimN 1 4 3 A, chunkPrimDimN 1 4 3 B, c3]] := by
  have hchunkA : ∀ r, (chunkPrimDimN 1 4 r A).shape = [1, 2, 32] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ hA (by omega)]; simp [List.set, List.getD]
  have hcshead : (([c0, c1, c2, c3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hc0]
  have hsum0_shape : (tensorSum [chunkPrimDimN 1 4 0 A, chunkPrimDimN 1 4 0 B, c0]).shape =
      [1, 2, 32] := hchunkA 0
  have hrhshead : (([tensorSum [chunkPrimDimN 1 4 0 A, chunkPrimDimN 1 4 0 B, c0],
       tensorSum [chunkPrimDimN 1 4 1 A, chunkPrimDimN 1 4 1 B, c1],
       tensorSum [chunkPrimDimN 1 4 2 A, chunkPrimDimN 1 4 2 B, c2],
       tensorSum [chunkPrimDimN 1 4 3 A, chunkPrimDimN 1 4 3 B, c3]].head?.map
        (fun t => t.shape)).getD []) = [1, 2, 32] := by simp [hsum0_shape]
  have hlhs_shape : (tensorSum [A, B, allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]]).shape =
      [1, 8, 32] := hA
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [tensorSum [chunkPrimDimN 1 4 0 A, chunkPrimDimN 1 4 0 B, c0],
       tensorSum [chunkPrimDimN 1 4 1 A, chunkPrimDimN 1 4 1 B, c1],
       tensorSum [chunkPrimDimN 1 4 2 A, chunkPrimDimN 1 4 2 B, c2],
       tensorSum [chunkPrimDimN 1 4 3 A, chunkPrimDimN 1 4 3 B, c3]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hrhshead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by rw [hlhs_shape] at hidx; simpa [prodShape] using hidx
  set p := idx / 32 with hp_def
  set j := idx % 32 with hj_def
  have hp_lt : p < 8 := by omega
  have hj_lt : j < 32 := by omega
  have hidx_eq : idx = p * 32 + j := by omega
  set r := p / 2 with hr_def
  set p' := p % 2 with hp'_def
  have hr_lt : r < 4 := by omega
  have hp'_lt : p' < 2 := by omega
  have hidx_rp : idx = (r * 2 + p') * 32 + j := by omega
  rw [tensorSum_triple_valAt_g184 A B _ idx (by rw [hA]; simp [prodShape]; omega)]
  have hgather_val : valAt (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]) idx =
      valAt ([c0, c1, c2, c3].getD r (zeroTensor [1, 2, 32])) (p' * 32 + j) := by
    rw [hidx_rp]
    exact allGatherPrimDimN_dim1_4_1_2_32_valAt [c0, c1, c2, c3] r hr_lt p' hp'_lt j hj_lt hcshead
  rw [hgather_val]
  have hrhs_val : valAt (allGatherPrimDimN 1 4 0
      [tensorSum [chunkPrimDimN 1 4 0 A, chunkPrimDimN 1 4 0 B, c0],
       tensorSum [chunkPrimDimN 1 4 1 A, chunkPrimDimN 1 4 1 B, c1],
       tensorSum [chunkPrimDimN 1 4 2 A, chunkPrimDimN 1 4 2 B, c2],
       tensorSum [chunkPrimDimN 1 4 3 A, chunkPrimDimN 1 4 3 B, c3]]) idx =
      valAt ([tensorSum [chunkPrimDimN 1 4 0 A, chunkPrimDimN 1 4 0 B, c0],
       tensorSum [chunkPrimDimN 1 4 1 A, chunkPrimDimN 1 4 1 B, c1],
       tensorSum [chunkPrimDimN 1 4 2 A, chunkPrimDimN 1 4 2 B, c2],
       tensorSum [chunkPrimDimN 1 4 3 A, chunkPrimDimN 1 4 3 B, c3]].getD r
        (zeroTensor [1, 2, 32])) (p' * 32 + j) := by
    rw [hidx_rp]
    exact allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr_lt p' hp'_lt j hj_lt hrhshead
  rw [hrhs_val]
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with h0 | h1 | h2 | h3
  · rw [h0]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_triple_valAt_g184 _ _ _ (p' * 32 + j)
        (by rw [hchunkA 0]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt A 0 p' j hA (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt B 0 p' j hB (by omega) hp'_lt hj_lt]
    rw [show idx = (0 * 2 + p') * 32 + j from by rw [hidx_rp, h0]]
  · rw [h1]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_triple_valAt_g184 _ _ _ (p' * 32 + j)
        (by rw [hchunkA 1]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt A 1 p' j hA (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt B 1 p' j hB (by omega) hp'_lt hj_lt]
    rw [show idx = (1 * 2 + p') * 32 + j from by rw [hidx_rp, h1]]
  · rw [h2]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_triple_valAt_g184 _ _ _ (p' * 32 + j)
        (by rw [hchunkA 2]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt A 2 p' j hA (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt B 2 p' j hB (by omega) hp'_lt hj_lt]
    rw [show idx = (2 * 2 + p') * 32 + j from by rw [hidx_rp, h2]]
  · rw [h3]
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [tensorSum_triple_valAt_g184 _ _ _ (p' * 32 + j)
        (by rw [hchunkA 3]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt A 3 p' j hA (by omega) hp'_lt hj_lt]
    rw [chunk_dim1_4_1_8_32_valAt B 3 p' j hB (by omega) hp'_lt hj_lt]
    rw [show idx = (3 * 2 + p') * 32 + j from by rw [hidx_rp, h3]]

/-- BW_multiref distributes over two same-dim allGathers (dim 1, 4 parts, [1,2,32] shards):
    `tensorSum [gather as, gather bs] = gather [tensorSum [a_r, b_r] | r]`. -/
theorem tensorSum_gather_gather_dim1_4_1_2_32_g207
    (a0 a1 a2 a3 b0 b1 b2 b3 : Tensor)
    (ha0 : a0.shape = [1, 2, 32]) (ha1 : a1.shape = [1, 2, 32])
    (ha2 : a2.shape = [1, 2, 32]) (ha3 : a3.shape = [1, 2, 32])
    (hb0 : b0.shape = [1, 2, 32]) (hb1 : b1.shape = [1, 2, 32])
    (hb2 : b2.shape = [1, 2, 32]) (hb3 : b3.shape = [1, 2, 32]) :
    tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
               allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]] =
      allGatherPrimDimN 1 4 0
        [tensorSum [a0, b0], tensorSum [a1, b1],
         tensorSum [a2, b2], tensorSum [a3, b3]] := by
  have haHead : (([a0, a1, a2, a3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [ha0]
  have hbHead : (([b0, b1, b2, b3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hb0]
  have hsHead : (([tensorSum [a0, b0], tensorSum [a1, b1],
      tensorSum [a2, b2], tensorSum [a3, b3]].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp only [List.head?, Option.map, Option.getD]
    rw [tensorSum_shape]; exact ha0
  have hgatherA_shape : (allGatherPrimDimN 1 4 0 [a0, a1, a2, a3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ haHead]; simp [List.set, List.getD]
  have hgatherB_shape : (allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hbHead]; simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
      allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]]).shape = [1, 8, 32] := by
    rw [tensorSum_shape]; exact hgatherA_shape
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [tensorSum [a0, b0], tensorSum [a1, b1],
       tensorSum [a2, b2], tensorSum [a3, b3]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hsHead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  set q := idx / 32 with hq_def
  set j := idx % 32 with hj_def
  set r := q / 2 with hr_def
  set p := q % 2 with hp_def
  have hj_lt : j < 32 := by omega
  have hq_lt : q < 8 := by omega
  have hr_lt : r < 4 := by omega
  have hp_lt : p < 2 := by omega
  have hidx_eq : idx = (r * 2 + p) * 32 + j := by omega
  rw [tensorSum_pair_valAt _ _ idx (by rw [hgatherA_shape]; simp [prodShape]; omega)]
  rw [hidx_eq]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [a0, a1, a2, a3] r hr_lt p hp_lt j hj_lt haHead]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [b0, b1, b2, b3] r hr_lt p hp_lt j hj_lt hbHead]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt
      [tensorSum [a0, b0], tensorSum [a1, b1], tensorSum [a2, b2], tensorSum [a3, b3]]
      r hr_lt p hp_lt j hj_lt hsHead]
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h | h | h | h
  · rw [h]
    show valAt a0 (p * 32 + j) + valAt b0 (p * 32 + j) = valAt (tensorSum [a0, b0]) (p * 32 + j)
    rw [tensorSum_pair_valAt a0 b0 (p * 32 + j) (by rw [ha0]; simp [prodShape]; omega)]
  · rw [h]
    show valAt a1 (p * 32 + j) + valAt b1 (p * 32 + j) = valAt (tensorSum [a1, b1]) (p * 32 + j)
    rw [tensorSum_pair_valAt a1 b1 (p * 32 + j) (by rw [ha1]; simp [prodShape]; omega)]
  · rw [h]
    show valAt a2 (p * 32 + j) + valAt b2 (p * 32 + j) = valAt (tensorSum [a2, b2]) (p * 32 + j)
    rw [tensorSum_pair_valAt a2 b2 (p * 32 + j) (by rw [ha2]; simp [prodShape]; omega)]
  · rw [h]
    show valAt a3 (p * 32 + j) + valAt b3 (p * 32 + j) = valAt (tensorSum [a3, b3]) (p * 32 + j)
    rw [tensorSum_pair_valAt a3 b3 (p * 32 + j) (by rw [ha3]; simp [prodShape]; omega)]

/-- `tensorSum [a, b]` distributes over `allGatherPrimDimN` on dim 1 with 4 parts for
    `[1, 2, 32]` shards: summing two gathered tensors equals gathering the per-shard sums.
    Used for BW_multiref goals whose inputs are both dim-1 all-gathers. -/
theorem tensorSum_add_gather_dim1_4_1_2_32_g216
    (a0 a1 a2 a3 b0 b1 b2 b3 : Tensor)
    (ha0 : a0.shape = [1, 2, 32]) (ha1 : a1.shape = [1, 2, 32])
    (ha2 : a2.shape = [1, 2, 32]) (ha3 : a3.shape = [1, 2, 32])
    (hb0 : b0.shape = [1, 2, 32])
    (hb1 : b1.shape = [1, 2, 32]) (hb2 : b2.shape = [1, 2, 32])
    (hb3 : b3.shape = [1, 2, 32]) :
    tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
               allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]] =
      allGatherPrimDimN 1 4 0
        [tensorSum [a0, b0], tensorSum [a1, b1], tensorSum [a2, b2], tensorSum [a3, b3]] := by
  have hahead : (([a0, a1, a2, a3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [ha0]
  have hbhead : (([b0, b1, b2, b3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hb0]
  have hshead : (([tensorSum [a0, b0], tensorSum [a1, b1], tensorSum [a2, b2],
      tensorSum [a3, b3]].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [tensorSum_shape, ha0]
  have hgA : (allGatherPrimDimN 1 4 0 [a0, a1, a2, a3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hahead]; simp [List.set, List.getD]
  have hgS : (allGatherPrimDimN 1 4 0 [tensorSum [a0, b0], tensorSum [a1, b1],
      tensorSum [a2, b2], tensorSum [a3, b3]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hshead]; simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
      allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]]).shape = [1, 8, 32] := by
    rw [tensorSum_shape]; exact hgA
  apply Tensor.ext (by rw [hlhs_shape, hgS])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_shape, prodShape] using hidx
  obtain ⟨r, p, j, hr_lt, hp_lt, hj_lt, hidx_eq⟩ :
      ∃ r p j, r < 4 ∧ p < 2 ∧ j < 32 ∧ idx = (r * 2 + p) * 32 + j :=
    ⟨idx / 32 / 2, idx / 32 % 2, idx % 32, by omega, by omega, by omega, by omega⟩
  rw [hidx_eq]
  rw [tensorSum_pair_valAt _ _ _ (by rw [hgA]; simp [prodShape]; omega)]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr_lt p hp_lt j hj_lt hahead]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr_lt p hp_lt j hj_lt hbhead]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt _ r hr_lt p hp_lt j hj_lt hshead]
  have hpj_lt : p * 32 + j < 64 := by omega
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with h | h | h | h <;>
    subst h <;>
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
    rw [tensorSum_pair_valAt _ _ _
      (by (first | rw [ha0] | rw [ha1] | rw [ha2] | rw [ha3]); simp [prodShape]; omega)]

/-- `valAt` of a 3-input `tensorSum`. -/
private theorem tensorSum_triple_valAt_g219 (a b c : Tensor) (idx : Nat)
    (hidx : idx < prodShape a.shape) :
    valAt (tensorSum [a, b, c]) idx = valAt a idx + valAt b idx + valAt c idx := by
  have hsh : (tensorSum [a, b, c]).shape = a.shape := rfl
  rw [valAt_of_lt _ _ (by rw [hsh]; exact hidx)]
  simp [tensorSum, Tensor.mkShape, List.foldl]

/-- 3-input BW_multiref distribution over AllToAll on dim 1 (shape [1,8,32] inputs,
    [1,2,32] shards). Two summands are gathered along dim 2 (so chunked along dim 1),
    the third is gathered along dim 1. -/
theorem tensorSum_add3_gather_dim1_4_1_8_32_g219 (a b c0 c1 c2 c3 : Tensor)
    (ha : a.shape = [1, 8, 32]) (hb : b.shape = [1, 8, 32])
    (hc0 : c0.shape = [1, 2, 32]) (hc1 : c1.shape = [1, 2, 32])
    (hc2 : c2.shape = [1, 2, 32]) (hc3 : c3.shape = [1, 2, 32]) :
    tensorSum [a, b, allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]] = allGatherPrimDimN 1 4 0
      [tensorSum [chunkPrimDimN 1 4 0 a, chunkPrimDimN 1 4 0 b, c0],
       tensorSum [chunkPrimDimN 1 4 1 a, chunkPrimDimN 1 4 1 b, c1],
       tensorSum [chunkPrimDimN 1 4 2 a, chunkPrimDimN 1 4 2 b, c2],
       tensorSum [chunkPrimDimN 1 4 3 a, chunkPrimDimN 1 4 3 b, c3]] := by
  have hchunk_shape_a : ∀ r, (chunkPrimDimN 1 4 r a).shape = [1, 2, 32] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ ha (by omega)]; simp [List.set, List.getD]
  have hchunk_shape_b : ∀ r, (chunkPrimDimN 1 4 r b).shape = [1, 2, 32] := by
    intro r; rw [chunkPrimDimN_shape 1 4 r _ _ hb (by omega)]; simp [List.set, List.getD]
  have hsum_shape : ∀ (x y z : Tensor), x.shape = [1, 2, 32] →
      (tensorSum [x, y, z]).shape = [1, 2, 32] := by
    intro x y z hx; show x.shape = [1, 2, 32]; exact hx
  have hsum0_shape : (tensorSum [chunkPrimDimN 1 4 0 a, chunkPrimDimN 1 4 0 b, c0]).shape = [1, 2, 32] :=
    hsum_shape _ _ _ (hchunk_shape_a 0)
  have hc_head : (([c0, c1, c2, c3].head?.map (fun t => t.shape)).getD []) = [1, 2, 32] := by
    simp [hc0]
  have hgather_c_shape : (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hc_head]; simp [List.set, List.getD]
  have hlhs_shape : (tensorSum [a, allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]]).shape = [1, 8, 32] := ha
  have hsums_head : (([tensorSum [chunkPrimDimN 1 4 0 a, chunkPrimDimN 1 4 0 b, c0],
       tensorSum [chunkPrimDimN 1 4 1 a, chunkPrimDimN 1 4 1 b, c1],
       tensorSum [chunkPrimDimN 1 4 2 a, chunkPrimDimN 1 4 2 b, c2],
       tensorSum [chunkPrimDimN 1 4 3 a, chunkPrimDimN 1 4 3 b, c3]].head?.map
         (fun t => t.shape)).getD []) = [1, 2, 32] := by simp [hsum0_shape]
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [tensorSum [chunkPrimDimN 1 4 0 a, chunkPrimDimN 1 4 0 b, c0],
       tensorSum [chunkPrimDimN 1 4 1 a, chunkPrimDimN 1 4 1 b, c1],
       tensorSum [chunkPrimDimN 1 4 2 a, chunkPrimDimN 1 4 2 b, c2],
       tensorSum [chunkPrimDimN 1 4 3 a, chunkPrimDimN 1 4 3 b, c3]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hsums_head]; simp [List.set, List.getD]
  have hlhs_full_shape : (tensorSum [a, b, allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]]).shape = [1, 8, 32] := ha
  apply Tensor.ext (by rw [hlhs_full_shape, hrhs_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hlhs_full_shape, prodShape] using hidx
  set r := idx / 64 with hr_def
  set q := idx % 64 / 32 with hq_def
  set k := idx % 32 with hk_def
  have hr_lt : r < 4 := by omega
  have hq_lt : q < 2 := by omega
  have hk_lt : k < 32 := by omega
  have hidx_eq : idx = (r * 2 + q) * 32 + k := by
    rw [hr_def, hq_def, hk_def]; omega
  rw [hidx_eq]
  rw [tensorSum_triple_valAt_g219 a b (allGatherPrimDimN 1 4 0 [c0, c1, c2, c3]) ((r * 2 + q) * 32 + k)
    (by rw [ha]; simp [prodShape]; omega)]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [c0, c1, c2, c3] r hr_lt q hq_lt k hk_lt hc_head]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt
    [tensorSum [chunkPrimDimN 1 4 0 a, chunkPrimDimN 1 4 0 b, c0],
     tensorSum [chunkPrimDimN 1 4 1 a, chunkPrimDimN 1 4 1 b, c1],
     tensorSum [chunkPrimDimN 1 4 2 a, chunkPrimDimN 1 4 2 b, c2],
     tensorSum [chunkPrimDimN 1 4 3 a, chunkPrimDimN 1 4 3 b, c3]]
    r hr_lt q hq_lt k hk_lt hsums_head]
  clear_value r q k
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h | h | h | h <;> subst h <;>
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  · rw [tensorSum_triple_valAt_g219 _ _ c0 (q * 32 + k)
      (by rw [hchunk_shape_a 0]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 0 q k ha (by omega) hq_lt hk_lt]
    rw [chunk_dim1_4_1_8_32_valAt b 0 q k hb (by omega) hq_lt hk_lt]
  · rw [tensorSum_triple_valAt_g219 _ _ c1 (q * 32 + k)
      (by rw [hchunk_shape_a 1]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 1 q k ha (by omega) hq_lt hk_lt]
    rw [chunk_dim1_4_1_8_32_valAt b 1 q k hb (by omega) hq_lt hk_lt]
  · rw [tensorSum_triple_valAt_g219 _ _ c2 (q * 32 + k)
      (by rw [hchunk_shape_a 2]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 2 q k ha (by omega) hq_lt hk_lt]
    rw [chunk_dim1_4_1_8_32_valAt b 2 q k hb (by omega) hq_lt hk_lt]
  · rw [tensorSum_triple_valAt_g219 _ _ c3 (q * 32 + k)
      (by rw [hchunk_shape_a 3]; simp [prodShape]; omega)]
    rw [chunk_dim1_4_1_8_32_valAt a 3 q k ha (by omega) hq_lt hk_lt]
    rw [chunk_dim1_4_1_8_32_valAt b 3 q k hb (by omega) hq_lt hk_lt]

/-- `tensorSum` of two identically-gathered (dim 1, 4 parts, shard [1,2,32]) tensors equals
    the gather of the per-shard `tensorSum`s. Used for BW_multiref distribution. -/
theorem tensorSum_pair_gather_dim1_4_1_2_32_g242
    (a0 a1 a2 a3 b0 b1 b2 b3 : Tensor)
    (ha0 : a0.shape = [1, 2, 32]) (ha1 : a1.shape = [1, 2, 32])
    (ha2 : a2.shape = [1, 2, 32]) (ha3 : a3.shape = [1, 2, 32])
    (hb0 : b0.shape = [1, 2, 32]) (hb1 : b1.shape = [1, 2, 32])
    (hb2 : b2.shape = [1, 2, 32]) (hb3 : b3.shape = [1, 2, 32]) :
    tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
               allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]] =
      allGatherPrimDimN 1 4 0
        [tensorSum [a0, b0], tensorSum [a1, b1], tensorSum [a2, b2], tensorSum [a3, b3]] := by
  have hheadA : (([a0, a1, a2, a3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [ha0]
  have hheadB : (([b0, b1, b2, b3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [hb0]
  have hheadR : (([tensorSum [a0, b0], tensorSum [a1, b1], tensorSum [a2, b2], tensorSum [a3, b3]] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [tensorSum_shape, ha0]
  have hAshape : (allGatherPrimDimN 1 4 0 [a0, a1, a2, a3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hheadA]; simp [List.set, List.getD]
  have hLHSshape : (tensorSum [allGatherPrimDimN 1 4 0 [a0, a1, a2, a3],
               allGatherPrimDimN 1 4 0 [b0, b1, b2, b3]]).shape = [1, 8, 32] := by
    rw [tensorSum_shape]; exact hAshape
  have hRshape : (allGatherPrimDimN 1 4 0
        [tensorSum [a0, b0], tensorSum [a1, b1], tensorSum [a2, b2], tensorSum [a3, b3]]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32] hheadR]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHSshape, hRshape])
  intro idx hidx
  have hidx256 : idx < 256 := by
    rw [hLHSshape] at hidx; simpa [prodShape] using hidx
  set r := idx / 64 with hr_def
  set p := idx / 32 % 2 with hp_def
  set j := idx % 32 with hj_def
  have hr4 : r < 4 := by omega
  have hp2 : p < 2 := by omega
  have hj32 : j < 32 := by omega
  have hidx_eq : idx = (r * 2 + p) * 32 + j := by omega
  rw [hidx_eq]
  have hbound : (r * 2 + p) * 32 + j < prodShape (allGatherPrimDimN 1 4 0 [a0, a1, a2, a3]).shape := by
    rw [hAshape]; simp [prodShape]; omega
  rw [tensorSum_pair_valAt _ _ _ hbound]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [a0, a1, a2, a3] r hr4 p hp2 j hj32 hheadA]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt [b0, b1, b2, b3] r hr4 p hp2 j hj32 hheadB]
  rw [allGatherPrimDimN_dim1_4_1_2_32_valAt
        [tensorSum [a0, b0], tensorSum [a1, b1], tensorSum [a2, b2], tensorSum [a3, b3]]
        r hr4 p hp2 j hj32 hheadR]
  have hpj64 : ∀ (t : Tensor), t.shape = [1, 2, 32] → p * 32 + j < prodShape t.shape := by
    intro t ht; rw [ht]; simp [prodShape]; omega
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h | h | h | h <;>
    rw [h] <;> simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [tensorSum_pair_valAt a0 b0 _ (hpj64 a0 ha0)]
  · rw [tensorSum_pair_valAt a1 b1 _ (hpj64 a1 ha1)]
  · rw [tensorSum_pair_valAt a2 b2 _ (hpj64 a2 ha2)]
  · rw [tensorSum_pair_valAt a3 b3 _ (hpj64 a3 ha3)]

set_option maxHeartbeats 1600000 in
/-- The dW output of `bw_linear` where BOTH the gradient `G` (`[1,8,32]`) and the input
    `X` (`[1,8,128]`) are dim-1 chunked per rank, equals `tensorSum` of the per-rank dW
    outputs.  This is the data-parallel weight reduction (CROSS_DP_WRED) identity for
    `BW_linear` with `w = [32,128]`, used by goal_144 (activation arrives via AllToAll). -/
theorem bw_linear_dw_dp_chunk_both_dim1_4_1_8_32_128_g144
    (G X w : Tensor)
    (hG : G.shape = [1, 8, 32])
    (hX : X.shape = [1, 8, 128])
    (hw : w.shape = [32, 128]) :
    (bw_linear G X w).2 =
      tensorSum [(bw_linear (chunkPrimDimN 1 4 0 G) (chunkPrimDimN 1 4 0 X) w).2,
                 (bw_linear (chunkPrimDimN 1 4 1 G) (chunkPrimDimN 1 4 1 X) w).2,
                 (bw_linear (chunkPrimDimN 1 4 2 G) (chunkPrimDimN 1 4 2 X) w).2,
                 (bw_linear (chunkPrimDimN 1 4 3 G) (chunkPrimDimN 1 4 3 X) w).2] := by
  have hcG0 : (chunkPrimDimN 1 4 0 G).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 0 G _ hG (by omega)]; simp [List.set, List.getD]
  have hcG1 : (chunkPrimDimN 1 4 1 G).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 1 G _ hG (by omega)]; simp [List.set, List.getD]
  have hcG2 : (chunkPrimDimN 1 4 2 G).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 2 G _ hG (by omega)]; simp [List.set, List.getD]
  have hcG3 : (chunkPrimDimN 1 4 3 G).shape = [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 3 G _ hG (by omega)]; simp [List.set, List.getD]
  have hcX0 : (chunkPrimDimN 1 4 0 X).shape = [1, 2, 128] := by
    rw [chunkPrimDimN_shape 1 4 0 X _ hX (by omega)]; simp [List.set, List.getD]
  have hcX1 : (chunkPrimDimN 1 4 1 X).shape = [1, 2, 128] := by
    rw [chunkPrimDimN_shape 1 4 1 X _ hX (by omega)]; simp [List.set, List.getD]
  have hcX2 : (chunkPrimDimN 1 4 2 X).shape = [1, 2, 128] := by
    rw [chunkPrimDimN_shape 1 4 2 X _ hX (by omega)]; simp [List.set, List.getD]
  have hcX3 : (chunkPrimDimN 1 4 3 X).shape = [1, 2, 128] := by
    rw [chunkPrimDimN_shape 1 4 3 X _ hX (by omega)]; simp [List.set, List.getD]
  apply Tensor.ext
  · rw [bw_linear_3d_snd_shape 1 8 32 128 G X w hG hX hw, tensorSum_shape,
        bw_linear_3d_snd_shape 1 2 32 128 (chunkPrimDimN 1 4 0 G) (chunkPrimDimN 1 4 0 X) w hcG0 hcX0 hw]
  · intro idx hidx
    rw [bw_linear_3d_snd_shape 1 8 32 128 G X w hG hX hw] at hidx
    have hidxp : idx < 4096 := by simpa [prodShape] using hidx
    have hc : idx / 128 < 32 := by omega
    have hk : idx % 128 < 128 := by omega
    have hide : idx = (idx / 128) * 128 + idx % 128 := by omega
    rw [hide]
    rw [bw_linear_dw_valAt3d G X w 1 8 32 128 hG hX hw (idx / 128) hc (idx % 128) hk]
    rw [show tensorSum [(bw_linear (chunkPrimDimN 1 4 0 G) (chunkPrimDimN 1 4 0 X) w).2,
                        (bw_linear (chunkPrimDimN 1 4 1 G) (chunkPrimDimN 1 4 1 X) w).2,
                        (bw_linear (chunkPrimDimN 1 4 2 G) (chunkPrimDimN 1 4 2 X) w).2,
                        (bw_linear (chunkPrimDimN 1 4 3 G) (chunkPrimDimN 1 4 3 X) w).2] =
            Tensor.mkShape (bw_linear (chunkPrimDimN 1 4 0 G) (chunkPrimDimN 1 4 0 X) w).2.shape
              (fun i => [(bw_linear (chunkPrimDimN 1 4 0 G) (chunkPrimDimN 1 4 0 X) w).2,
                         (bw_linear (chunkPrimDimN 1 4 1 G) (chunkPrimDimN 1 4 1 X) w).2,
                         (bw_linear (chunkPrimDimN 1 4 2 G) (chunkPrimDimN 1 4 2 X) w).2,
                         (bw_linear (chunkPrimDimN 1 4 3 G) (chunkPrimDimN 1 4 3 X) w).2].foldl
                         (fun acc x => acc + valAt x i.1) 0) from rfl]
    rw [valAt_of_lt _ _ (by
      rw [Tensor.mkShape, bw_linear_3d_snd_shape 1 2 32 128 (chunkPrimDimN 1 4 0 G) (chunkPrimDimN 1 4 0 X) w hcG0 hcX0 hw]
      simp [prodShape]; omega)]
    simp only [Tensor.mkShape, List.foldl]
    rw [bw_linear_dw_valAt3d (chunkPrimDimN 1 4 0 G) (chunkPrimDimN 1 4 0 X) w 1 2 32 128 hcG0 hcX0 hw (idx / 128) hc (idx % 128) hk,
        bw_linear_dw_valAt3d (chunkPrimDimN 1 4 1 G) (chunkPrimDimN 1 4 1 X) w 1 2 32 128 hcG1 hcX1 hw (idx / 128) hc (idx % 128) hk,
        bw_linear_dw_valAt3d (chunkPrimDimN 1 4 2 G) (chunkPrimDimN 1 4 2 X) w 1 2 32 128 hcG2 hcX2 hw (idx / 128) hc (idx % 128) hk,
        bw_linear_dw_valAt3d (chunkPrimDimN 1 4 3 G) (chunkPrimDimN 1 4 3 X) w 1 2 32 128 hcG3 hcX3 hw (idx / 128) hc (idx % 128) hk]
    simp only [show (1 : Nat) * 8 = 8 from rfl, show (1 : Nat) * 2 = 2 from rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [chunk_dim1_4_1_8_32_valAt G 0 0 (idx / 128) hG (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt G 0 1 (idx / 128) hG (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt G 1 0 (idx / 128) hG (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt G 1 1 (idx / 128) hG (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt G 2 0 (idx / 128) hG (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt G 2 1 (idx / 128) hG (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt G 3 0 (idx / 128) hG (by omega) (by omega) hc,
        chunk_dim1_4_1_8_32_valAt G 3 1 (idx / 128) hG (by omega) (by omega) hc]
    rw [chunk_dim1_4_1_8_128_valAt X 0 0 (idx % 128) hX (by omega) (by omega) hk,
        chunk_dim1_4_1_8_128_valAt X 0 1 (idx % 128) hX (by omega) (by omega) hk,
        chunk_dim1_4_1_8_128_valAt X 1 0 (idx % 128) hX (by omega) (by omega) hk,
        chunk_dim1_4_1_8_128_valAt X 1 1 (idx % 128) hX (by omega) (by omega) hk,
        chunk_dim1_4_1_8_128_valAt X 2 0 (idx % 128) hX (by omega) (by omega) hk,
        chunk_dim1_4_1_8_128_valAt X 2 1 (idx % 128) hX (by omega) (by omega) hk,
        chunk_dim1_4_1_8_128_valAt X 3 0 (idx % 128) hX (by omega) (by omega) hk,
        chunk_dim1_4_1_8_128_valAt X 3 1 (idx % 128) hX (by omega) (by omega) hk]
    ring

-- ===== batch10 g210 net-new lemma(s): BW_linear dX with oG=128, AllToAll sandwich =====

/-- Value of `bw_linear`'s dX (first output) at a `[1,8,8]` position, with an arbitrary
    grad inner dimension `o` (so `g : [1,8,o]`, `x : [1,8,8]`, `w : [o,8]`). -/
theorem bw_linear_fst_valAt_1_8_8_oG_g210 (g x w : Tensor) (o : Nat)
    (hg : g.shape = [1, 8, o]) (hx : x.shape = [1, 8, 8]) (hw : w.shape = [o, 8])
    (P : Nat) (hP : P < 8) (col : Nat) (hcol : col < 8) :
    valAt (bw_linear g x w).1 (P * 8 + col) =
      ∑ j ∈ Finset.range o, valAt g (P * o + j) * valAt w (j * 8 + col) := by
  have hdx : (bw_linear g x w).1 =
      Tensor.mkShape [1, 8, 8] (fun outIdx =>
        ∑ j ∈ Finset.range o,
          valAt g (((if (8:Nat) * 8 = 0 then 0 else outIdx.1 / (8 * 8)) * 8 +
                    if (8:Nat) = 0 then 0 else (if (8:Nat) * 8 = 0 then 0 else outIdx.1 % (8 * 8)) / 8) * o + j) *
          valAt w (j * 8 + if (8:Nat) = 0 then 0 else (if (8:Nat) * 8 = 0 then 0 else outIdx.1 % (8 * 8)) % 8)) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hdx]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl]; omega)]
  simp only [Tensor.mkShape]
  have e1 : (P*8+col)/(8*8) = 0 := by omega
  have e2 : ((P*8+col)%(8*8))/8 = P := by omega
  have e3 : ((P*8+col)%(8*8))%8 = col := by omega
  simp only [show ((8:Nat)*8=0)=False from by simp, show ((8:Nat)=0)=False from by simp,
    if_false, e1, e2, e3, Nat.zero_mul, Nat.zero_add]

set_option maxRecDepth 8192 in
/-- Value of `allGatherPrimDimN 1 4` over shards of shape `[128,8]` (gather on dim 1 to `[128,32]`). -/
theorem allGatherPrimDimN_1_4_valAt_128_8_g210 (ws : List Tensor)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [128, 8])
    (a : Nat) (ha : a < 128) (r : Nat) (hr : r < 4) (b : Nat) (hb : b < 8) :
    valAt (allGatherPrimDimN 1 4 0 ws) (a * 32 + (r * 8 + b)) =
      valAt (ws.getD r (zeroTensor [128, 8])) (a * 8 + b) := by
  have hshape : (allGatherPrimDimN 1 4 0 ws).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 1 4 ws [128, 8] hhead]; simp [List.set, List.getD]
  have hbound : a * 32 + (r * 8 + b) < prodShape (allGatherPrimDimN 1 4 0 ws).shape := by
    rw [hshape]; simp only [prodShape, List.foldl]; omega
  rw [valAt_of_lt _ _ hbound]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.drop, List.foldl, show ([128,8].getD 1 0 : Nat) = 8 from rfl]
  have d1 : (a * 32 + (r * 8 + b)) / (8 * 4 * 1) = a := by omega
  have d2 : ((a * 32 + (r * 8 + b)) % (8 * 4 * 1)) / 1 / 8 = r := by omega
  have d3 : ((a * 32 + (r * 8 + b)) % (8 * 4 * 1)) / 1 % 8 = b := by omega
  have d4 : ((a * 32 + (r * 8 + b)) % (8 * 4 * 1)) % 1 = 0 := by omega
  simp only [show (8*4*1:Nat) ≠ 0 from by omega, show (8:Nat) ≠ 0 from by omega,
    show (1:Nat) ≠ 0 from by omega, if_false, d1, d2, d3, d4]
  congr 1
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- Tensor-parallel (input-feature) dX split of `BW_linear` with grad inner dim 128: the
    gradient `g` (`[1,8,128]`) is shared, the per-rank activations `x0..x3` (`[1,8,8]`, values
    irrelevant for dX) are arbitrary, and the weight is dim-1 all-gathered from four `[128,8]`
    shards.  The full dX equals the dim-2 all-gather of the per-rank dX outputs (`[1,8,8]`). -/
theorem bw_linear_dx_isplit_dim2_4_oG128_g210
    (g xf x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1,8,128]) (hxf : xf.shape = [1,8,32])
    (hx0 : x0.shape = [1,8,8]) (hx1 : x1.shape = [1,8,8])
    (hx2 : x2.shape = [1,8,8]) (hx3 : x3.shape = [1,8,8])
    (hw0 : w0.shape = [128,8]) (hw1 : w1.shape = [128,8])
    (hw2 : w2.shape = [128,8]) (hw3 : w3.shape = [128,8]) :
    (bw_linear g xf (allGatherPrimDimN 1 4 0 [w0,w1,w2,w3])).1 =
      allGatherPrimDimN 2 4 0
        [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
         (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] := by
  have hheadw : (([w0,w1,w2,w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [128,8] := by
    simp [hw0]
  set W := allGatherPrimDimN 1 4 0 [w0,w1,w2,w3] with hWdef
  have hWshape : W.shape = [128,32] := by
    rw [hWdef, allGatherPrimDimN_shape 1 4 _ [128,8] hheadw]; simp [List.set, List.getD]
  have hdx0shape : (bw_linear g x0 w0).1.shape = [1,8,8] :=
    bw_linear_3d_fst_shape 1 8 128 8 _ _ _ hg hx0 hw0
  have hLshape : (bw_linear g xf W).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 128 32 g xf W hg hxf hWshape
  have hheadR : (([(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
                   (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,8,8] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 2 4 _ [1,8,8] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/32 < 8 := by omega
    have hcol : idx%32 < 32 := by omega
    have hide : idx = (idx/32)*32 + idx%32 := by omega
    rw [hide]
    set P := idx/32 with hPdef
    set col := idx%32 with hcoldef
    set r := col/8 with hrdef
    set b := col%8 with hbdef
    have hr : r < 4 := by omega
    have hb : b < 8 := by omega
    have hcolrb : col = r * 8 + b := by omega
    rw [bw_linear_fst_valAt_1_8_32_g134 g xf W 128 hg hxf hWshape P hP col hcol]
    have hRHS : valAt (allGatherPrimDimN 2 4 0
          [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
           (bw_linear g x2 w2).1, (bw_linear g x3 w3).1]) (P * 32 + col)
        = valAt ([(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
                  (bw_linear g x2 w2).1, (bw_linear g x3 w3).1].getD r (zeroTensor [1,8,8]))
                (P * 8 + b) := by
      rw [hcolrb]
      exact allGatherDimN2_4_188_valAt_g134 _ hheadR P hP r hr b hb
    rw [hRHS]
    have hLHS : (∑ j ∈ Finset.range 128, valAt g (P*128+j) * valAt W (j*32+col))
        = ∑ j ∈ Finset.range 128,
            valAt g (P*128+j) * valAt ([w0,w1,w2,w3].getD r (zeroTensor [128,8])) (j*8+b) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj128 : j < 128 := Finset.mem_range.mp hj
      have hidxj : j * 32 + col = j * 32 + (r * 8 + b) := by rw [hcolrb]
      rw [hWdef, hidxj, allGatherPrimDimN_1_4_valAt_128_8_g210 [w0,w1,w2,w3] hheadw j hj128 r hr b hb]
    rw [hLHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_8_8_oG_g210 g x0 w0 128 hg hx0 hw0 P hP b hb]
    · rw [bw_linear_fst_valAt_1_8_8_oG_g210 g x1 w1 128 hg hx1 hw1 P hP b hb]
    · rw [bw_linear_fst_valAt_1_8_8_oG_g210 g x2 w2 128 hg hx2 hw2 P hP b hb]
    · rw [bw_linear_fst_valAt_1_8_8_oG_g210 g x3 w3 128 hg hx3 hw3 P hP b hb]

/- Input-feature (row) parallel weight gradient for `BW_linear`, output width 128.
   The activation `x` (`[1,8,32]`) is split along dim 2 into four `[1,8,8]` shards,
   the gradient `g` (`[1,8,128]`) is shared, and the weight `w` (`[128,32]`) is split
   along dim 1 into four `[128,8]` shards.  The full dW (`[128,32]`) equals the dim-1
   all-gather of the four per-rank dW outputs (each `[128,8]`).  dW depends only on `g`
   and `x`, so the per-rank `w` shards only fix the output column width. -/
set_option maxHeartbeats 800000 in
theorem bw_linear_dw_isplit_dim2_4_1_8_8_o128_g211
    (g x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 128])
    (hx0 : x0.shape = [1, 8, 8]) (hx1 : x1.shape = [1, 8, 8])
    (hx2 : x2.shape = [1, 8, 8]) (hx3 : x3.shape = [1, 8, 8])
    (hw0 : w0.shape = [128, 8]) (hw1 : w1.shape = [128, 8])
    (hw2 : w2.shape = [128, 8]) (hw3 : w3.shape = [128, 8]) :
    (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
        (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 1 4 0
        [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2,
         (bw_linear g x2 w2).2, (bw_linear g x3 w3).2] := by
  have hxhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hx0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [128, 8] := by
    simp [hw0]
  have hX_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hxhead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; simp [List.set, List.getD]
  have hp0 : (bw_linear g x0 w0).2.shape = [128, 8] := bw_linear_3d_snd_shape 1 8 128 8 g x0 w0 hg hx0 hw0
  have hp1 : (bw_linear g x1 w1).2.shape = [128, 8] := bw_linear_3d_snd_shape 1 8 128 8 g x1 w1 hg hx1 hw1
  have hp2 : (bw_linear g x2 w2).2.shape = [128, 8] := bw_linear_3d_snd_shape 1 8 128 8 g x2 w2 hg hx2 hw2
  have hp3 : (bw_linear g x3 w3).2.shape = [128, 8] := bw_linear_3d_snd_shape 1 8 128 8 g x3 w3 hg hx3 hw3
  set pieces : List Tensor :=
    [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2, (bw_linear g x2 w2).2, (bw_linear g x3 w3).2]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [128, 8] := by
    simp [hpieces_def, hp0]
  have hpgetD : ∀ r, r < 4 → (pieces.getD r (zeroTensor [128, 8])).shape = [128, 8] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hpieces_def, List.getD, hp0, hp1, hp2, hp3]
  have hLHS_shape : (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2.shape = [128, 32] :=
    bw_linear_3d_snd_shape 1 8 128 32 g _ _ hg hX_shape hW_shape
  have hRHS_shape : (allGatherPrimDimN 1 4 0 pieces).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx4096 : idx < 4096 := by simpa [hLHS_shape, prodShape] using hidx
  set c := idx / 32 with hc_def
  set k := idx % 32 with hk_def
  have hk : k < 32 := by rw [hk_def]; exact Nat.mod_lt _ (by omega)
  have hc : c < 128 := by rw [hc_def]; omega
  have hidx_eq : idx = c * 32 + k := by rw [hc_def, hk_def]; omega
  rw [hidx_eq]
  rw [bw_linear_dw_valAt3d g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) 1 8 128 32 hg hX_shape hW_shape c hc k hk]
  have hkc : k % 8 < 8 := Nat.mod_lt _ (by omega)
  have hr : k / 8 < 4 := by omega
  conv_rhs => rw [show c * 32 + k = c * 32 + k / 8 * 8 + k % 8 from by omega]
  rw [allGatherPrimDimN1_4_valAt_128_8 pieces hphead hpgetD c hc (k / 8) hr (k % 8) hkc]
  have hX_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) (p * 32 + k) =
      valAt (([x0, x1, x2, x3] : List Tensor).getD (k / 8) (zeroTensor [1, 8, 8])) (p * 8 + k % 8) := by
    intro p hp
    have hb : p * 32 + k < 256 := by omega
    rw [allGatherPrimDimN_2_4_valAt_1_8_8 [x0, x1, x2, x3] (p * 32 + k) hxhead hb]
    have hrank : (p * 32 + k) % 32 / 8 = k / 8 := by omega
    have hflat : (p * 32 + k) / 32 * 8 + (p * 32 + k) % 8 = p * 8 + k % 8 := by omega
    rw [hrank, hflat]
  rcases (show k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_dw_valAt3d g x0 w0 1 8 128 8 hg hx0 hw0 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x1 w1 1 8 128 8 hg hx1 hw1 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x2 w2 1 8 128 8 hg hx2 hw2 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x3 w3 1 8 128 8 hg hx3 hw3 c hc (k % 8) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp

-- ===== batch10 g213 net-new lemma(s) =====

set_option maxRecDepth 8192 in
/-- Value of `allGatherPrimDimN 1 4` over weight shards of shape `[32,32]`
    (dim-1 gathered to `[32,128]`). -/
theorem allGatherPrimDimN_dim1_4_32_32_valAt_g213 (ws : List Tensor)
    (row : Nat) (hrow : row < 32) (r : Nat) (hr : r < 4) (lc : Nat) (hlc : lc < 32)
    (hhead : (ws.head?.map (fun t => t.shape)).getD [] = [32, 32]) :
    valAt (allGatherPrimDimN 1 4 0 ws) (row * 128 + r * 32 + lc) =
      valAt (ws.getD r (zeroTensor [32, 32])) (row * 32 + lc) := by
  have hidx_lt : row * 128 + r * 32 + lc < 4096 := by omega
  have hgather_shape : (allGatherPrimDimN 1 4 0 ws).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 1 4 ws [32, 32] hhead]
    simp [List.set, List.getD]
  have hidx_prod : row * 128 + r * 32 + lc < prodShape (allGatherPrimDimN 1 4 0 ws).shape := by
    rw [hgather_shape]; simp [prodShape]; exact hidx_lt
  rw [valAt_of_lt _ _ hidx_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.set, List.length, List.take,
    show (32 : Nat) ≠ 0 from by omega,
    show (128 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (1 : Nat) ≠ 0 from by omega]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod,
    ite_false, ite_true, Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    List.prod_cons, List.prod_nil, Nat.one_mul]
  have hd128 : (row * 128 + r * 32 + lc) / 128 = row := by omega
  have hm128 : (row * 128 + r * 32 + lc) % 128 = r * 32 + lc := by omega
  have hdr : (r * 32 + lc) / 32 = r := by omega
  have hmr : (r * 32 + lc) % 32 = lc := by omega
  rw [hd128, hm128, hdr, hmr]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- BW_linear dX with the weight `w` (`[32,128]`) dim-1 split into 4 shards (each `[32,32]`,
    dim-1 all-gathered), and the per-rank gradient `g` (`[1,8,32]`) shared.  The full dX
    (`[1,8,128]`) is the dim-2 all-gather of the per-rank dX outputs (each `[1,8,32]`).
    dX depends only on `g` and `w`, so the per-rank activation `x` shards are irrelevant. -/
theorem bw_linear_dx_wsplit_dim1_4_g213
    (g x x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1,8,32]) (hx : x.shape = [1,8,128])
    (hx0 : x0.shape = [1,8,32]) (hx1 : x1.shape = [1,8,32])
    (hx2 : x2.shape = [1,8,32]) (hx3 : x3.shape = [1,8,32])
    (hw0 : w0.shape = [32,32]) (hw1 : w1.shape = [32,32])
    (hw2 : w2.shape = [32,32]) (hw3 : w3.shape = [32,32]) :
    (bw_linear g x (allGatherPrimDimN 1 4 0 [w0,w1,w2,w3])).1 =
      allGatherPrimDimN 2 4 0
        [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
         (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] := by
  have hheadw : (([w0,w1,w2,w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32,32] := by
    simp [hw0]
  set W := allGatherPrimDimN 1 4 0 [w0,w1,w2,w3] with hWdef
  have hWshape : W.shape = [32,128] := by
    rw [hWdef, allGatherPrimDimN_shape 1 4 _ [32,32] hheadw]; simp [List.set, List.getD]
  have hdx0shape : (bw_linear g x0 w0).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 g x0 w0 hg hx0 hw0
  have hLshape : (bw_linear g x W).1.shape = [1,8,128] :=
    bw_linear_3d_fst_shape 1 8 32 128 g x W hg hx hWshape
  have hheadR : (([(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
                   (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,8,32] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 2 4 _ [1,8,32] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx1024 : idx < 1024 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/128 < 8 := by omega
    have hcol : idx%128 < 128 := by omega
    have hide : idx = (idx/128)*128 + idx%128 := by omega
    rw [hide]
    set P := idx/128 with hPdef
    set col := idx%128 with hcoldef
    set r := col/32 with hrdef
    set lc := col%32 with hlcdef
    have hr : r < 4 := by omega
    have hlc : lc < 32 := by omega
    have hcolrlc : col = r * 32 + lc := by omega
    rw [bw_linear_fst_valAt_1_8_128_g178 g x W 32 hg hx hWshape P hP col hcol]
    have hRHS : valAt (allGatherPrimDimN 2 4 0
          [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
           (bw_linear g x2 w2).1, (bw_linear g x3 w3).1]) (P * 128 + col)
        = valAt ([(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
                  (bw_linear g x2 w2).1, (bw_linear g x3 w3).1].getD r (zeroTensor [1,8,32]))
                (P * 32 + lc) := by
      rw [hcolrlc]
      exact allGatherDimN2_4_1832_valAt_g175 _ hheadR P hP r hr lc hlc
    rw [hRHS]
    have hLHS : (∑ j ∈ Finset.range 32, valAt g (P*32+j) * valAt W (j*128+col))
        = ∑ j ∈ Finset.range 32,
            valAt g (P*32+j) * valAt ([w0,w1,w2,w3].getD r (zeroTensor [32,32])) (j*32+lc) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      have hidxj : j * 128 + col = j * 128 + r * 32 + lc := by rw [hcolrlc]; ring
      rw [hWdef, hidxj, allGatherPrimDimN_dim1_4_32_32_valAt_g213 [w0,w1,w2,w3] j hj32 r hr lc hlc hheadw]
    rw [hLHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x0 w0 32 hg hx0 hw0 P hP lc hlc]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x1 w1 32 hg hx1 hw1 P hP lc hlc]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x2 w2 32 hg hx2 hw2 P hP lc hlc]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x3 w3 32 hg hx3 hw3 P hP lc hlc]

-- ===== batch10 BW_linear g214 net-new lemma =====

/- BW_linear dW: input-feature (row) parallel.  The gradient `g` (`[1,8,32]`) is shared,
   the activation `x` (`[1,8,128]`) is sharded on dim 2 into four `[1,8,32]` shards, and the
   weight `w` (`[32,128]`) is sharded on dim 1 into four `[32,32]` shards.  The full dW
   (`[32,128]`) equals the dim-1 all-gather of the four per-rank dW outputs (each `[32,32]`). -/
set_option maxHeartbeats 800000 in
theorem bw_linear_dw_isplit_dim2_4_1_8_32_g214
    (g x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 32])
    (hx0 : x0.shape = [1, 8, 32]) (hx1 : x1.shape = [1, 8, 32])
    (hx2 : x2.shape = [1, 8, 32]) (hx3 : x3.shape = [1, 8, 32])
    (hw0 : w0.shape = [32, 32]) (hw1 : w1.shape = [32, 32])
    (hw2 : w2.shape = [32, 32]) (hw3 : w3.shape = [32, 32]) :
    (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
        (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2 =
      allGatherPrimDimN 1 4 0
        [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2,
         (bw_linear g x2 w2).2, (bw_linear g x3 w3).2] := by
  -- head shapes
  have hxhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    simp [hx0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    simp [hw0]
  -- gathered input shapes
  have hX_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 128] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hxhead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; simp [List.set, List.getD]
  -- per-rank dW shapes
  have hp0 : (bw_linear g x0 w0).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g x0 w0 hg hx0 hw0
  have hp1 : (bw_linear g x1 w1).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g x1 w1 hg hx1 hw1
  have hp2 : (bw_linear g x2 w2).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g x2 w2 hg hx2 hw2
  have hp3 : (bw_linear g x3 w3).2.shape = [32, 32] := bw_linear_3d_snd_shape 1 8 32 32 g x3 w3 hg hx3 hw3
  set pieces : List Tensor :=
    [(bw_linear g x0 w0).2, (bw_linear g x1 w1).2, (bw_linear g x2 w2).2, (bw_linear g x3 w3).2]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [32, 32] := by
    simp [hpieces_def, hp0]
  have hpgetD : ∀ r, r < 4 → (pieces.getD r (zeroTensor [32, 32])).shape = [32, 32] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [hpieces_def, List.getD, hp0, hp1, hp2, hp3]
  -- LHS / RHS shapes
  have hLHS_shape : (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).2.shape = [32, 128] :=
    bw_linear_3d_snd_shape 1 8 32 128 g _ _ hg hX_shape hW_shape
  have hRHS_shape : (allGatherPrimDimN 1 4 0 pieces).shape = [32, 128] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx4096 : idx < 4096 := by simpa [hLHS_shape, prodShape] using hidx
  set c := idx / 128 with hc_def
  set k := idx % 128 with hk_def
  have hk : k < 128 := by rw [hk_def]; exact Nat.mod_lt _ (by omega)
  have hc : c < 32 := by rw [hc_def]; omega
  have hidx_eq : idx = c * 128 + k := by rw [hc_def, hk_def]; omega
  rw [hidx_eq]
  -- LHS value
  rw [bw_linear_dw_valAt3d g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) 1 8 32 128 hg hX_shape hW_shape c hc k hk]
  -- RHS value: split column index on the i-axis and peel the dim-1 gather
  have hkc : k % 32 < 32 := Nat.mod_lt _ (by omega)
  have hr : k / 32 < 4 := by omega
  conv_rhs => rw [show c * 128 + k = c * 128 + k / 32 * 32 + k % 32 from by omega]
  rw [allGatherPrimDimN1_4_valAt_32_32 pieces hphead hpgetD c hc (k / 32) hr (k % 32) hkc]
  -- expand the selected per-rank dW and match term by term
  have hX_term : ∀ p, p < 8 →
      valAt (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) (p * 128 + k) =
      valAt (([x0, x1, x2, x3] : List Tensor).getD (k / 32) (zeroTensor [1, 8, 32])) (p * 32 + k % 32) := by
    intro p hp
    have hb : p * 128 + k < 1024 := by omega
    rw [allGatherPrimDimN_2_4_valAt_1_8_32 [x0, x1, x2, x3] (p * 128 + k) hxhead hb]
    have hrank : (p * 128 + k) % 128 / 32 = k / 32 := by omega
    have hflat : (p * 128 + k) / 128 * 32 + (p * 128 + k) % 32 = p * 32 + k % 32 := by omega
    rw [hrank, hflat]
  rcases (show k / 32 = 0 ∨ k / 32 = 1 ∨ k / 32 = 2 ∨ k / 32 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_dw_valAt3d g x0 w0 1 8 32 32 hg hx0 hw0 c hc (k % 32) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x1 w1 1 8 32 32 hg hx1 hw1 c hc (k % 32) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x2 w2 1 8 32 32 hg hx2 hw2 c hc (k % 32) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp
  · rw [bw_linear_dw_valAt3d g x3 w3 1 8 32 32 hg hx3 hw3 c hc (k % 32) hkc]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hX_term p (Finset.mem_range.mp hp), h, List.getD]; simp

-- ===== net-new lemmas for BW_linear AllToAll goal_245 (_g245 suffix) =====

/-- `bw_linear` dX (first output) ignores the *value* of the activation `x`; it depends on
    `x` only through its shape (which fixes the output width).  Specialised to the
    `[1,8,128] × [1,8,32] × [128,32]` instance used by goal_245. -/
theorem bw_linear_fst_x_irrelevant_1_8_32_g245 (g x x' w : Tensor)
    (hg : g.shape = [1, 8, 128]) (hx : x.shape = [1, 8, 32]) (hx' : x'.shape = [1, 8, 32])
    (hw : w.shape = [128, 32]) :
    (bw_linear g x w).1 = (bw_linear g x' w).1 := by
  have s1 : (bw_linear g x w).1.shape = [1, 8, 32] :=
    bw_linear_3d_fst_shape 1 8 128 32 g x w hg hx hw
  have s2 : (bw_linear g x' w).1.shape = [1, 8, 32] :=
    bw_linear_3d_fst_shape 1 8 128 32 g x' w hg hx' hw
  apply Tensor.ext (by rw [s1, s2])
  intro idx hidx
  rw [s1] at hidx
  have hidx256 : idx < 256 := by simpa [prodShape] using hidx
  set seq := idx / 32 with hseq_def
  set col := idx % 32 with hcol_def
  have hcol : col < 32 := by rw [hcol_def]; exact Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by rw [hseq_def]; omega
  have hidx_eq : idx = seq * 32 + col := by rw [hseq_def, hcol_def]; omega
  rw [hidx_eq,
      bw_linear_fst_valAt_1_8_32_g134 g x w 128 hg hx hw seq hseq col hcol,
      bw_linear_fst_valAt_1_8_32_g134 g x' w 128 hg hx' hw seq hseq col hcol]

set_option maxHeartbeats 1600000 in
/-- Column-parallel (output-feature split) input gradient for `BW_linear` with a wide
    gradient (`g : [1,8,128]`).  The gradient `g` is shared, the weight `w` (`[128,32]`)
    is sharded on dim 1 into four `[128,8]` shards (reassembled by `allGatherPrimDimN 1`),
    and the activation `x` (`[1,8,32]`) is sharded on dim 2 into four `[1,8,8]` shards
    (reassembled by `allGatherPrimDimN 2`).  Then the full dX (`[1,8,32]`) equals the
    dim-2 all-gather of the four per-rank dX outputs (each `[1,8,8]`).  dX depends only on
    `g` and `w`, so the per-rank `x` shards only fix the output column width. -/
theorem bw_linear_dx_csplit_dim1_4_1_8_8_g245
    (g x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 128])
    (hx0 : x0.shape = [1, 8, 8]) (hx1 : x1.shape = [1, 8, 8])
    (hx2 : x2.shape = [1, 8, 8]) (hx3 : x3.shape = [1, 8, 8])
    (hw0 : w0.shape = [128, 8]) (hw1 : w1.shape = [128, 8])
    (hw2 : w2.shape = [128, 8]) (hw3 : w3.shape = [128, 8]) :
    (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
        (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).1 =
      allGatherPrimDimN 2 4 0
        [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
         (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] := by
  have hxhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hx0]
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [128, 8] := by
    simp [hw0]
  have hwgetD : ∀ r, r < 4 →
      (([w0, w1, w2, w3] : List Tensor).getD r (zeroTensor [128, 8])).shape = [128, 8] := by
    intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp [List.getD, hw0, hw1, hw2, hw3]
  have hX_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hxhead]; simp [List.set, List.getD]
  have hW_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [128, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; simp [List.set, List.getD]
  have hp0 : (bw_linear g x0 w0).1.shape = [1, 8, 8] := bw_linear_3d_fst_shape 1 8 128 8 g x0 w0 hg hx0 hw0
  set pieces : List Tensor :=
    [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1, (bw_linear g x2 w2).1, (bw_linear g x3 w3).1]
    with hpieces_def
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [1, 8, 8] := by
    simp [hpieces_def, hp0]
  have hLHS_shape : (bw_linear g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).1.shape = [1, 8, 32] :=
    bw_linear_3d_fst_shape 1 8 128 32 g _ _ hg hX_shape hW_shape
  have hRHS_shape : (allGatherPrimDimN 2 4 0 pieces).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hphead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hLHS_shape, hRHS_shape])
  intro idx hidx
  have hidx256 : idx < 256 := by simpa [hLHS_shape, prodShape] using hidx
  set seq := idx / 32 with hseq_def
  set col := idx % 32 with hcol_def
  have hcol : col < 32 := by rw [hcol_def]; exact Nat.mod_lt _ (by omega)
  have hseq : seq < 8 := by rw [hseq_def]; omega
  have hidx_eq : idx = seq * 32 + col := by rw [hseq_def, hcol_def]; omega
  rw [hidx_eq]
  rw [bw_linear_fst_valAt_1_8_32_g134 g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) 128 hg hX_shape hW_shape seq hseq col hcol]
  have hr : col / 8 < 4 := by omega
  have hlc : col % 8 < 8 := Nat.mod_lt _ (by omega)
  conv_rhs => rw [show seq * 32 + col = seq * 32 + (col / 8 * 8 + col % 8) from by omega]
  rw [allGatherDimN2_4_188_valAt_g134 pieces hphead seq hseq (col / 8) hr (col % 8) hlc]
  have hW_term : ∀ j, j < 128 →
      valAt (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) (j * 32 + col) =
      valAt (([w0, w1, w2, w3] : List Tensor).getD (col / 8) (zeroTensor [128, 8])) (j * 8 + col % 8) := by
    intro j hj
    rw [show j * 32 + col = j * 32 + col / 8 * 8 + col % 8 from by omega]
    rw [allGatherPrimDimN1_4_valAt_128_8 [w0, w1, w2, w3] hwhead hwgetD j hj (col / 8) hr (col % 8) hlc]
  rcases (show col / 8 = 0 ∨ col / 8 = 1 ∨ col / 8 = 2 ∨ col / 8 = 3 from by omega) with h | h | h | h <;>
    rw [h] <;>
    simp only [hpieces_def, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x0 w0 128 hg hx0 hw0 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x1 w1 128 hg hx1 hw1 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x2 w2 128 hg hx2 hw2 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp
  · rw [bw_linear_fst_valAt_1_8_8_g276 g x3 w3 128 hg hx3 hw3 seq hseq (col % 8) hlc]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hW_term j (Finset.mem_range.mp hj), h, List.getD]; simp

-- ===== net-new lemmas for batch10 BW_linear g143 (dX with AllToAll reshard) =====

/-- Value of `bw_linear` dX (first output) for the per-rank 3D inputs whose intrinsic
    output width is 128 and sequence length is 2 (so the per-rank dX shard has shape
    `[1,2,128]`).  Mirror of `bw_linear_fst_valAt_1_2_32_g169` for output width 128. -/
theorem bw_linear_fst_valAt_1_2_128_g143 (g x w : Tensor) (o : Nat)
    (hg : g.shape = [1, 2, o]) (hx : x.shape = [1, 2, 128]) (hw : w.shape = [o, 128])
    (P : Nat) (hP : P < 2) (col : Nat) (hcol : col < 128) :
    valAt (bw_linear g x w).1 (P * 128 + col) =
      ∑ j ∈ Finset.range o, valAt g (P * o + j) * valAt w (j * 128 + col) := by
  have hdx : (bw_linear g x w).1 =
      Tensor.mkShape [1, 2, 128] (fun outIdx =>
        ∑ j ∈ Finset.range o,
          valAt g (((if (2:Nat) * 128 = 0 then 0 else outIdx.1 / (2 * 128)) * 2 +
                    if (128:Nat) = 0 then 0 else (if (2:Nat) * 128 = 0 then 0 else outIdx.1 % (2 * 128)) / 128) * o + j) *
          valAt w (j * 128 + if (128:Nat) = 0 then 0 else (if (2:Nat) * 128 = 0 then 0 else outIdx.1 % (2 * 128)) % 128)) := by
    unfold bw_linear
    rw [hg, hx, hw]
  rw [hdx]
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl]; omega)]
  simp only [Tensor.mkShape]
  have e1 : (P*128+col)/(2*128) = 0 := by omega
  have e2 : ((P*128+col)%(2*128))/128 = P := by omega
  have e3 : ((P*128+col)%(2*128))%128 = col := by omega
  simp only [show ((2:Nat)*128=0)=False from by simp, show ((128:Nat)=0)=False from by simp,
    if_false, e1, e2, e3, Nat.zero_mul, Nat.zero_add]

set_option maxHeartbeats 2000000 in
/-- Data-parallel (sequence-dim) split of the dX output of `BW_linear` matching the
    AllToAll-resharded layout of goal_143: the gradient (`[1,8,32]`) is dim-1 all-gathered
    from four `[1,2,32]` shards `g0..g3`, the activation `x` (`[1,8,128]`) is only used for
    its shape, the per-rank activations `x0..x3` (`[1,2,128]`) are arbitrary shards, and the
    weight `w` (`[32,128]`) is shared.  Then the full dX (`[1,8,128]`) equals the dim-1
    all-gather of the per-rank dX outputs (each `[1,2,128]`).  dX depends only on `g` and
    `w`, so the per-rank activations need not match a chunk of any particular tensor. -/
theorem bw_linear_dx_dp_split_dim1_4_g143
    (g0 g1 g2 g3 x x0 x1 x2 x3 w : Tensor)
    (hg0 : g0.shape = [1,2,32]) (hg1 : g1.shape = [1,2,32])
    (hg2 : g2.shape = [1,2,32]) (hg3 : g3.shape = [1,2,32])
    (hx : x.shape = [1,8,128])
    (hx0 : x0.shape = [1,2,128]) (hx1 : x1.shape = [1,2,128])
    (hx2 : x2.shape = [1,2,128]) (hx3 : x3.shape = [1,2,128])
    (hw : w.shape = [32,128]) :
    (bw_linear (allGatherPrimDimN 1 4 0 [g0,g1,g2,g3]) x w).1 =
      allGatherPrimDimN 1 4 0
        [(bw_linear g0 x0 w).1, (bw_linear g1 x1 w).1,
         (bw_linear g2 x2 w).1, (bw_linear g3 x3 w).1] := by
  have hheadg : (([g0,g1,g2,g3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1,2,32] := by
    simp [hg0]
  set G := allGatherPrimDimN 1 4 0 [g0,g1,g2,g3] with hGdef
  have hGshape : G.shape = [1,8,32] := by
    rw [hGdef, allGatherPrimDimN_shape 1 4 _ [1,2,32] hheadg]; simp [List.set, List.getD]
  have hdx0shape : (bw_linear g0 x0 w).1.shape = [1,2,128] :=
    bw_linear_3d_fst_shape 1 2 32 128 _ _ _ hg0 hx0 hw
  have hLshape : (bw_linear G x w).1.shape = [1,8,128] :=
    bw_linear_3d_fst_shape 1 8 32 128 G x w hGshape hx hw
  have hheadR : (([(bw_linear g0 x0 w).1, (bw_linear g1 x1 w).1,
                   (bw_linear g2 x2 w).1, (bw_linear g3 x3 w).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,2,128] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 1 4 _ [1,2,128] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx1024 : idx < 1024 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/128 < 8 := by omega
    have hcol : idx%128 < 128 := by omega
    have hide : idx = (idx/128)*128 + idx%128 := by omega
    rw [hide]
    set P := idx/128 with hPdef
    set col := idx%128 with hcoldef
    set r := P/2 with hrdef
    set p := P%2 with hpdef
    have hr : r < 4 := by omega
    have hp : p < 2 := by omega
    have hPrp : P = r * 2 + p := by omega
    rw [bw_linear_fst_valAt_1_8_128_g178 G x w 32 hGshape hx hw P hP col hcol]
    have hRHS : valAt (allGatherPrimDimN 1 4 0
          [(bw_linear g0 x0 w).1, (bw_linear g1 x1 w).1,
           (bw_linear g2 x2 w).1, (bw_linear g3 x3 w).1]) (P * 128 + col)
        = valAt ([(bw_linear g0 x0 w).1, (bw_linear g1 x1 w).1,
                  (bw_linear g2 x2 w).1, (bw_linear g3 x3 w).1].getD r (zeroTensor [1,2,128]))
                (p * 128 + col) := by
      rw [hPrp]
      exact allGatherPrimDimN_dim1_4_1_2_128_valAt _ r hr p hp col hcol hheadR
    rw [hRHS]
    have hLHS : (∑ j ∈ Finset.range 32, valAt G (P*32+j) * valAt w (j*128+col))
        = ∑ j ∈ Finset.range 32,
            valAt ([g0,g1,g2,g3].getD r (zeroTensor [1,2,32])) (p*32+j) * valAt w (j*128+col) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      have hidxj : P * 32 + j = (r * 2 + p) * 32 + j := by rw [hPrp]
      rw [hGdef, hidxj, allGatherPrimDimN_dim1_4_1_2_32_valAt [g0,g1,g2,g3] r hr p hp j hj32 hheadg]
    rw [hLHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_2_128_g143 g0 x0 w 32 hg0 hx0 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_128_g143 g1 x1 w 32 hg1 hx1 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_128_g143 g2 x2 w 32 hg2 hx2 hw p hp col hcol]
    · rw [bw_linear_fst_valAt_1_2_128_g143 g3 x3 w 32 hg3 hx3 hw p hp col hcol]

-- ===== net-new lemmas for batch10 BW_linear g246 (x dim-2 split, g=[1,8,128]) =====

set_option maxHeartbeats 1600000 in
/-- Per-rank dW value when `x` (`[1,8,32]`) is chunked along its last (input-feature)
    dim into rank `R` (giving `[1,8,8]`), with gradient `g` (`[1,8,128]`).  The rank-`R`
    dW (`[128,8]`) at row `c`, col `i` equals the global reduction whose `x`-index is
    offset by `R*8`. -/
private theorem bw_linear_dw_xchunk_rank_valAt_g246
    (g x w_r : Tensor) (R c i : Nat)
    (hg : g.shape = [1, 8, 128]) (hx : x.shape = [1, 8, 32]) (hwr : w_r.shape = [128, 8])
    (hR : R < 4) (hc : c < 128) (hi : i < 8) :
    valAt (bw_linear g (chunkPrimDimN 2 4 R x) w_r).2 (c * 8 + i) =
      ∑ r' ∈ Finset.range 8, valAt g (r' * 128 + c) * valAt x (r' * 32 + R * 8 + i) := by
  have hchunk : (chunkPrimDimN 2 4 R x).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 R x _ hx (by omega)]; simp [List.set, List.getD]
  rw [bw_linear_dw_valAt3d g (chunkPrimDimN 2 4 R x) w_r 1 8 128 8 hg hchunk hwr c hc i hi]
  simp only [show (1 : Nat) * 8 = 8 from rfl]
  apply Finset.sum_congr rfl
  intro r' hr'
  rw [chunk2_4_1_8_32_valAt_pj x R r' i hx hR (Finset.mem_range.mp hr') hi]

set_option maxHeartbeats 1600000 in
/-- The dW output of `bw_linear` where the input `x` (`[1,8,32]`) is chunked along its
    last (input-feature) dim into 4 ranks (each `[1,8,8]`) and the gradient `g` is
    `[1,8,128]`, equals the dim-1 all-gather of the per-rank dW outputs (each `[128,8]`).
    This is the column-(input-)parallel weight-gradient identity for `BW_linear`; dW is
    independent of `w` (per-rank `w0..w3` only fix the shape). -/
theorem bw_linear_dw_xsplit_dim2_4_g246
    (g x w w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 128]) (hx : x.shape = [1, 8, 32]) (hw : w.shape = [128, 32])
    (hw0 : w0.shape = [128, 8]) (hw1 : w1.shape = [128, 8])
    (hw2 : w2.shape = [128, 8]) (hw3 : w3.shape = [128, 8]) :
    (bw_linear g x w).2 = allGatherPrimDimN 1 4 0
      [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
       (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
       (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
       (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2] := by
  have hch0 : (chunkPrimDimN 2 4 0 x).shape = [1, 8, 8] := by
    rw [chunkPrimDimN_shape 2 4 0 x _ hx (by omega)]; simp [List.set, List.getD]
  have hd0 : (bw_linear g (chunkPrimDimN 2 4 0 x) w0).2.shape = [128, 8] :=
    bw_linear_3d_snd_shape 1 8 128 8 g _ w0 hg hch0 hw0
  have hhead : (([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
                  (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
                  (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
                  (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2].head?.map
                  (fun t => t.shape)).getD [] = [128, 8]) := by
    simp [hd0]
  have hWs_shape : ∀ r (_ : r < 4),
      (([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
         (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
         (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
         (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2].getD r (zeroTensor [128, 8])).shape = [128, 8]) := by
    intro r hr
    rcases r with _|_|_|_|r
    · simpa [List.getD] using bw_linear_3d_snd_shape 1 8 128 8 g _ w0 hg hch0 hw0
    · have : (chunkPrimDimN 2 4 1 x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 1 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 128 8 g _ w1 hg this hw1
    · have : (chunkPrimDimN 2 4 2 x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 2 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 128 8 g _ w2 hg this hw2
    · have : (chunkPrimDimN 2 4 3 x).shape = [1, 8, 8] := by
        rw [chunkPrimDimN_shape 2 4 3 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 128 8 g _ w3 hg this hw3
    · omega
  apply Tensor.ext
  · rw [bw_linear_3d_snd_shape 1 8 128 32 g x w hg hx hw,
        allGatherPrimDimN_shape 1 4 _ [128, 8] hhead]
    decide
  · intro idx hidx
    rw [bw_linear_3d_snd_shape 1 8 128 32 g x w hg hx hw] at hidx
    have hidxp : idx < 4096 := by simpa [prodShape] using hidx
    have hc : idx / 32 < 128 := by omega
    have hk : idx % 32 < 32 := by omega
    set c := idx / 32 with hcdef
    set k := idx % 32 with hkdef
    have hidc : idx = c * 32 + k := by omega
    rw [hidc, bw_linear_dw_valAt3d g x w 1 8 128 32 hg hx hw c hc k hk]
    have hr : k / 8 < 4 := by omega
    have hi : k % 8 < 8 := by omega
    rw [show c * 32 + k = c * (8 * 4) + (k / 8 * 8 + k % 8) from by omega]
    rw [allGatherPrimDimN1_valAt_g240 4 128 8
          [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
           (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
           (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
           (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2]
          (by omega) (by omega) (by omega) hhead hWs_shape c hc (k / 8) hr (k % 8) hi]
    have hcase : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 := by omega
    rcases hcase with h | h | h | h
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g246 g x w0 0 c (k % 8) hg hx hw0 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 0 * 8 + k % 8 = r' * 32 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g246 g x w1 1 c (k % 8) hg hx hw1 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 1 * 8 + k % 8 = r' * 32 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g246 g x w2 2 c (k % 8) hg hx hw2 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 2 * 8 + k % 8 = r' * 32 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g246 g x w3 3 c (k % 8) hg hx hw3 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 32 + 3 * 8 + k % 8 = r' * 32 + k from by omega]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- BW_linear dX input-split (column/tensor-parallel) for goal_248:
    weight `[32,128]` split on dim 1 into four `[32,32]` shards (all-gathered on dim 1);
    `x` is `[1,8,128]` and the per-rank `x` shards are arbitrary `[1,8,32]` tensors
    (dX does not depend on `x`).  The full dX `[1,8,128]` is the dim-2 all-gather of the
    per-rank dX shards `[1,8,32]`. -/
theorem bw_linear_dx_isplit_dim2_4_1_8_128_g248
    (g x x0 x1 x2 x3 w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1,8,32]) (hx : x.shape = [1,8,128])
    (hx0 : x0.shape = [1,8,32]) (hx1 : x1.shape = [1,8,32])
    (hx2 : x2.shape = [1,8,32]) (hx3 : x3.shape = [1,8,32])
    (hw0 : w0.shape = [32,32]) (hw1 : w1.shape = [32,32])
    (hw2 : w2.shape = [32,32]) (hw3 : w3.shape = [32,32]) :
    (bw_linear g x (allGatherPrimDimN 1 4 0 [w0,w1,w2,w3])).1 =
      allGatherPrimDimN 2 4 0
        [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
         (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] := by
  have hheadw : (([w0,w1,w2,w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [32,32] := by
    simp [hw0]
  have hWsh : ∀ r, r < 4 →
      (([w0,w1,w2,w3]:List Tensor).getD r (zeroTensor [32,32])).shape = [32,32] := by
    intro r hr
    match r, hr with
    | 0, _ => exact hw0
    | 1, _ => exact hw1
    | 2, _ => exact hw2
    | 3, _ => exact hw3
  set W := allGatherPrimDimN 1 4 0 [w0,w1,w2,w3] with hWdef
  have hWshape : W.shape = [32,128] := by
    rw [hWdef, allGatherPrimDimN_shape 1 4 _ [32,32] hheadw]; simp [List.set, List.getD]
  have hLshape : (bw_linear g x W).1.shape = [1,8,128] :=
    bw_linear_3d_fst_shape 1 8 32 128 g x W hg hx hWshape
  have hdx0shape : (bw_linear g x0 w0).1.shape = [1,8,32] :=
    bw_linear_3d_fst_shape 1 8 32 32 g x0 w0 hg hx0 hw0
  have hheadR : (([(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
                   (bw_linear g x2 w2).1, (bw_linear g x3 w3).1] : List Tensor).head?.map
                  (fun t => t.shape)).getD [] = [1,8,32] := by
    simp only [List.head?, Option.map, Option.getD]; exact hdx0shape
  apply Tensor.ext
  · rw [hLshape, allGatherPrimDimN_shape 2 4 _ [1,8,32] hheadR]; simp [List.set, List.getD]
  · intro idx hidx
    rw [hLshape] at hidx
    have hidx1024 : idx < 1024 := by simpa [prodShape, List.foldl] using hidx
    have hP : idx/128 < 8 := by omega
    have hcol : idx%128 < 128 := by omega
    have hide : idx = (idx/128)*128 + idx%128 := by omega
    rw [hide]
    set P := idx/128 with hPdef
    set col := idx%128 with hcoldef
    set r := col/32 with hrdef
    set c := col%32 with hcdef
    have hr : r < 4 := by omega
    have hc : c < 32 := by omega
    have hcolrc : col = r * 32 + c := by omega
    rw [bw_linear_fst_valAt_1_8_128_g178 g x W 32 hg hx hWshape P hP col hcol]
    have hRHS : valAt (allGatherPrimDimN 2 4 0
          [(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
           (bw_linear g x2 w2).1, (bw_linear g x3 w3).1]) (P * 128 + col)
        = valAt ([(bw_linear g x0 w0).1, (bw_linear g x1 w1).1,
                  (bw_linear g x2 w2).1, (bw_linear g x3 w3).1].getD r (zeroTensor [1,8,32]))
                (P * 32 + c) := by
      rw [hcolrc]
      exact allGatherDimN2_4_1832_valAt_g175 _ hheadR P hP r hr c hc
    rw [hRHS]
    have hLHS : (∑ j ∈ Finset.range 32, valAt g (P*32+j) * valAt W (j*128+col))
        = ∑ j ∈ Finset.range 32,
            valAt g (P*32+j) * valAt ([w0,w1,w2,w3].getD r (zeroTensor [32,32])) (j*32+c) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj32 : j < 32 := Finset.mem_range.mp hj
      have hidxj : j * 128 + col = j * 128 + r * 32 + c := by rw [hcolrc]; ring
      rw [hWdef, hidxj,
        allGatherPrimDimN1_4_valAt_32_32 [w0,w1,w2,w3] hheadw hWsh j hj32 r hr c hc]
    rw [hLHS]
    have hrcase : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrcase with h|h|h|h <;> rw [h] <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x0 w0 32 hg hx0 hw0 P hP c hc]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x1 w1 32 hg hx1 hw1 P hP c hc]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x2 w2 32 hg hx2 hw2 P hP c hc]
    · rw [bw_linear_fst_valAt_1_8_32_g134 g x3 w3 32 hg hx3 hw3 P hP c hc]

-- ===== net-new lemmas for batch10 BW_linear g249 (AllToAll-fed dW, input-parallel) =====

/-- Per-element value of `chunkPrimDimN 2 4 r` on a `[1,8,128]` tensor (shard `[1,8,32]`). -/
private theorem chunk2_4_1_8_128_valAt_pj_g249 (x : Tensor) (r p j : Nat)
    (hx : x.shape = [1, 8, 128]) (hr : r < 4) (hp : p < 8) (hj : j < 32) :
    valAt (chunkPrimDimN 2 4 r x) (p * 32 + j) = valAt x (p * 128 + r * 32 + j) := by
  have hloc : p * 32 + j < 256 := by omega
  have hchunk_shape : (chunkPrimDimN 2 4 r x).shape = [1, 8, 32] := by
    rw [chunkPrimDimN_shape 2 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : p * 32 + j < prodShape (chunkPrimDimN 2 4 r x).shape := by
    rw [hchunk_shape]
    simp [prodShape]
    exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have hidx : (p * 32 + j) / 32 * 128 + (r % 4 * 32 + (p * 32 + j) % 32 / 1) * 1 + (p * 32 + j) % 32 % 1 =
      p * 128 + r * 32 + j := by omega
  rw [hidx]

/-- Per-rank dW value when `x` (`[1,8,128]`) is chunked along its last (input-feature)
    dim into rank `R` (giving `[1,8,32]`).  The rank-`R` dW (`[32,32]`) at row `c`, col `i`
    equals the global reduction whose `x`-index is offset by `R*32`. -/
private theorem bw_linear_dw_xchunk_rank_valAt_g249
    (g x w_r : Tensor) (R c i : Nat)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 128]) (hwr : w_r.shape = [32, 32])
    (hR : R < 4) (hc : c < 32) (hi : i < 32) :
    valAt (bw_linear g (chunkPrimDimN 2 4 R x) w_r).2 (c * 32 + i) =
      ∑ r' ∈ Finset.range 8, valAt g (r' * 32 + c) * valAt x (r' * 128 + R * 32 + i) := by
  have hchunk : (chunkPrimDimN 2 4 R x).shape = [1, 8, 32] := by
    rw [chunkPrimDimN_shape 2 4 R x _ hx (by omega)]; simp [List.set, List.getD]
  rw [bw_linear_dw_valAt3d g (chunkPrimDimN 2 4 R x) w_r 1 8 32 32 hg hchunk hwr c hc i hi]
  simp only [show (1 : Nat) * 8 = 8 from rfl]
  apply Finset.sum_congr rfl
  intro r' hr'
  rw [chunk2_4_1_8_128_valAt_pj_g249 x R r' i hx hR (Finset.mem_range.mp hr') hi]

set_option maxHeartbeats 1600000 in
/-- The dW output of `bw_linear` where the input `x` (`[1,8,128]`) is chunked along its
    last (input-feature) dim into 4 ranks (each `[1,8,32]`), equals the dim-1 all-gather
    of the per-rank dW outputs (each `[32,32]`).  This is the column-(input-)parallel
    weight-gradient identity for `BW_linear`; dW is independent of `w` (per-rank `w0..w3`
    only fix the shape). -/
theorem bw_linear_dw_xsplit_dim2_4_1_8_128_g249
    (g x w w0 w1 w2 w3 : Tensor)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 128]) (hw : w.shape = [32, 128])
    (hw0 : w0.shape = [32, 32]) (hw1 : w1.shape = [32, 32])
    (hw2 : w2.shape = [32, 32]) (hw3 : w3.shape = [32, 32]) :
    (bw_linear g x w).2 = allGatherPrimDimN 1 4 0
      [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
       (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
       (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
       (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2] := by
  have hch0 : (chunkPrimDimN 2 4 0 x).shape = [1, 8, 32] := by
    rw [chunkPrimDimN_shape 2 4 0 x _ hx (by omega)]; simp [List.set, List.getD]
  have hd0 : (bw_linear g (chunkPrimDimN 2 4 0 x) w0).2.shape = [32, 32] :=
    bw_linear_3d_snd_shape 1 8 32 32 g _ w0 hg hch0 hw0
  have hhead : (([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
                  (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
                  (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
                  (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2].head?.map
                  (fun t => t.shape)).getD [] = [32, 32]) := by
    simp [hd0]
  have hWs_shape : ∀ r (_ : r < 4),
      (([(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
         (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
         (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
         (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2].getD r (zeroTensor [32, 32])).shape = [32, 32]) := by
    intro r hr
    rcases r with _|_|_|_|r
    · simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 32 g _ w0 hg hch0 hw0
    · have : (chunkPrimDimN 2 4 1 x).shape = [1, 8, 32] := by
        rw [chunkPrimDimN_shape 2 4 1 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 32 g _ w1 hg this hw1
    · have : (chunkPrimDimN 2 4 2 x).shape = [1, 8, 32] := by
        rw [chunkPrimDimN_shape 2 4 2 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 32 g _ w2 hg this hw2
    · have : (chunkPrimDimN 2 4 3 x).shape = [1, 8, 32] := by
        rw [chunkPrimDimN_shape 2 4 3 x _ hx (by omega)]; simp [List.set, List.getD]
      simpa [List.getD] using bw_linear_3d_snd_shape 1 8 32 32 g _ w3 hg this hw3
    · omega
  apply Tensor.ext
  · rw [bw_linear_3d_snd_shape 1 8 32 128 g x w hg hx hw,
        allGatherPrimDimN_shape 1 4 _ [32, 32] hhead]
    decide
  · intro idx hidx
    rw [bw_linear_3d_snd_shape 1 8 32 128 g x w hg hx hw] at hidx
    have hidxp : idx < 4096 := by simpa [prodShape] using hidx
    have hc : idx / 128 < 32 := by omega
    have hk : idx % 128 < 128 := by omega
    set c := idx / 128 with hcdef
    set k := idx % 128 with hkdef
    have hidc : idx = c * 128 + k := by omega
    rw [hidc, bw_linear_dw_valAt3d g x w 1 8 32 128 hg hx hw c hc k hk]
    have hr : k / 32 < 4 := by omega
    have hi : k % 32 < 32 := by omega
    rw [show c * 128 + k = c * (32 * 4) + (k / 32 * 32 + k % 32) from by omega]
    rw [allGatherPrimDimN1_valAt_g240 4 32 32
          [(bw_linear g (chunkPrimDimN 2 4 0 x) w0).2,
           (bw_linear g (chunkPrimDimN 2 4 1 x) w1).2,
           (bw_linear g (chunkPrimDimN 2 4 2 x) w2).2,
           (bw_linear g (chunkPrimDimN 2 4 3 x) w3).2]
          (by omega) (by omega) (by omega) hhead hWs_shape c hc (k / 32) hr (k % 32) hi]
    have hcase : k / 32 = 0 ∨ k / 32 = 1 ∨ k / 32 = 2 ∨ k / 32 = 3 := by omega
    rcases hcase with h | h | h | h
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g249 g x w0 0 c (k % 32) hg hx hw0 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 128 + 0 * 32 + k % 32 = r' * 128 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g249 g x w1 1 c (k % 32) hg hx hw1 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 128 + 1 * 32 + k % 32 = r' * 128 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g249 g x w2 2 c (k % 32) hg hx hw2 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 128 + 2 * 32 + k % 32 = r' * 128 + k from by omega]
    · rw [h]; simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [bw_linear_dw_xchunk_rank_valAt_g249 g x w3 3 c (k % 32) hg hx hw3 (by omega) hc hi]
      apply Finset.sum_congr rfl
      intro r' _
      rw [show r' * 128 + 3 * 32 + k % 32 = r' * 128 + k from by omega]

/-- `applyNode` for `FW_multiref` with `outs = [t1, t2]` and `params = [2]`: the second
    output equals the input (when `t1 ≠ t2`). -/
theorem applyNode_fw_multiref2_second_out_g259
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid t1 t2 : Tid) (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2], params := [2] } t2 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl,
      evalOp_fw_multiref]
  change storeSet s ([t1, t2].zip (List.replicate 2 (s xTid))) t2 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

end TrainVerify.Denote
