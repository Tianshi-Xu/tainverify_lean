import Std
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace TrainVerify.Denote

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
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
theorem list_ofFn_get_eq {α : Type*} (xs : List α) :
  List.ofFn (fun i : Fin xs.length => xs.get ⟨i.1, by exact i.2⟩) = xs := by
  apply List.ext_get
  · simp [List.length_ofFn]
  · intro n hn1 hn2
    have hn : n < xs.length := by
      simpa [List.length_ofFn] using hn1
    simp [List.getElem_ofFn, List.get_eq_getElem, hn]

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
  -- Intended: x:[B,I], w:[I,O] => y:[B,O]
  match x.shape, w.shape with
  | [b, i], [o, _i2] =>
      -- We intentionally do not branch on the equality of inner dimensions here.
      -- Graph consistency is enforced separately by shape assumptions.
      Tensor.mkShape [b, o] (k_matmul b o i x w)
  | _, _ => Tensor.mkShape [] (fun _ => 0)

def bw_linear (gradOut x w : Tensor) : Tensor × Tensor :=
  match gradOut.shape, x.shape, w.shape with
  | [_bG, _oG], [bX, iX], [oW, iW] =>
      -- As with `fw_linear`, we do not branch on dimension equalities here.
      -- Under the intended shape assumptions, these dimensions match.
  let dx := Tensor.mkShape [bX, iX] (k_matmul_right_transpose bX iX oW gradOut w)
      let dw := Tensor.mkShape [oW, iW] (k_matmul_transpose bX oW iW gradOut x)
      (dx, dw)
  | _, _, _ => (Tensor.mkShape [] (fun _ => 0), Tensor.mkShape [] (fun _ => 0))

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


def allReducePrim (_numParts _rank : Nat) (xs : List Tensor) : Tensor :=
  let sh := (xs.head?.map (fun t => t.shape)).getD []
  Tensor.mkShape sh (fun idx => xs.foldl (fun acc t => acc + valAt t idx.1) 0)

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

/-!
## fw_sum commutes with allReduce (scalar tensors)

If all inputs are scalar, summing the all-reduced tensor equals
all-reducing the per-rank scalar sums.
-/

theorem fw_sum_allReduce_eq_allReduce_fw_sum
    (numParts rank : Nat) (xs : List Tensor)
    (hshape : ∀ x ∈ xs, x.shape = [1])
    (hne : xs ≠ []) :
    fw_sum (allReducePrim numParts rank xs) =
      allReducePrim numParts rank (xs.map fw_sum) := by
  -- Reduce to equality at index 0 (scalar shape).
  cases xs with
  | nil => cases (hne rfl)
  | cons x xs' =>
      have hx : x.shape = [1] := hshape x (by simp)
      have hshape_ar : (allReducePrim numParts rank (x :: xs')).shape = [1] := by
        have hhead : (x :: xs').head? = some x := rfl
        simpa [hx] using allReducePrim_shape numParts rank (x :: xs') x hhead
      have hshape_rhs : (allReducePrim numParts rank ((x :: xs').map fw_sum)).shape = [1] := by
        have hhead : ((x :: xs').map fw_sum).head? = some (fw_sum x) := rfl
        have h := allReducePrim_shape numParts rank ((x :: xs').map fw_sum) (fw_sum x) hhead
        simpa [fw_sum_shape] using h
      have hshape_fw : (fw_sum (allReducePrim numParts rank (x :: xs'))).shape = [1] :=
        fw_sum_shape _
      have hshape_eq : (fw_sum (allReducePrim numParts rank (x :: xs'))).shape =
          (allReducePrim numParts rank ((x :: xs').map fw_sum)).shape := by
        rw [hshape_fw, hshape_rhs]
      apply Tensor.ext hshape_eq
      intro idx hidx
      -- only index is 0
      have hidx0 : idx = 0 := by
        have : idx < 1 := by
          simpa [hshape_ar, prodShape_one] using hidx
        exact Nat.lt_one_iff.mp this
      subst hidx0
      -- LHS: fw_sum on allReduce
      have hpos : 0 < prodShape (allReducePrim numParts rank (x :: xs')).shape := by
        simp [hshape_ar, prodShape_one]
      have hL : valAt (fw_sum (allReducePrim numParts rank (x :: xs'))) 0 =
          valAt (allReducePrim numParts rank (x :: xs')) 0 :=
        fw_sum_valAt0_of_shape_one _ hshape_ar
      -- RHS: allReduce over fw_sum
      have hshape_rhs' : (allReducePrim numParts rank (fw_sum x :: List.map fw_sum xs')).shape = [1] := by
        simpa [List.map] using hshape_rhs
      have hpos_rhs : 0 < prodShape (allReducePrim numParts rank (fw_sum x :: List.map fw_sum xs')).shape := by
        simp [hshape_rhs', prodShape_one]
      have hR : valAt (allReducePrim numParts rank ((x :: xs').map fw_sum)) 0 =
          ((x :: xs').map fw_sum).foldl (fun acc t => acc + valAt t 0) 0 := by
        have hR' := allReducePrim_valAt0_of_pos numParts rank (fw_sum x :: List.map fw_sum xs') hpos_rhs
        simpa [List.map] using hR'
      -- Rewrite fw_sum valAt0 to valAt0 of original tensor
      have hmap : ((x :: xs').map fw_sum).foldl (fun acc t => acc + valAt t 0) 0 =
          (x :: xs').foldl (fun acc t => acc + valAt t 0) 0 := by
        -- map preserves the foldl values since each fw_sum is scalar
        have hmap_all : ∀ ys : List Tensor, (∀ y ∈ ys, y.shape = [1]) → ∀ acc : Scalar,
            (ys.map fw_sum).foldl (fun acc t => acc + valAt t 0) acc =
              ys.foldl (fun acc t => acc + valAt t 0) acc := by
          intro ys hsh acc
          induction ys generalizing acc with
          | nil =>
              simp [List.map, List.foldl]
          | cons z zs ih =>
              have hz : z.shape = [1] := hsh z (by simp)
              have hsh' : ∀ y ∈ zs, y.shape = [1] := by
                intro (y : Tensor) hy; exact hsh y (by simp [hy])
              have hval : valAt (fw_sum z) 0 = valAt z 0 :=
                fw_sum_valAt0_of_shape_one z hz
              have ih' := ih hsh' (acc + valAt z 0)
              -- unfold one step of foldl and use IH with updated accumulator
              dsimp [List.map, List.foldl]
              rw [hval]
              exact ih'
        exact hmap_all (x :: xs') hshape 0
      -- Convert LHS allReduce to foldl
      have hL' : valAt (allReducePrim numParts rank (x :: xs')) 0 =
          (x :: xs').foldl (fun acc t => acc + valAt t 0) 0 :=
        allReducePrim_valAt0_of_pos numParts rank (x :: xs') hpos
      -- Conclude
      calc
        valAt (fw_sum (allReducePrim numParts rank (x :: xs'))) 0
            = valAt (allReducePrim numParts rank (x :: xs')) 0 := hL
        _ = (x :: xs').foldl (fun acc t => acc + valAt t 0) 0 := hL'
        _ = ((x :: xs').map fw_sum).foldl (fun acc t => acc + valAt t 0) 0 := by
              symm; exact hmap
        _ = valAt (allReducePrim numParts rank ((x :: xs').map fw_sum)) 0 := by
              symm; exact hR

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

def opOutShapes (numParts : Nat) (op : String) (inShapes : List Shape) : Option (List Shape) :=
  match op, inShapes with
  | "OpName.FW_sum", [_x] =>
      some [[1]]
  | "OpName.BW_sum", [g, x] =>
      if decide (g = [1]) then some [x] else none
  | "OpName.FW_linear", [[b, i], [o, i2]] =>
      if decide (i = i2) then some [[b, o]] else none
  | "OpName.BW_linear", [[bG, oG], [bX, iX], [oW, iW]] =>
      if decide (bG = bX ∧ oG = oW ∧ iX = iW) then
        some [[bX, iX], [oW, iW]]
      else
        none
  | "OpName.ChunkPrim", [x] =>
      let pref := dropLast x
      let d := lastD x
      if decide (0 < numParts ∧ numParts ≤ d) then
        let shard := divNat d numParts
        if decide (0 < shard) then some [appendLast pref shard] else none
      else
        none
  | "OpName.AllGatherPrim", xs =>
      match xs with
      | [] => none
      | sh0 :: _ =>
          let pref := dropLast sh0
          let shard := lastD sh0
          if decide (0 < numParts) then
            if decide (xs.length = numParts) && allEqShape sh0 xs && decide (0 < shard) then
              some [appendLast pref (shard * numParts)]
            else
              none
          else
            none
  | "OpName.AllReducePrim", xs =>
      match xs with
      | [] => none
      | sh0 :: _ =>
          if allEqShape sh0 xs then some [sh0] else none
  | _, _ => none

def applyNodeShapesChecked (g : GraphDecl) (m : ShapeMap) (n : NodeDecl) : Except String ShapeMap :=
  let inShapes? : Option (List Shape) := n.ins.mapM (shapeMapGet m)
  match inShapes? with
  | none => Except.error "shape check: missing input shape"
  | some inShapes =>
      match opOutShapes g.numRanks n.op inShapes with
      | none => Except.error "shape check: op/shape mismatch"
      | some outShapes =>
          if _hLen : outShapes.length = n.outs.length then
            -- Also enforce positivity of all produced shapes (no zero dimensions).
            if outShapes.all dimsPos then
              let pairs := n.outs.zip outShapes
              let m' := pairs.foldl (fun acc p => shapeMapSet acc p.1 p.2) m
              Except.ok m'
            else
              Except.error "shape check: produced a degenerate shape"
          else
            Except.error "shape check: arity mismatch"

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
-/

def evalOp (numParts rank : Nat) (op : String) (args : List Tensor) : List Tensor :=
  match op, args with
  | "OpName.FW_sum", [x] => [fw_sum x]
  | "OpName.BW_sum", [g, x] => [bw_sum g x]
  | "OpName.FW_linear", [x, w] => [fw_linear x w]
  | "OpName.BW_linear", [g, x, w] =>
      let (dx, dw) := bw_linear g x w
      [dx, dw]
  | "OpName.ChunkPrim", [x] => [chunkPrim numParts rank x]
  | "OpName.AllGatherPrim", xs => [allGatherPrim numParts rank xs]
  | "OpName.AllReducePrim", xs => [allReducePrim numParts rank xs]
  | _, _ => []

/-!
## Graph denotation (single forward fold)
-/

def storeSet (s : Store) (pairs : List (Tid × Tensor)) : Store :=
  fun tid =>
    match pairs.find? (fun p => decide (p.1 = tid)) with
    | some (_, v) => v
    | none => s tid

theorem storeSet_eq_of_find?_some (s : Store) (pairs : List (Tid × Tensor)) (tid : Tid) (v : Tensor)
    (h : pairs.find? (fun p => decide (p.1 = tid)) = some (tid, v)) :
    storeSet s pairs tid = v := by
  simp [storeSet, h]

theorem storeSet_eq_of_find?_none (s : Store) (pairs : List (Tid × Tensor)) (tid : Tid)
    (h : pairs.find? (fun p => decide (p.1 = tid)) = none) :
    storeSet s pairs tid = s tid := by
  simp [storeSet, h]

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
  let outs : List Tensor := evalOp g.numRanks n.rank n.op args
  let pairs : List (Tid × Tensor) := n.outs.zip outs
  storeSet s pairs

def denoteGraph (g : GraphDecl) (init : Store) : Store :=
  g.nodes.foldl (applyNode g) init

/-!
## Small `applyNode` rewrite lemmas (singleton outs)

These are definitional facts that keep generated proofs readable and avoid repeatedly
unfolding `storeSet`/`find?` for the common case `outs = [tid]`.
-/

theorem applyNode_fw_sum_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_sum", ins := [inTid], outs := [outTid] } outTid =
      fw_sum (s inTid) := by
  classical
  simp [applyNode, evalOp, storeSet]

theorem applyNode_chunkPrim_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.ChunkPrim", ins := [inTid], outs := [outTid] } outTid =
      chunkPrim g.numRanks rank (s inTid) := by
  classical
  simp [applyNode, evalOp, storeSet]

theorem applyNode_fw_linear_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid wTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_linear", ins := [xTid, wTid], outs := [outTid] } outTid =
      fw_linear (s xTid) (s wTid) := by
  classical
  simp [applyNode, evalOp, storeSet]

theorem applyNode_allReducePrim_out
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.AllReducePrim", ins := ins, outs := [outTid] } outTid =
      allReducePrim g.numRanks rank (ins.map s) := by
  classical
  simp [applyNode, evalOp, storeSet]

/-- applyNode for bw_sum with singleton output. -/
theorem applyNode_bw_sum_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_sum", ins := [gTid, xTid], outs := [outTid] } outTid =
      bw_sum (s gTid) (s xTid) := by
  classical
  simp [applyNode, evalOp, storeSet]

/-- applyNode for allGatherPrim with singleton output. -/
theorem applyNode_allGatherPrim_out
    (g : GraphDecl) (s : Store) (rank : Nat) (ins : List Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.AllGatherPrim", ins := ins, outs := [outTid] } outTid =
      allGatherPrim g.numRanks rank (ins.map s) := by
  classical
  simp [applyNode, evalOp, storeSet]

/-- applyNode for bw_linear first output (dx). -/
theorem applyNode_bw_linear_fst_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid dxTid dwTid : Tid)
    (_ : dxTid ≠ dwTid) :
    applyNode g s { rank := rank, op := "OpName.BW_linear", ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] } dxTid =
      (bw_linear (s gTid) (s xTid) (s wTid)).1 := by
  simp only [applyNode, evalOp, storeSet, List.map, List.zip]
  simp only [List.zipWith, List.find?]
  rfl

/-- applyNode for bw_linear second output (dw). -/
theorem applyNode_bw_linear_snd_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid dxTid dwTid : Tid)
    (hne : dxTid ≠ dwTid) :
    applyNode g s { rank := rank, op := "OpName.BW_linear", ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] } dwTid =
      (bw_linear (s gTid) (s xTid) (s wTid)).2 := by
  simp only [applyNode, evalOp, storeSet, List.map, List.zip]
  simp only [List.zipWith, List.find?]
  have hfalse : (dxTid = dwTid) = False := eq_false hne
  simp only [hfalse, decide_false, cond_false, decide_true, cond_true]

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
    let outs : List Tensor := evalOp g.numRanks n.rank n.op args
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

/-- Folding over nodes that don't write to tid preserves the value at tid. -/
theorem foldl_applyNode_preserves_tid (g : GraphDecl) (s : Store) (tid : Nat) (nodes : List NodeDecl)
    (h : ∀ n ∈ nodes, tid ∉ n.outs) :
    (nodes.foldl (applyNode g) s) tid = s tid := by
  induction nodes generalizing s with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.foldl]
    have hn : tid ∉ n.outs := h n (List.mem_cons.mpr (Or.inl rfl))
    have hns : ∀ n' ∈ ns, tid ∉ n'.outs := fun n' hn' => h n' (List.mem_cons.mpr (Or.inr hn'))
    rw [ih (applyNode g s n) hns]
    exact applyNode_eq_of_not_mem_outs g s n tid hn

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

/-- Denotation over `take (n+1)` equals one more `applyNode` over `take n`. -/
theorem denoteGraph_take_succ (g : GraphDecl) (init : Store) (n : Nat) (hn : n < g.nodes.length) :
    denoteGraph { g with nodes := g.nodes.take (n + 1) } init =
      applyNode g (denoteGraph { g with nodes := g.nodes.take n } init) (g.nodes.get ⟨n, hn⟩) := by
  -- Reduce to foldl on the node list, then use `foldl_take_succ`.
  change (g.nodes.take (n + 1)).foldl (applyNode g) init =
    applyNode g ((g.nodes.take n).foldl (applyNode g) init) (g.nodes.get ⟨n, hn⟩)
  exact foldl_take_succ (f := applyNode g) (l := g.nodes) (init := init) (n := n) hn

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

/-!
## Reconstruction for coarse lineage goals

We provide a default, *shape-directed* reconstruction:

- if shards are scalars (`shape = [1]`), we interpret reconstruction as a reduction over ranks;
- otherwise, we interpret it as an all-gather/concatenation along the last dimension.

This matches common tensor-parallel patterns and is sufficient for the current example.
If you need more precision, extend `LineageGoal` with slice metadata
and define a slice-based assembler.
-/

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
        allGatherPrim numParts rank xs

/-- `reconstruct` on a list with ≥2 elements and scalar head uses `allReducePrim`. -/
theorem reconstruct_cons_cons_scalar
    (numParts rank : Nat) (x y : Tensor) (xs : List Tensor)
    (h : x.shape = [1]) :
    reconstruct numParts rank (x :: y :: xs) = allReducePrim numParts rank (x :: y :: xs) := by
  -- Reduce by definition; the head shape decides the branch.
  simp [reconstruct, h]

/-- `reconstruct` on a list with ≥2 elements and non-scalar head uses `allGatherPrim`. -/
theorem reconstruct_cons_cons_nonscalar
    (numParts rank : Nat) (x y : Tensor) (xs : List Tensor)
    (h : x.shape ≠ [1]) :
    reconstruct numParts rank (x :: y :: xs) = allGatherPrim numParts rank (x :: y :: xs) := by
  -- Reduce by definition; the head shape decides the branch.
  simp [reconstruct, h]

/-- Scalar `reconstruct` reduces to the sum of scalar shards at index 0. -/
theorem reconstruct_scalar_valAt0_eq_sum
    (numParts rank : Nat) (x y : Tensor) (xs : List Tensor)
    (h : x.shape = [1]) :
    valAt (reconstruct numParts rank (x :: y :: xs)) 0 =
      (x :: y :: xs).foldl (fun acc t => acc + valAt t 0) 0 := by
  -- Switch to `allReducePrim` and use its `valAt0` lemma.
  have hrec : reconstruct numParts rank (x :: y :: xs) =
      allReducePrim numParts rank (x :: y :: xs) :=
    reconstruct_cons_cons_scalar numParts rank x y xs h
  have hshape : (allReducePrim numParts rank (x :: y :: xs)).shape = [1] := by
    -- Head of the list is `x`.
    have hhead : (x :: y :: xs).head? = some x := rfl
    have hshape' := allReducePrim_shape numParts rank (x :: y :: xs) x hhead
    exact hshape'.trans h
  have hpos : 0 < prodShape (allReducePrim numParts rank (x :: y :: xs)).shape := by
    -- prodShape [1] = 1
    have : prodShape ([1] : Shape) = 1 := prodShape_one
    -- rewrite the shape and finish
    simp [hshape, this]
  -- Use the allReduce value lemma.
  have hval : valAt (allReducePrim numParts rank (x :: y :: xs)) 0 =
      (x :: y :: xs).foldl (fun acc t => acc + valAt t 0) 0 :=
    allReducePrim_valAt0_of_pos numParts rank (x :: y :: xs) hpos
  have hval' : valAt (reconstruct numParts rank (x :: y :: xs)) 0 =
      (x :: y :: xs).foldl (fun acc t => acc + valAt t 0) 0 := by
    rw [hrec]
    exact hval
  exact hval'

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

set_option maxHeartbeats 0 in
-- The proof is a large index-manipulation lemma; disable heartbeats to avoid deterministic timeouts.
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
          simp [hparts]
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
          simp [pieces, hnp, list_ofFn_head_eq]
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
          simp [hws', hw]
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
    simp [h1, h2, Nat.add_assoc]
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
          simp [hws', hw]
    have hmap := allGatherPrim_valAt_mul_add numParts r o shard ws hheadW hparts hr_lt t ht j hj_lt
    have hidx' : t * (shard * numParts) + r * shard + j = t * i + (r * shard + j) := by
      simp [hi, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc]
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
    simp [full, hi, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc]
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

/-!
## bw_linear (dW) with column-sharded inputs (allGather over i)

This lemma states that when the input matrix `x` is sharded along the input dimension `i`
and reassembled by `allGatherPrim`, the weight gradient (dW) computed by `bw_linear`
is exactly the `allGatherPrim` of per-shard dW results.

Key insight: dW = gradOut.T @ x, so sharding x along columns shards dW along columns.
Unlike dX, dW does NOT depend on the weight matrix w.
-/

set_option maxHeartbeats 0 in
-- Extensive index arithmetic across allGather and bw_linear requires many heartbeats
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
        have hparts' : 0 < Nat.succ n := by simp [hnp] at hparts; simp [hparts]
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
          simp [pieces, hnp, list_ofFn_head_eq]
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
          simp [hws', hw]
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
    simp [h1, h2, Nat.add_assoc]
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
    simp [full, hi, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc]
  have hidx_eq' : idx = c * full + r * shard + j := by simpa [Nat.add_assoc] using hidx_eq
  have hvalL'' : valAt (bw_linear g x (allGatherPrim numParts 0 ws)).2 idx =
      ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt x (p * i + (r * shard + j))) := by
    simpa [hidx_eq', hidx_norm] using hvalL'
  have hvalR''' : valAt (allGatherPrim numParts 0 pieces) idx =
      ∑ p ∈ Finset.range b, (valAt g (p * o + c)) * (valAt x (p * i + (r * shard + j))) := by
    simpa [hidx_eq'] using hvalR''
  exact hvalL''.trans hvalR'''.symm

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

/-- bw_linear first output shape: either 2D [bX, iX] or empty [] (fallback). -/
theorem bw_linear_fst_shape_cases (gradOut x w : Tensor) :
    (∃ b i, (bw_linear gradOut x w).1.shape = [b, i]) ∨ (bw_linear gradOut x w).1.shape = [] := by
  unfold bw_linear
  split
  · next bG oG bX iX oW iW hg hx hw =>
    simp only [Tensor.mkShape]
    exact Or.inl ⟨bX, iX, rfl⟩
  · next hfall =>
    simp only [Tensor.mkShape]
    exact Or.inr trivial

/-- bw_linear second output shape: either 2D [oW, iW] or empty [] (fallback). -/
theorem bw_linear_snd_shape_cases (gradOut x w : Tensor) :
    (∃ o i, (bw_linear gradOut x w).2.shape = [o, i]) ∨ (bw_linear gradOut x w).2.shape = [] := by
  unfold bw_linear
  split
  · next bG oG bX iX oW iW hg hx hw =>
    simp only [Tensor.mkShape]
    exact Or.inl ⟨oW, iW, rfl⟩
  · next hfall =>
    simp only [Tensor.mkShape]
    exact Or.inr trivial

/-- Shape of bw_linear first output via applyNode. -/
theorem applyNode_bw_linear_fst_shape
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid dxTid dwTid : Tid)
    (hne : dxTid ≠ dwTid)
    (hg : ∃ bG oG, (s gTid).shape = [bG, oG])
    (hx : ∃ bX iX, (s xTid).shape = [bX, iX])
    (hw : ∃ oW iW, (s wTid).shape = [oW, iW]) :
    ∃ b i, (applyNode g s { rank := rank, op := "OpName.BW_linear", ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] } dxTid).shape = [b, i] := by
  rw [applyNode_bw_linear_fst_out g s rank gTid xTid wTid dxTid dwTid hne]
  exact bw_linear_fst_is_2d (s gTid) (s xTid) (s wTid) hg hx hw

/-- Shape of bw_linear second output via applyNode. -/
theorem applyNode_bw_linear_snd_shape
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid dxTid dwTid : Tid)
    (hne : dxTid ≠ dwTid)
    (hg : ∃ bG oG, (s gTid).shape = [bG, oG])
    (hx : ∃ bX iX, (s xTid).shape = [bX, iX])
    (hw : ∃ oW iW, (s wTid).shape = [oW, iW]) :
    ∃ o i, (applyNode g s { rank := rank, op := "OpName.BW_linear", ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] } dwTid).shape = [o, i] := by
  rw [applyNode_bw_linear_snd_out g s rank gTid xTid wTid dxTid dwTid hne]
  exact bw_linear_snd_is_2d (s gTid) (s xTid) (s wTid) hg hx hw

/-!
## Unified Distributivity Theorems for Tensor Parallelism
-/

-- Auxiliary lemma: allReducePrim shape from List.ofFn of tensors with same shape
lemma allReducePrim_ofFn_shape {n : Nat} (numParts : Nat) (axis : Nat)
    (sh : Shape) (f : Fin (n + 1) → Tensor)
    (hf : ∀ i, (f i).shape = sh) :
    (allReducePrim numParts axis (List.ofFn f)).shape = sh := by
  simp only [allReducePrim, Tensor.mkShape]
  have hhead := list_ofFn_head_eq f
  simp only [hhead, Option.map_some, hf 0, Option.getD_some]

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
    | succ n => simp [List.ofFn, Fin.foldr_succ, Tensor.mkShape]
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
    simp only [allReducePrim, Tensor.mkShape, Tensor.mk]
    -- Use our auxiliary lemma to establish the shape
    have hhead : (List.ofFn (fun r : Fin numParts =>
        (Tensor.mk [m, n] (k_matmul m n shard (chunkPrim numParts r.val a)
          (bs.get ⟨r.val, by omega⟩))))).head? = some (Tensor.mk [m, n]
          (k_matmul m n shard (chunkPrim numParts 0 a) (bs.get ⟨0, by omega⟩))) := by
      subst hnp
      exact list_ofFn_head_eq _
    simp only [hhead, Option.map_some, Tensor.mk, Option.getD_some, prodShape, List.foldl, Nat.one_mul]
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
  rw [valAt_of_lt _ _ (by simp only [Tensor.mkShape, prodShape, List.foldl, Nat.one_mul]; exact hpnc_lt)]
  simp only [Tensor.mkShape, k_matmul, hdiv, hmod]
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
    exact hws_shapes _ (by simp [List.get_mem])
  simp only [this]
  have hconv : Tensor.mkShape [b, o] (k_matmul b o i x (allGatherPrim numParts 0 ws)) =
      Tensor.mkShape [b, o] (k_matmul b o (numParts * shard) x (allGatherPrim numParts 0 ws)) := by
    rw [← hi]
  rw [hconv]
  convert matmul_allGather_eq_allReduce_matmul_chunk b o (numParts * shard) numParts shard x ws
    _ rfl hws_len hws_shapes hparts hshard
  rw [← hi]; exact hx

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
    ts = reconstruct numParts 0 tps

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
      ts = reconstruct pm.numRanks 0 tps

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
      ts = reconstruct pm.numRanks 0 tps

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
      ts = reconstruct pm.numRanks 0 tps

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
    ts = reconstruct numParts 0 tps

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
      ts = reconstruct pm.numRanks 0 tps

/-- If we prove the full statement for a goal, the incremental version follows. -/
theorem CoarseLineageHoldsWithIntermediates_of_full
    (sm pm : GraphDecl) (goal : LineageGoal)
    (smInit pmInit : ShapeEnv) (initGoals prereqGoals : List LineageGoal)
    (hfull : CoarseLineageHoldsWithInit sm pm goal smInit pmInit initGoals) :
    CoarseLineageHoldsWithIntermediates sm pm goal smInit pmInit initGoals prereqGoals := by
  intro initSM initPM hSmInit hPmInit hInitGoals hPrereqs
  exact hfull initSM initPM hSmInit hPmInit hInitGoals

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

end
end TrainVerify.Denote
