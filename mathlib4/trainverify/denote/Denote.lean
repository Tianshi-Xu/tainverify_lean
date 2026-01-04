import Std
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic

namespace TrainVerify.Denote

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

def Tensor.mkShape (sh : Shape) (v : Fin (prodShape sh) → Scalar) : Tensor := { shape := sh, val := v }

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

theorem Finset.sum_range_mul_eq_sum_sum (n m : Nat) (f : Nat → Scalar) :
    (∑ k ∈ Finset.range (n * m), f k) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f (i * m + j) := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- Split `range ((n+1)*m)` into `range (n*m)` plus the last block `n*m + range m`.
      have hmul : (n + 1) * m = n * m + m := by
        simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hsplit : Finset.range ((n + 1) * m) =
          Finset.range (n * m) ∪ (Finset.range m).map (addLeftEmbedding (n * m)) := by
        simpa [hmul] using (Finset.range_add (n * m) m)
      have hdisj : Disjoint (Finset.range (n * m)) ((Finset.range m).map (addLeftEmbedding (n * m))) := by
        simpa using (Finset.disjoint_range_addLeftEmbedding (n * m) (Finset.range m))
      have hmap : (∑ k ∈ (Finset.range m).map (addLeftEmbedding (n * m)), f k) =
          ∑ j ∈ Finset.range m, f (n * m + j) := by
        -- `Finset.sum_map` over the embedding.
        exact
          (Finset.sum_map (s := Finset.range m) (e := addLeftEmbedding (n * m)) (f := fun k => f k))
      calc
        (∑ k ∈ Finset.range ((n + 1) * m), f k)
            = (∑ k ∈ Finset.range (n * m) ∪ (Finset.range m).map (addLeftEmbedding (n * m)), f k) := by
                simp [hsplit]
        _ = (∑ k ∈ Finset.range (n * m), f k) +
              ∑ k ∈ (Finset.range m).map (addLeftEmbedding (n * m)), f k := by
                simp [Finset.sum_union hdisj]
        _ = (∑ k ∈ Finset.range (n * m), f k) + ∑ j ∈ Finset.range m, f (n * m + j) := by
              simp [hmap]
        _ = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f (i * m + j)) +
              ∑ j ∈ Finset.range m, f (n * m + j) := by
              simp [ih]
        _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range m, f (i * m + j) := by
              -- `sum_range_succ` on the outer sum.
              simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

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

def zeroTensor (sh : Shape) : Tensor :=
  Tensor.mkShape sh (fun _ => 0)

def k_fw_sum (t : Tensor) : Fin (prodShape [1]) → Scalar :=
  fun _ =>
    (∑ i : Fin (prodShape t.shape), t.val i)

def k_bw_sum (gradOut : Tensor) (x : Tensor) : Fin (prodShape x.shape) → Scalar :=
  fun _ => valAt gradOut 0

-- Linear uses weight layout `w : [O, I]` (output-major), matching the backend graphs.
def k_fw_linear_matmul (b i o : Nat) (x w : Tensor) : Fin (prodShape [b, o]) → Scalar :=
  fun outIdx =>
    let r := outIdx.1 / o
    let c := outIdx.1 % o
    ∑ k ∈ Finset.range i,
      (valAt x (r * i + k)) * (valAt w (c * i + k))

def k_bw_linear_dx_matmul (b i o : Nat) (gradOut w : Tensor) : Fin (prodShape [b, i]) → Scalar :=
  fun dxIdx =>
    let r := dxIdx.1 / i
    let k := dxIdx.1 % i
    ∑ c ∈ Finset.range o,
      (valAt gradOut (r * o + c)) * (valAt w (c * i + k))

def k_bw_linear_dw_matmul (b i o : Nat) (gradOut x : Tensor) : Fin (prodShape [o, i]) → Scalar :=
  fun dwIdx =>
    let c := dwIdx.1 / i
    let k := dwIdx.1 % i
    ∑ r ∈ Finset.range b,
      (valAt gradOut (r * o + c)) * (valAt x (r * i + k))

def k_chunk_last
    (_prefLen d shard rank numParts : Nat) (x : Tensor) : Fin (prodShape (appendLast (dropLast x.shape) shard)) → Scalar :=
  fun outIdx =>
    let idx := outIdx.1
    let p := if shard = 0 then 0 else idx / shard
    let j := if shard = 0 then 0 else idx % shard
    let r := if numParts = 0 then rank else rank % numParts
    valAt x (p * d + r * shard + j)

def k_allgather_last
    (_prefLen shard numParts : Nat) (pieces : List Tensor) : Fin (prodShape (appendLast (dropLast ((pieces.head?.map (fun t => t.shape)).getD [])) (shard * numParts))) → Scalar :=
  fun outIdx =>
    let full := shard * numParts
    let idx := outIdx.1
    let p := if full = 0 then 0 else idx / full
    let l := if full = 0 then 0 else idx % full
    let r := if shard = 0 then 0 else l / shard
    let j := if shard = 0 then 0 else l % shard
    let shardShape := (pieces.head?.map (fun t => t.shape)).getD []
    let pref := dropLast shardShape
    let piece := pieces.getD r (zeroTensor (appendLast pref shard))
    valAt piece (p * shard + j)

/-!
## Operator wrappers (shape + value)
-/

def fw_sum (x : Tensor) : Tensor :=
  Tensor.mkShape [1] (k_fw_sum x)

def bw_sum (gradOut x : Tensor) : Tensor :=
  Tensor.mkShape x.shape (k_bw_sum gradOut x)

def fw_linear (x w : Tensor) : Tensor :=
  -- Intended: x:[B,I], w:[I,O] => y:[B,O]
  match x.shape, w.shape with
  | [b, i], [o, _i2] =>
      -- We intentionally do not branch on the equality of inner dimensions here.
      -- Graph consistency is enforced separately by shape assumptions.
      Tensor.mkShape [b, o] (k_fw_linear_matmul b i o x w)
  | _, _ => Tensor.mkShape [] (fun _ => 0)

def bw_linear (gradOut x w : Tensor) : Tensor × Tensor :=
  match gradOut.shape, x.shape, w.shape with
  | [_bG, _oG], [bX, iX], [oW, iW] =>
      -- As with `fw_linear`, we do not branch on dimension equalities here.
      -- Under the intended shape assumptions, these dimensions match.
      let dx := Tensor.mkShape [bX, iX] (k_bw_linear_dx_matmul bX iX oW gradOut w)
      let dw := Tensor.mkShape [oW, iW] (k_bw_linear_dw_matmul bX iW oW gradOut x)
      (dx, dw)
      | _, _, _ => (Tensor.mkShape [] (fun _ => 0), Tensor.mkShape [] (fun _ => 0))

def chunkPrim (numParts rank : Nat) (x : Tensor) : Tensor :=
  -- Split along last dimension: prefix same, last := last/numParts
  let pref := dropLast x.shape
  let d := lastD x.shape
  let shard := divNat d numParts
  let prefLen := prodShape pref
  Tensor.mkShape (appendLast pref shard) (k_chunk_last prefLen d shard rank numParts x)

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
    simp [divNat, Nat.mul_div_left, hnumParts_ne0]

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
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.1

  have hmod_p : (p * shard + j) % shard = j := by
    have heq : j + shard * p = p * shard + j := by
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.2

  have hrmod : (rank % numParts) = rank := Nat.mod_eq_of_lt hrank

  -- Unfold `chunkPrim` and `k_chunk_last` only locally, then discharge the `if` branches.
  have h0 : valAt (chunkPrim numParts rank x) (p * shard + j) =
      (chunkPrim numParts rank x).val ⟨p * shard + j, hlt_chunk⟩ := by
    simp [valAt, hlt_chunk]
  rw [h0]
  -- The remaining simplification is small: unfold the local kernel and rewrite div/mod.
  simp [chunkPrim, Tensor.mkShape, k_chunk_last, hshape, dropLast, lastD, appendLast, divNat,
    hdrop, hlast, hdiv', hnumParts_ne0, hshard_pos.ne', hdiv_p, hmod_p, hrmod, valAt_of_lt]

def allGatherPrim (numParts _rank : Nat) (xs : List Tensor) : Tensor :=
  -- Reassemble along last dimension: prefix same, last := shard*numParts
  let shardShape := (xs.head?.map (fun t => t.shape)).getD []
  let pref := dropLast shardShape
  let shard := lastD shardShape
  let full := shard * numParts
  let prefLen := prodShape pref
  Tensor.mkShape (appendLast pref full) (k_allgather_last prefLen shard numParts xs)

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
    have : p * (shard * numParts) + rank * shard + j = p * (shard * numParts) + (rank * shard + j) := by
      omega
    -- `prodShape [o, shard*numParts] = o*(shard*numParts)`
    simpa [hshape_out, prodShape, this] using hlt_full

  -- Reduce the division/mod computations in `k_allgather_last`.
  have hdiv_full : (p * (shard * numParts) + rank * shard + j) / (shard * numParts) = p := by
    have heq : (rank * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + rank * shard + j := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, by
      -- remainder < divisor
      simpa [Nat.add_assoc] using (by
        -- `rank*shard+j < shard*numParts`
        exact hrem_lt_full)⟩ |>.1

  have hmod_full : (p * (shard * numParts) + rank * shard + j) % (shard * numParts) = rank * shard + j := by
    have heq : (rank * shard + j) + (shard * numParts) * p =
        p * (shard * numParts) + rank * shard + j := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hfull_pos).2 ⟨heq, by
      simpa [Nat.add_assoc] using hrem_lt_full⟩ |>.2

  have hdiv_shard : (rank * shard + j) / shard = rank := by
    have heq : j + shard * rank = rank * shard + j := by
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.1

  have hmod_shard : (rank * shard + j) % shard = j := by
    have heq : j + shard * rank = rank * shard + j := by
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique hshard_pos).2 ⟨heq, hj⟩ |>.2

  have hrmod : (rank % numParts) = rank := Nat.mod_eq_of_lt hrank

  -- Finally, unfold only locally.
  have h0 : valAt (allGatherPrim numParts 0 pieces) (p * (shard * numParts) + rank * shard + j) =
      (allGatherPrim numParts 0 pieces).val ⟨p * (shard * numParts) + rank * shard + j, hlt_out⟩ := by
    simp [valAt, hlt_out]
  rw [h0]
  simp [allGatherPrim, Tensor.mkShape, k_allgather_last, hhead, dropLast, lastD, appendLast,
    hnumParts_ne0, hshard_pos.ne', hfull_pos.ne', hdiv_full, hmod_full, hdiv_shard, hmod_shard, hrmod,
    valAt_of_lt]

def allReducePrim (_numParts _rank : Nat) (xs : List Tensor) : Tensor :=
  let sh := (xs.head?.map (fun t => t.shape)).getD []
  Tensor.mkShape sh (fun idx => xs.foldl (fun acc t => acc + valAt t idx.1) 0)

/-!
## Small value-level lemmas (avoid giant simp)

These lemmas are intentionally lightweight and rewrite only the *observable scalar* values
we need in generated specs.
-/

@[simp] theorem prodShape_one : prodShape ([1] : Shape) = 1 := by
  simp [prodShape]

theorem fw_sum_valAt0 (x : Tensor) : valAt (fw_sum x) 0 = (∑ i : Fin (prodShape x.shape), x.val i) := by
  -- `fw_sum x` is a scalar tensor; `valAt` at 0 is the stored value.
  have h0 : (0 : Nat) < prodShape (fw_sum x).shape := by
    simp [fw_sum, Tensor.mkShape]
  -- Reduce the guard and unfold the constant kernel.
  simp [fw_sum, Tensor.mkShape, k_fw_sum, valAt, h0]

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
    simp [divNat, Nat.mul_div_left, hnumParts_ne0]

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
  -- Normalize `prodShape x.shape`.
  simp [hshape, prodShape]

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
  simpa [Nat.add_assoc] using
    (Finset.sum_comm (s := Finset.range numParts) (t := Finset.range b)
      (f := fun r p => ∑ j ∈ Finset.range shard, valAt x (p * (numParts * shard) + r * shard + j))).symm


/-!
## Linear / reduction algebra lemmas (dimension-parametric)

These are the key “math facts” used to avoid unfolding huge generated graphs.

They do **not** hard-code concrete dimensions (like 4/8/16/128). Instead they are stated
in terms of parameters `b o numParts shard` and explicit shape equalities.
-/

theorem fw_linear_valAt_mul_add
    (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i])
    (hw : w.shape = [o, i])
    (p : Nat) (hp : p < b)
    (c : Nat) (hc : c < o) :
    valAt (fw_linear x w) (p * o + c) =
      ∑ k ∈ Finset.range i, (valAt x (p * i + k)) * (valAt w (c * i + k)) := by
  -- Prove the queried index is in-bounds for the output tensor `[b,o]`.
  have hlt_bo : p * o + c < b * o := by
    have hlt1 : p * o + c < p * o + o := by
      simpa [Nat.add_assoc] using Nat.add_lt_add_left hc (p * o)
    have hlt2 : p * o + c < (p + 1) * o := by
      simpa [Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc] using hlt1
    have hle : (p + 1) * o ≤ b * o := Nat.mul_le_mul_right o (Nat.succ_le_of_lt hp)
    exact lt_of_lt_of_le hlt2 hle
  have hlt' : (p * o + c) < prodShape ([b, o] : Shape) := by
    simpa [prodShape] using hlt_bo
  -- Reduce the output index division/modulo (used inside the matmul kernel).
  have ho_pos : 0 < o := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  have hdiv : (p * o + c) / o = p := by
    have heq : c + o * p = p * o + c := by
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique ho_pos).2 ⟨heq, hc⟩ |>.1
  have hmod : (p * o + c) % o = c := by
    have heq : c + o * p = p * o + c := by
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Nat.div_mod_unique ho_pos).2 ⟨heq, hc⟩ |>.2
  -- Now rewrite `fw_linear` into `Tensor.mkShape [b,o] ...` and unfold `valAt` at an in-bounds index.
  have hfw : fw_linear x w = Tensor.mkShape [b, o] (k_fw_linear_matmul b i o x w) := by
    simp [fw_linear, hx, hw, Tensor.mkShape]
  -- With `hfw`, unfold only the *outer* `valAt` (keep inner `valAt` calls opaque).
  rw [hfw]
  -- `valAt (Tensor.mkShape ...)` at an in-bounds index is just the kernel evaluation.
  simp [valAt, hlt', Tensor.mkShape]
  -- Unfold the kernel and rewrite div/mod.
  dsimp [k_fw_linear_matmul]
  -- At this point the only remaining simplification is the `valAt` guards.
  simp [hdiv, hmod, valAt]


theorem swap_range_list_sum_valAt (N : Nat) (xs : List Tensor) :
  (∑ k ∈ Finset.range N, (xs.map (fun t => valAt t k)).sum) =
    (xs.map (fun t => ∑ k ∈ Finset.range N, valAt t k)).sum := by
  classical
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    -- Expand the list sum and distribute the finite sum.
    simp [List.map, List.sum_cons, Finset.sum_add_distrib, ih, add_assoc, add_left_comm, add_comm]

  theorem List.foldl_add_eq_add_sum {α β : Type} [AddMonoid β] (f : α → β) (b : β) (xs : List α) :
    xs.foldl (fun acc x => acc + f x) b = b + (xs.map f).sum := by
    induction xs generalizing b with
    | nil =>
      simp
    | cons a as ih =>
      simpa [List.foldl, List.map, List.sum_cons, add_assoc] using (ih (b := b + f a))


theorem fw_sum_allReducePrim_eq_sum_fw_sum_of_cons
    (numParts rank : Nat) (x : Tensor) (xs : List Tensor)
    (hall : ∀ t ∈ xs, t.shape = x.shape) :
    valAt (fw_sum (allReducePrim numParts rank (x :: xs))) 0 =
      ((x :: xs).map (fun t => valAt (fw_sum t) 0)).sum := by
  classical
  -- Work in range-sum form; for a nonempty all-reduce, the output shape is `x.shape`.
  rw [fw_sum_valAt0_eq_sum_range_valAt]
  -- Rewrite the range size using the definitional shape of `allReducePrim`.
  simp [allReducePrim, Tensor.mkShape]
  -- Rewrite each `valAt` term into the underlying fold (in-bounds by `mem_range`).
  -- After `simp`, the kernel is `xs.foldl ... (x.val idx)` (i.e. the head step is already done).
  have hterm :
      ∀ k, k ∈ Finset.range (prodShape x.shape) →
        valAt ({ shape := x.shape, val := fun idx => xs.foldl (fun acc t => acc + valAt t idx.1) (x.val idx) } : Tensor) k =
          xs.foldl (fun acc t => acc + valAt t k) (valAt x k) := by
    intro k hk
    have hklt : k < prodShape x.shape := Finset.mem_range.1 hk
    -- Rewrite only the *outer* `valAt` on the constructed tensor using `valAt_of_lt`.
    let T : Tensor := { shape := x.shape, val := fun idx => xs.foldl (fun acc t => acc + valAt t idx.1) (x.val idx) }
    have hTlt : k < prodShape T.shape := by
      simpa [T] using hklt
    have hT : valAt T k = xs.foldl (fun acc t => acc + valAt t k) (x.val ⟨k, by simpa [T] using hTlt⟩) := by
      -- `valAt T k = T.val ⟨k,hTlt⟩`.
      have h' : valAt T k = T.val ⟨k, hTlt⟩ := by
        simpa using (valAt_of_lt (t := T) (k := k) hTlt)
      -- Unfold `T.val` at this index; note `⟨k,hTlt⟩.1 = k`.
      simpa [T] using h'
    -- Rewrite the head value `x.val ...` as `valAt x k` using `valAt_of_fin`.
    have hxval : x.val ⟨k, by simpa [T] using hTlt⟩ = valAt x k := by
      -- `valAt x k = x.val ⟨k, hklt⟩`, so use the same proof via rewriting.
      have : valAt x k = x.val ⟨k, by simpa [T] using hTlt⟩ := by
        simpa using (valAt_of_fin x ⟨k, by simpa [T] using hTlt⟩)
      simpa using this.symm
    -- Finish.
    simp [T, hT, hxval]
  -- Rewrite the whole LHS sum using `hterm`.
  have hL :
      (∑ k ∈ Finset.range (prodShape x.shape),
          valAt ({ shape := x.shape, val := fun idx => xs.foldl (fun acc t => acc + valAt t idx.1) (x.val idx) } : Tensor) k) =
        ∑ k ∈ Finset.range (prodShape x.shape),
          xs.foldl (fun acc t => acc + valAt t k) (valAt x k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [hterm k hk]
  -- Replace the fold by `valAt x k + sum_{t∈xs} valAt t k`, then swap the sums.
  rw [hL]
  have hfold :
      ∀ k,
        xs.foldl (fun acc t => acc + valAt t k) (valAt x k) =
          valAt x k + (xs.map (fun t => valAt t k)).sum := by
    intro k
    simpa using (List.foldl_add_eq_add_sum (f := fun t : Tensor => valAt t k) (b := valAt x k) (xs := xs))
  -- Rewrite the body under the `Finset` sum.
  have hL' :
      (∑ k ∈ Finset.range (prodShape x.shape),
          xs.foldl (fun acc t => acc + valAt t k) (valAt x k)) =
        ∑ k ∈ Finset.range (prodShape x.shape),
          (valAt x k + (xs.map (fun t => valAt t k)).sum) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [hfold k]
  rw [hL']
  -- Distribute the outer sum.
  simp [Finset.sum_add_distrib]
  -- Swap the range-sum with the list-sum for the tail part.
  rw [swap_range_list_sum_valAt (N := prodShape x.shape) (xs := xs)]
  -- Finally, rewrite each inner range-sum as `fw_sum` using shape equalities.
  -- Head element is immediate.
  have hxsum : (∑ k ∈ Finset.range (prodShape x.shape), valAt x k) = valAt (fw_sum x) 0 := by
    simpa using (fw_sum_valAt0_eq_sum_range_valAt x).symm
  -- Tail elements use `hall` to align `prodShape`.
  have htsum :
      (xs.map (fun t => ∑ k ∈ Finset.range (prodShape x.shape), valAt t k)).sum =
        (xs.map (fun t => valAt (fw_sum t) 0)).sum := by
    -- Keep the induction hypothesis small.
    clear hterm hL hfold hL'
    induction xs with
    | nil =>
        simp
    | cons t ts ih =>
        have htshape : t.shape = x.shape := hall t (by simp)
        have hhall' : ∀ u ∈ ts, u.shape = x.shape := by
          intro u hu
          exact hall u (by simp [hu])
        have ht : (∑ k ∈ Finset.range (prodShape x.shape), valAt t k) = valAt (fw_sum t) 0 := by
          have : (∑ k ∈ Finset.range (prodShape t.shape), valAt t k) = valAt (fw_sum t) 0 :=
            (fw_sum_valAt0_eq_sum_range_valAt t).symm
          simpa [htshape] using this
        simp [List.map, List.sum_cons, ht, ih (hall := hhall')]
  -- Put it together.
  simp [List.map, List.sum_cons, hxsum, htsum, add_assoc]



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

/-!
## Dimension consistency (well-formedness)

The operator semantics above are intentionally total (they always return a tensor), and we removed
most shape-checking branches to keep later expression-level proofs simple.

Instead, we make **dimension matching** an explicit proof obligation: a graph is *dimension-consistent*
if, along the denotation fold, every node is applied to arguments whose shapes satisfy the expected
constraints of that operator.

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
          simp [List.zipWith, hx, hrec]

theorem not_mem_map_fst_zip_of_not_mem_left (tid : Tid) (xs : List Tid) (ys : List Tensor)
    (h : tid ∉ xs) : tid ∉ (xs.zip ys).map Prod.fst := by
  -- `List.zip` is `zipWith Prod.mk`.
  simpa [List.zip] using not_mem_map_fst_zipWith_of_not_mem_left tid xs ys h

theorem applyNode_eq_of_not_mem_outs (g : GraphDecl) (s : Store) (n : NodeDecl) (tid : Tid)
    (h : tid ∉ n.outs) : applyNode g s n tid = s tid := by
  -- `applyNode` updates only tids listed in `n.outs` (modulo zip truncation).
  simp [applyNode, storeSet_eq_of_not_mem_fst, not_mem_map_fst_zip_of_not_mem_left, h]

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
If you need more precision, extend `LineageGoal` with slice metadata and define a slice-based assembler.
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

    end
    end TrainVerify.Denote
