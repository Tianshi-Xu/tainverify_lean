import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import trainverify.attention_complex
-- Add ext attribute for OnlineState
attribute [ext] OnlineState

/-!
# Formal Verification of Attention Mechanism Equivalence (2D Matrix version)

This file contains a formal proof that the standard attention mechanism and
FlashAttention algorithm are mathematically equivalent when applied to 2D matrices.

The proof is an extension of the 1D vector case. The softmax operation is
applied column-wise, and the proof shows that applying the online (block-wise)
algorithm to blocks of rows is equivalent to applying the standard softmax
algorithm to the entire matrix at once.

## Main Results

* `softmax_equivalence_2d`: Proves that FlashAttention produces the same output as standard attention for matrices.

-/

noncomputable section

open BigOperators Real

-- Work with fixed dimensions for simplicity
variable (n m : ℕ) [NeZero n]

-- Softmax for a single vector, reused from 1D proof
def softmax_vec {n : ℕ} [NeZero n] (v : Vec n) : Vec n :=
  softmax v

-- Online softmax state for 2D matrices.
-- We maintain a running max and sum for each column.
structure OnlineState2D (n m : ℕ) where
  m_vals : Vec m      -- running maximum for each column
  l_vals : Vec m      -- running sum of exponentials for each column
  finished : Bool

-- Update function for online softmax on a matrix block.
-- This applies the 1D update logic to each column in parallel.
def update_online_state2D {n m : ℕ} [NeZero n] (state : OnlineState2D n m) (new_block : Mat n m) : OnlineState2D n m :=
  have _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (NeZero.pos n)
  let m_new_local_vec := fun j => Finset.univ.sup' Finset.univ_nonempty (fun i => new_block i j)
  let m_new_vec := fun j => max (state.m_vals j) (m_new_local_vec j)
  let l_new_vec := fun j =>
    let exp_old := Real.exp (state.m_vals j - m_new_vec j)
    let exp_new := Real.exp (m_new_local_vec j - m_new_vec j)
    let sum_new_block_exp := ∑ i : Fin n, Real.exp (new_block i j - m_new_local_vec j)
    exp_old * (state.l_vals j) + exp_new * sum_new_block_exp
  { m_vals := m_new_vec, l_vals := l_new_vec, finished := true }

-- Initial state for 2D online softmax.
def initial_state2D (n m : ℕ) : OnlineState2D n m :=
  { m_vals := fun _ => -1000000, l_vals := fun _ => 0, finished := false }

-- Invariant for the 2D online softmax state.
-- The invariant from the 1D case must hold for each column.
structure StateInvariant2D (n m : ℕ) [NeZero n] (state : OnlineState2D n m) (processed_matrices : List (Mat n m)) where
  inv : ∀ j : Fin m,
    let processed_vectors_j := processed_matrices.map (fun mat => fun i => mat i j)
    let state_j : OnlineState n := { m := state.m_vals j, l := state.l_vals j, finished := state.finished }
    StateInvariant n state_j processed_vectors_j

-- Key lemma: a single update preserves the invariant for all columns.
lemma update_preserves_invariant2D {n m : ℕ} [NeZero n] (state : OnlineState2D n m) (new_mat : Mat n m)
  (processed : List (Mat n m)) (h_inv : StateInvariant2D n m state processed) :
  StateInvariant2D n m (update_online_state2D state new_mat) (processed ++ [new_mat]) := by
  constructor
  intro j
  -- The 2D invariant for column `j` is proven by applying the 1D preservation lemma.
  let processed_vectors_j := List.map (fun mat => fun i => mat i j) processed
  let state_j : OnlineState n := { m := state.m_vals j, l := state.l_vals j, finished := state.finished }
  let new_vec_j := fun i => new_mat i j
  -- The invariant for the `j`-th column holds by hypothesis.
  have h_inv_j : StateInvariant n state_j processed_vectors_j := h_inv.inv j
  -- Apply the 1D lemma.
  have h_1d_lemma_res := update_preserves_invariant state_j new_vec_j processed_vectors_j h_inv_j

  -- Prove that the new state and processed list for column `j` match the result of the 1D lemma.
  have h_processed_eq : (processed ++ [new_mat]).map (fun mat => fun i => mat i j) = processed_vectors_j ++ [new_vec_j] := by
    simp [List.map_append, processed_vectors_j, new_vec_j]
  have h_state_eq : { m := (update_online_state2D state new_mat).m_vals j, l := (update_online_state2D state new_mat).l_vals j, finished := (update_online_state2D state new_mat).finished } = update_online_state state_j new_vec_j := by
    -- Prove equality field by field
    constructor

  -- Rewrite the goal using these equalities and apply the 1D lemma result.
  rw [h_state_eq, h_processed_eq]
  exact h_1d_lemma_res

-- Base case: initial state is valid for an empty list of matrices.
lemma initial_invariant2D {n m : ℕ} [NeZero n] : StateInvariant2D n m (initial_state2D n m) [] := by
  constructor
  intro j
  simp [initial_state2D, initial_state]
  exact initial_invariant

-- Inductive step: processing matrix blocks preserves the invariant.
lemma process_blocks_invariant2D {n m : ℕ} [NeZero n] (blocks : List (Mat n m)) :
  StateInvariant2D n m (blocks.foldl update_online_state2D (initial_state2D n m)) blocks := by
  -- The proof is by induction on the list of blocks, analogous to the 1D case.
  suffices ∀ (remaining : List (Mat n m)) (processed : List (Mat n m)) (state : OnlineState2D n m),
      StateInvariant2D n m state processed →
      StateInvariant2D n m (remaining.foldl update_online_state2D state) (processed ++ remaining) by
    exact this blocks [] (initial_state2D n m) initial_invariant2D

  intro remaining
  induction remaining with
  | nil =>
    intro processed state h_inv
    simp only [List.foldl_nil, List.append_nil]
    exact h_inv
  | cons head tail ih =>
    intro processed state h_inv
    rw [List.foldl_cons, List.append_cons]
    exact ih (processed ++ [head]) (update_online_state2D state head) (update_preserves_invariant2D state head processed h_inv)

/--
Computes softmax on a list of matrix blocks using the standard method.
All matrices are treated as a single concatenated matrix.
-/
def standard_softmax_on_blocks_2d {n m : ℕ} [NeZero n] (blocks : List (Mat n m)) : List (Mat n m) :=
  match blocks with
  | [] => []
  | _ =>
    -- For each column, calculate the global max and sum over all blocks.
    let M_vec := fun j => (blocks.map (fun mat => fun i => mat i j)).foldl (fun acc v => max acc (Finset.univ.sup' Finset.univ_nonempty v)) (-1000000)
    let S_vec := fun j => ((blocks.map (fun mat => fun i => mat i j)).map (fun v => ∑ i, Real.exp (v i - M_vec j))).sum
    -- Apply softmax to each block using the global M and S for each column.
    blocks.map (fun mat => fun i j => Real.exp (mat i j - M_vec j) / S_vec j)

/--
Computes softmax on a list of matrix blocks using the online algorithm.
-/
def online_softmax_output_2d {n m : ℕ} [NeZero n] (blocks : List (Mat n m)) : List (Mat n m) :=
  match blocks with
  | [] => []
  | _ =>
    let final_state := blocks.foldl update_online_state2D (initial_state2D n m)
    let M_vec := final_state.m_vals
    let S_vec := final_state.l_vals
    -- Apply softmax to each block using the final computed M and S.
    blocks.map (fun mat => fun i j => Real.exp (mat i j - M_vec j) / S_vec j)

/--
This theorem proves that the online softmax algorithm produces the exact same result as the
standard softmax algorithm when applied to a series of matrix blocks.
-/
theorem softmax_equivalence_2d {n m : ℕ} [NeZero n] (blocks : List (Mat n m)) :
  online_softmax_output_2d blocks = standard_softmax_on_blocks_2d blocks := by
  cases blocks with
  | nil => rfl
  | cons head tail =>
    -- Unfold definitions for the non-empty case.
    unfold online_softmax_output_2d standard_softmax_on_blocks_2d
    simp only [List.cons_ne_nil]

    -- The proof relies on showing that the computed M and S vectors are identical.
    let h_inv := process_blocks_invariant2D (head :: tail)
    -- The invariant tells us that for each column j, the 1D invariant holds.
    have h_inv_j : ∀ j, StateInvariant n { m := ((head :: tail).foldl update_online_state2D (initial_state2D n m)).m_vals j, l := ((head :: tail).foldl update_online_state2D (initial_state2D n m)).l_vals j, finished := true } (List.map (fun mat => fun i => mat i j) (head :: tail)) := by
      intro j
      let final_state := (head :: tail).foldl update_online_state2D (initial_state2D n m)
      have h_finished : final_state.finished = true := by
        -- We prove by induction that for any non-empty list `l`, the fold results in `finished = true`.
        suffices ∀ (l : List (Mat n m)) (s : OnlineState2D n m), l ≠ [] → (l.foldl update_online_state2D s).finished = true by
          apply this (head::tail) (initial_state2D n m); simp

        intro l
        induction l with
        | nil => intro s h; contradiction
        | cons hd tl ih =>
          intro s h_l
          rw [List.foldl_cons]
          if h : tl = [] then
            rw [h, List.foldl_nil]
            simp [update_online_state2D]
          else
            have ih_applied := ih (update_online_state2D s hd)
            apply ih_applied
            exact h
      -- The invariant from `process_blocks_invariant2D` gives us the property for `final_state`.
      -- We can use this and `h_finished` to prove the goal.
      exact h_finished ▸ h_inv.inv j
    -- Extract equality for M and S for each column from the 1D invariant.
    have h_m_eq : ∀ j, ((head :: tail).foldl update_online_state2D (initial_state2D n m)).m_vals j = ((head :: tail).map (fun mat => fun i => mat i j)).foldl (fun acc v => max acc (Finset.univ.sup' Finset.univ_nonempty v)) (-1000000) :=
      fun j => (h_inv_j j).max_correct
    have h_s_eq : ∀ j, ((head :: tail).foldl update_online_state2D (initial_state2D n m)).l_vals j = (((head :: tail).map (fun mat => fun i => mat i j)).map (fun v => ∑ i, Real.exp (v i - ((head :: tail).map (fun mat' => fun i' => mat' i' j)).foldl (fun acc v' => max acc (Finset.univ.sup' Finset.univ_nonempty v')) (-1000000)))).sum :=
      fun j => (h_inv_j j).sum_correct

    -- Rewrite with the equality of M and S vectors. This is sufficient to prove the goals are equal.
    congr 1
    ext mat i j
    rw [h_m_eq j, h_s_eq j]
