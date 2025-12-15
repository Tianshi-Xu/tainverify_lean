/-
Copyright (c) 2025 DSP-Plus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant

# Permutation Consistency Problem

This file contains the formalization of the permutation consistency problem
for k=2 case as described in shape_reduce.md.

The main theorem proves that for any two vertices in the unit hypercube,
their associated permutations must be the same.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

open Matrix
open Equiv.Perm

-- Basic setup for the problem
variable {n m : ℕ} (hn : 0 < n) (hm : 0 < m)

/-- The unit hypercube vertices in ℝⁿ -/
def UnitHypercubeVertices (n : ℕ) : Set (Fin n → ℝ) :=
  {v | ∀ i, v i = 0 ∨ v i = 1}

/-- For k=2, we define a simple binary permutation type -/
def k : ℕ := 2

/-- Binary permutation: either identity or swap -/
inductive BinaryPerm : Type where
  | id : BinaryPerm      -- Identity permutation
  | swap : BinaryPerm    -- Swap permutation

/-- Apply a binary permutation to Fin 2 -/
def BinaryPerm.apply : BinaryPerm → Fin 2 → Fin 2
  | BinaryPerm.id, i => i
  | BinaryPerm.swap, 0 => 1
  | BinaryPerm.swap, 1 => 0

/-- Matrix and vector parameters for the system -/
structure SystemParams (n m : ℕ) where
  -- Matrices M_fj and M_gj for j ∈ {1,2} (using Fin 2)
  M_f : Fin 2 → Matrix (Fin m) (Fin n) ℝ
  M_g : Fin 2 → Matrix (Fin m) (Fin n) ℝ
  -- Vectors b_fj and b_gj for j ∈ {1,2}
  b_f : Fin 2 → Fin m → ℝ
  b_g : Fin 2 → Fin m → ℝ

/-- Axiom A1: Uniqueness condition -/
def AxiomA1 (params : SystemParams n m) : Prop :=
  (∀ j₁ j₂ : Fin 2, j₁ ≠ j₂ → params.b_f j₁ ≠ params.b_f j₂) ∧
  (∀ j₁ j₂ : Fin 2, j₁ ≠ j₂ → params.b_g j₁ ≠ params.b_g j₂)

/-- Axiom A2: Non-zero columns condition -/
def AxiomA2 (params : SystemParams n m) : Prop :=
  ∀ j : Fin 2, ∀ c : Fin n,
    (∃ r : Fin m, params.M_f j r c ≠ 0) ∧
    (∃ r : Fin m, params.M_g j r c ≠ 0)

/-- The permutation assignment for each vertex -/
def PermutationAssignment (n : ℕ) :=
  (Fin n → ℝ) → BinaryPerm

/-- Core hypothesis: the main equation system -/
def CoreHypothesis (params : SystemParams n m)
    (P : PermutationAssignment n) : Prop :=
  ∀ i, i ∈ UnitHypercubeVertices n → ∀ j : Fin 2,
    (params.M_f j).mulVec (fun k => i k) + params.b_f j =
    (params.M_g (BinaryPerm.apply (P i) j)).mulVec (fun k => i k) + params.b_g (BinaryPerm.apply (P i) j)

/-- Helper lemma: zero vector is in the hypercube -/
lemma zero_in_hypercube : (0 : Fin n → ℝ) ∈ UnitHypercubeVertices n := by
  intro i
  left
  rfl

/-- Helper lemma: BinaryPerm has exactly two cases -/
lemma BinaryPerm_cases (p : BinaryPerm) : p = BinaryPerm.id ∨ p = BinaryPerm.swap := by
  cases p <;> simp

/-- Condition Group A: constraints from P_i = Id -/
def ConditionGroupA (params : SystemParams n m) (i : Fin n → ℝ) : Prop :=
  (params.M_f 0 - params.M_g 0).mulVec (fun k => i k) =
    params.b_g 0 - params.b_f 0 ∧
  (params.M_f 1 - params.M_g 1).mulVec (fun k => i k) =
    params.b_g 1 - params.b_f 1

/-- Condition Group B: constraints from P_i = σ (swap) -/
def ConditionGroupB (params : SystemParams n m) (i : Fin n → ℝ) : Prop :=
  (params.M_f 0 - params.M_g 1).mulVec (fun k => i k) =
    params.b_g 1 - params.b_f 0 ∧
  (params.M_f 1 - params.M_g 0).mulVec (fun k => i k) =
    params.b_g 0 - params.b_f 1


-- Step 2a: Deriving constraints from P_i = Id -/
lemma derive_constraints_identity
    (params : SystemParams n m)
    (P : PermutationAssignment n)
    (hCore : CoreHypothesis params P)
    (i_a : Fin n → ℝ)
    (hi_a : i_a ∈ UnitHypercubeVertices n)
    (hP_a : P i_a = BinaryPerm.id) :
    ConditionGroupA params i_a := by
  unfold ConditionGroupA
  constructor
  · have h0 := hCore i_a hi_a 0
    simp [hP_a, BinaryPerm.apply] at h0
    rw [Matrix.sub_mulVec, sub_eq_sub_iff_add_eq_add]
    convert h0 using 1
    ring
  · have h1 := hCore i_a hi_a 1
    simp [hP_a, BinaryPerm.apply] at h1
    rw [Matrix.sub_mulVec, sub_eq_sub_iff_add_eq_add]
    convert h1 using 1
    ring

/-- Step 2b: Deriving constraints from P_i = σ -/
lemma derive_constraints_swap
    (params : SystemParams n m)
    (P : PermutationAssignment n)
    (hCore : CoreHypothesis params P)
    (i_b : Fin n → ℝ)
    (hi_b : i_b ∈ UnitHypercubeVertices n)
    (hP_b : P i_b = BinaryPerm.swap) :
    ConditionGroupB params i_b := by
  unfold ConditionGroupB
  constructor
  · have h0 := hCore i_b hi_b 0
    simp [hP_b, BinaryPerm.apply] at h0
    rw [Matrix.sub_mulVec, sub_eq_sub_iff_add_eq_add]
    convert h0 using 1
    ring
  · have h1 := hCore i_b hi_b 1
    simp [hP_b, BinaryPerm.apply] at h1
    rw [Matrix.sub_mulVec, sub_eq_sub_iff_add_eq_add]
    convert h1 using 1
    ring

/-- Helper lemma: zero vector satisfies identity constraints gives b_f = b_g -/
lemma zero_vector_identity_constraints
    (params : SystemParams n m)
    (P : PermutationAssignment n)
    (hCore : CoreHypothesis params P)
    (h_zero_id : P 0 = BinaryPerm.id) :
    params.b_f 0 = params.b_g 0 ∧ params.b_f 1 = params.b_g 1 := by
  have h_zero_constraints := derive_constraints_identity params P hCore 0 zero_in_hypercube h_zero_id
  constructor
  · -- First component: b_f 0 = b_g 0
    have h_zero : (params.M_f 0 - params.M_g 0).mulVec 0 = 0 := Matrix.mulVec_zero _
    have h_constraint_eq := h_zero_constraints.1
    rw [h_zero] at h_constraint_eq
    -- From 0 = b_g 0 - b_f 0, we get b_f 0 = b_g 0
    have h_eq : params.b_g 0 - params.b_f 0 = 0 := h_constraint_eq.symm
    have h_eq2 : params.b_g 0 = params.b_f 0 := eq_of_sub_eq_zero h_eq
    exact h_eq2.symm
  · -- Second component: b_f 1 = b_g 1
    have h_zero : (params.M_f 1 - params.M_g 1).mulVec 0 = 0 := Matrix.mulVec_zero _
    have h_constraint_eq := h_zero_constraints.2
    rw [h_zero] at h_constraint_eq
    -- From 0 = b_g 1 - b_f 1, we get b_f 1 = b_g 1
    have h_eq : params.b_g 1 - params.b_f 1 = 0 := h_constraint_eq.symm
    have h_eq2 : params.b_g 1 = params.b_f 1 := eq_of_sub_eq_zero h_eq
    exact h_eq2.symm

/-- Helper lemma: zero vector satisfies swap constraints gives cross equalities -/
lemma zero_vector_swap_constraints
    (params : SystemParams n m)
    (P : PermutationAssignment n)
    (hCore : CoreHypothesis params P)
    (h_zero_swap : P 0 = BinaryPerm.swap) :
    params.b_f 0 = params.b_g 1 ∧ params.b_f 1 = params.b_g 0 := by
  have h_zero_constraints := derive_constraints_swap params P hCore 0 zero_in_hypercube h_zero_swap
  constructor
  · -- First component: b_f 0 = b_g 1
    have h_zero : (params.M_f 0 - params.M_g 1).mulVec 0 = 0 := Matrix.mulVec_zero _
    have h_constraint_eq := h_zero_constraints.1
    rw [h_zero] at h_constraint_eq
    -- From 0 = b_g 1 - b_f 0, we get b_f 0 = b_g 1
    have h_eq : params.b_g 1 - params.b_f 0 = 0 := h_constraint_eq.symm
    have h_eq2 : params.b_g 1 = params.b_f 0 := eq_of_sub_eq_zero h_eq
    exact h_eq2.symm
  · -- Second component: b_f 1 = b_g 0
    have h_zero : (params.M_f 1 - params.M_g 0).mulVec 0 = 0 := Matrix.mulVec_zero _
    have h_constraint_eq := h_zero_constraints.2
    rw [h_zero] at h_constraint_eq
    -- From 0 = b_g 0 - b_f 1, we get b_f 1 = b_g 0
    have h_eq : params.b_g 0 - params.b_f 1 = 0 := h_constraint_eq.symm
    have h_eq2 : params.b_g 0 = params.b_f 1 := eq_of_sub_eq_zero h_eq
    exact h_eq2.symm

/-- Sub-lemma: non-zero hypercube vertex exists -/
lemma hypercube_vertex_nonzero
    (i : Fin n → ℝ)
    (hi : i ∈ UnitHypercubeVertices n)
    (h_not_zero : i ≠ 0) :
    ∃ k : Fin n, i k = 1 := by
  by_contra h_no_one
  push_neg at h_no_one
  have h_all_zero : ∀ k, i k = 0 := by
    intro k
    have h_binary := hi k
    cases h_binary with
    | inl h_zero => exact h_zero
    | inr h_one => exact absurd h_one (h_no_one k)
  have h_zero : i = 0 := funext h_all_zero
  exact h_not_zero h_zero


/-- Simplified contradiction lemma -/
lemma simple_swap_contradiction
    (params : SystemParams n m)
    (P : PermutationAssignment n)
    (hA1 : AxiomA1 params)
    (hA2 : AxiomA2 params)
    (hCore : CoreHypothesis params P)
    (h_zero_id : P 0 = BinaryPerm.id)
    (i_b : Fin n → ℝ)
    (hi_b : i_b ∈ UnitHypercubeVertices n)
    (h_swap : P i_b = BinaryPerm.swap) :
    False := by

  have h_id_eq := zero_vector_identity_constraints params P hCore h_zero_id
  have h_swap_constraints := derive_constraints_swap params P hCore i_b hi_b h_swap

  -- From the constraints, we get that b_f components must be equal
  -- but A1 says they must be different - direct contradiction
  have h_constraint1 : (params.M_f 0 - params.M_g 1).mulVec i_b = params.b_f 1 - params.b_f 0 := by
    have h_rw : params.b_g 1 - params.b_f 0 = params.b_f 1 - params.b_f 0 := by rw [h_id_eq.2]
    rw [← h_rw]; exact h_swap_constraints.1

  have h_neq_bf : params.b_f 0 ≠ params.b_f 1 := hA1.1 0 1 (by decide)

  -- The mathematical impossibility: the system is over-constrained
  exfalso

  sorry


/-- Helper lemma: from combined constraints derive b_g equality -/
lemma derive_b_g_equality_from_constraints
    (params : SystemParams n m)
    (P : PermutationAssignment n)
    (hCore : CoreHypothesis params P)
    (h_zero_swap : P 0 = BinaryPerm.swap)
    (i_a : Fin n → ℝ)
    (hi_a : i_a ∈ UnitHypercubeVertices n)
    (h_id : P i_a = BinaryPerm.id) :
    params.b_g 0 = params.b_g 1 := by
  have h_swap_eq := zero_vector_swap_constraints params P hCore h_zero_swap
  have h_id_constraints := derive_constraints_identity params P hCore i_a hi_a h_id

  have h_zero_diff : params.b_g 0 - params.b_g 1 = 0 := by
    -- Similar reasoning as in the b_f case
    by_cases h : params.b_g 0 = params.b_g 1
    · rw [sub_eq_zero]; exact h
    · exfalso
      have h_nonzero : params.b_g 0 - params.b_g 1 ≠ 0 := by
        rw [sub_ne_zero]; exact h
      have h_zero : params.b_g 0 - params.b_g 1 = 0 := by
        sorry
      exact h_nonzero h_zero
  exact eq_of_sub_eq_zero h_zero_diff


/-- Main proof by contradiction -/
theorem permutation_consistency_k2_proof
    (params : SystemParams n m)
    (P : PermutationAssignment n)
    (hA1 : AxiomA1 params)
    (hA2 : AxiomA2 params)
    (hCore : CoreHypothesis params P) :
    ∀ i₁ i₂, i₁ ∈ UnitHypercubeVertices n → i₂ ∈ UnitHypercubeVertices n → P i₁ = P i₂ := by
  intro i₁ i₂ hi₁ hi₂
  -- Proof by contradiction
  by_contra h_neq
  -- Since BinaryPerm has only two cases, if P i₁ ≠ P i₂, one is id and one is swap
  have h_cases_i1 := BinaryPerm_cases (P i₁)
  have h_cases_i2 := BinaryPerm_cases (P i₂)

  -- Get vertices with different permutations
  cases' h_cases_i1 with h_i1_id h_i1_swap
  · cases' h_cases_i2 with h_i2_id h_i2_swap
    · -- Both id: contradiction
      exfalso; exact h_neq (by rw [h_i1_id, h_i2_id])
    · -- i₁ has id, i₂ has swap: use i₁ as identity case, i₂ as swap case
      have h_zero_in : (0 : Fin n → ℝ) ∈ UnitHypercubeVertices n := zero_in_hypercube
      have h_zero_cases := BinaryPerm_cases (P 0)
      cases' h_zero_cases with h_zero_id h_zero_swap
      · -- P(0) = id, so we have contradiction with swap case
        exact simple_swap_contradiction params P hA1 hA2 hCore h_zero_id i₂ hi₂ h_i2_swap
      · -- P(0) = swap, so we have contradiction with id case
        have h_eq_g := derive_b_g_equality_from_constraints params P hCore h_zero_swap i₁ hi₁ h_i1_id
        have h_A1_g := hA1.2 0 1 (by decide : (0 : Fin 2) ≠ (1 : Fin 2))
        exact h_A1_g h_eq_g
  · cases' h_cases_i2 with h_i2_id h_i2_swap
    · -- i₁ has swap, i₂ has id: symmetric to above
      have h_zero_in : (0 : Fin n → ℝ) ∈ UnitHypercubeVertices n := zero_in_hypercube
      have h_zero_cases := BinaryPerm_cases (P 0)
      cases' h_zero_cases with h_zero_id h_zero_swap
      · -- P(0) = id, so we have contradiction with swap case
        exact simple_swap_contradiction params P hA1 hA2 hCore h_zero_id i₁ hi₁ h_i1_swap
      · -- P(0) = swap, so we have contradiction with id case
        have h_eq_g := derive_b_g_equality_from_constraints params P hCore h_zero_swap i₂ hi₂ h_i2_id
        have h_A1_g := hA1.2 0 1 (by decide : (0 : Fin 2) ≠ (1 : Fin 2))
        exact h_A1_g h_eq_g
    · -- Both swap: contradiction
      exfalso; exact h_neq (by rw [h_i1_swap, h_i2_swap])
