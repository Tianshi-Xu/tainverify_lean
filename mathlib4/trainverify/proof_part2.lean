import trainverify.proof_def
import trainverify.proof_part1
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Module.Basic
set_option autoImplicit false
namespace TrainVerify

open scoped Classical BigOperators

variable {β : Type*}

/-- Cast a vector of natural numbers to integers elementwise. -/
def vectorToInt {n : ℕ} (v : List.Vector ℕ n) : List.Vector ℤ n :=
  List.Vector.map (fun x : ℕ => (x : ℤ)) v

@[simp]
lemma vectorToInt_get {n : ℕ} (v : List.Vector ℕ n) (t : Fin n) :
    (vectorToInt v).get t = (v.get t : ℤ) := by
  simp [vectorToInt]

/-- The elementwise `ℕ` → `ℤ` cast is injective on vectors. -/
@[simp]
lemma vectorToInt_eq_iff {n : ℕ} {v w : List.Vector ℕ n} :
    vectorToInt v = vectorToInt w ↔ v = w := by
  constructor
  · intro h
    apply List.Vector.ext
    intro t
    have := congrArg (fun vec => vec.get t) h
    simpa [vectorToInt_get] using this
  · intro h; simp [h]

/-- Natural-number sums equalities transfer to integer differences. -/
lemma sub_eq_sub_of_nat_add_eq {a b c d : ℕ} (h : a + b = c + d) :
    (a : ℤ) - (c : ℤ) = (d : ℤ) - (b : ℤ) := by
  apply (sub_eq_sub_iff_add_eq_add).2
  have h' : (a : ℤ) + (b : ℤ) = (c : ℤ) + (d : ℤ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simpa [Int.cast_add] using this
  simpa [add_comm] using h'.trans (by simp [add_comm, add_left_comm])

/-- Lean rendition of Lemma 5.5.3 (cycle decomposition) from `for_proof.md`.
Any finite permutation breaks into a list of pairwise-disjoint cycles whose product recovers the
original permutation.  We reuse Mathlib’s packaged construction `truncCycleFactors`. -/
lemma theorem5_5_3_perm_cycle_decomposition {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    ∃ L : List (Equiv.Perm α),
      L.prod = σ ∧ (∀ τ ∈ L, τ.IsCycle) ∧ L.Pairwise Equiv.Perm.Disjoint := by
  classical
  obtain ⟨L, hstruct⟩ := σ.truncCycleFactors.out
  rcases hstruct with ⟨hprod, hcycle, hpair⟩
  refine ⟨L, ?_⟩
  exact ⟨hprod, hcycle, hpair⟩

/-! ## Lemma 5.5 scaffolding

This section formalises the overall structure of Lemma 5.5 in Lean.  Each
auxiliary statement (labelled A–D in the manuscript) is presented as an
independent lemma, and the concluding result `lemma55_permutation_equivalence`
references them exactly as outlined in `for_proof.md`.  Proofs of the auxiliary
lemmas are deferred (marked with `sorry`), but their statements match the prose
description and can be filled in later without changing the surrounding code. -/

section PermutationEquivalence

open Equiv

variable {β : Type*}

/-- A helper predicate stating that a permutation `P` sends the values of `B`
to a translate by a constant vector `C`. -/
def constantDifference {k : ℕ} [AddGroup β]
    (B : Fin k → β) (P : Equiv.Perm (Fin k)) (C : β) : Prop :=
  ∀ i : Fin k, B (P i) - B i = C

def hasLongCycle {k : ℕ} (P : Equiv.Perm (Fin k)) : Prop :=
  ∃ τ : Equiv.Perm (Fin k), τ.IsCycle ∧ τ ≠ (1 : Equiv.Perm (Fin k)) ∧
    τ.support ⊆ P.support ∧ ∀ x ∈ τ.support, P x = τ x

class NoZeroNatSmul (β : Type*) [AddCommMonoid β] : Prop where
  eq_zero_of_nsmul_eq_zero : ∀ {n : ℕ} {x : β}, 0 < n → n • x = (0 : β) → x = 0

instance instNoZeroNatSmul_int : NoZeroNatSmul ℤ := by
  refine ⟨?_⟩
  intro n x hn hx
  have hx' : ((n : ℤ) * x) = 0 := by
    simpa [nsmul_eq_mul] using hx
  have hnz : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hmul := mul_eq_zero.mp hx'
  rcases hmul with hmul | hmul
  · exact (hnz hmul).elim
  · simpa using hmul

instance instNoZeroNatSmul_pi {α : Type*} {β : Type*}
    [AddCommMonoid β] [NoZeroNatSmul β] : NoZeroNatSmul (α → β) := by
  refine ⟨?_⟩
  intro n f hn hf
  funext a
  have := congrArg (fun g => g a) hf
  have : n • f a = (0 : β) := by
    simpa [Pi.smul_apply] using this
  exact NoZeroNatSmul.eq_zero_of_nsmul_eq_zero (β:=β) hn this

variable {n k : ℕ}

/-- Lemma 5.5.A (conjugate permutation constant difference).  If the differences
`B (P₁⁻¹ (P₀ i)) - B i` are independent of the index, then the conjugate permutation
`P₁⁻¹ * P₀` shifts the entries of `B` by a constant vector. -/
lemma lemma5_5_A_conjugate_perm_const_diff {β : Type*} [AddCommGroup β]
    (B : Fin k → β) (P₀ P₁ : Equiv.Perm (Fin k))
    (hAlign : ∀ i j : Fin k,
      B (P₁.symm (P₀ i)) - B i = B (P₁.symm (P₀ j)) - B j) :
    ∃ C : β, constantDifference B (P₁.symm * P₀) C := by
  classical
  by_cases hk : k = 0
  · subst hk
    have hContr : ∀ i : Fin 0, False := by intro i; exact Fin.elim0 i
    refine ⟨0, ?_⟩
    intro i
    exact (hContr i).elim
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    -- Use the first index as the reference point.
    let i₀ : Fin (Nat.succ k') := ⟨0, Nat.succ_pos _⟩
    let C := B ((P₁.symm * P₀) i₀) - B i₀
    refine ⟨C, ?_⟩
    intro i
    have h := hAlign i i₀
    simpa [C, constantDifference, Equiv.Perm.mul_def] using h

/-- Lemma 5.5.B (non-trivial permutations force a non-zero difference). -/
lemma lemma5_5_B_nonzero_diff_of_neq_perm {β : Type*} [AddCommGroup β] [DecidableEq β] {k : ℕ}
    (B : Fin k → β) (P : Equiv.Perm (Fin k))
    (hDistinct : ∀ ⦃a b : Fin k⦄, a ≠ b → B a ≠ B b)
    (hP : P ≠ (1 : Equiv.Perm (Fin k)))
    {C : β} (hConst : constantDifference B P C) :
    C ≠ 0 := by
  classical
  intro hC
  have hZero : ∀ i : Fin k, B (P i) = B i := by
    intro i
    have h := hConst i
    have h' : B (P i) - B i = 0 := by simpa [hC] using h
    exact sub_eq_zero.mp h'
  have hInjective : Function.Injective B := by
    intro a b hEq
    by_contra hne
    exact (hDistinct hne) hEq
  have hPid : P = (1 : Equiv.Perm (Fin k)) := by
    ext i
    have hi : P i = i := hInjective (hZero i)
    simpa using congrArg Fin.val hi
  exact hP hPid

/-- Telescoping sum for successive differences of a sequence. -/
lemma telescoping_sum {β : Type*} [AddCommGroup β]
  (f : ℕ → β) (n : ℕ) :
  ∑ m ∈ Finset.range n, (f (m + 1) - f m) = f n - f 0 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      have hSplit :
          ∑ m ∈ Finset.range (n + 1), (f (m + 1) - f m)
            = (f (n + 1) - f n) + ∑ m ∈ Finset.range n, (f (m + 1) - f m) := by
        have hnot : n ∉ Finset.range n := Finset.not_mem_range_self
        have :=
          Finset.sum_insert (s := Finset.range n) (a := n)
            (f := fun m : ℕ => f (m + 1) - f m) hnot
        simpa [Finset.range_succ, add_comm] using this
      have := ih
      calc
        ∑ m ∈ Finset.range (n + 1), (f (m + 1) - f m)
            = (f (n + 1) - f n) + ∑ m ∈ Finset.range n, (f (m + 1) - f m) := hSplit
        _ = (f (n + 1) - f n) + (f n - f 0) := by simp [this]
        _ = f (n + 1) - f 0 := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Lemma 5.5.C (cycle summation collapses the constant difference to zero). -/
lemma lemma5_5_C_cycle_sum_is_zero {β : Type*} [AddCommGroup β] [DecidableEq β] [NoZeroNatSmul β]
    {k : ℕ} (B : Fin k → β) (P : Equiv.Perm (Fin k)) {C : β}
    (hConst : constantDifference (β:=β) B P C) (hCycle : hasLongCycle P) :
    C = 0 := by
  classical
  rcases hCycle with ⟨τ, hCycleτ, hτ_ne, _, hAgree⟩
  rcases hCycleτ with ⟨x, hx_ne, _⟩
  have hx_support : x ∈ τ.support := by
    simpa [Equiv.Perm.mem_support] using hx_ne
  have hx_ne : τ x ≠ x := by
    simpa [Equiv.Perm.mem_support] using hx_support
  -- Every iterate of `τ` keeps the base point inside the cycle support.
  have hOrbit : ∀ m : ℕ, (τ ^ m) x ∈ τ.support := by
    refine Nat.rec (motive := fun m => (τ ^ m) x ∈ τ.support) ?base ?step
    · simpa using hx_support
    · intro m _
      have hFix : τ ((τ ^ m) x) ≠ (τ ^ m) x := by
        intro hEqual
        have hPowEq : (τ ^ (m + 1)) x = (τ ^ m) x := by
          simpa [Nat.succ_eq_add_one, pow_succ', Equiv.Perm.mul_def] using hEqual
        have hPowEq' : (τ ^ m) (τ x) = (τ ^ m) x := by
          have hTmp : (τ ^ m * τ) x = (τ ^ m) x := by
            simpa [Nat.succ_eq_add_one, pow_succ, Equiv.Perm.mul_def] using hPowEq
          simpa [Equiv.Perm.mul_def] using hTmp
        exact hx_ne ((τ ^ m).injective hPowEq')
      simpa [Nat.succ_eq_add_one, pow_succ', Equiv.Perm.mul_def] using
        Equiv.Perm.mem_support.mpr hFix
  -- Apply the constant-difference hypothesis along the cycle.
  have hConstCycle : ∀ m : ℕ,
      B ((τ ^ (m + 1)) x) - B ((τ ^ m) x) = C := by
    intro m
    have hMem : (τ ^ m) x ∈ τ.support := hOrbit m
    have hP_eq : P ((τ ^ m) x) = τ ((τ ^ m) x) := hAgree _ hMem
    have := hConst ((τ ^ m) x)
    simpa [Nat.succ_eq_add_one, pow_succ', Equiv.Perm.mul_def, hP_eq] using this
  -- Summing over one full cycle multiplies the constant by the cycle length.
  let N : ℕ := orderOf τ
  have hSumConst :
      ∑ m ∈ Finset.range N,
        (B ((τ ^ (m + 1)) x) - B ((τ ^ m) x)) = N • C := by
    classical
    have hSumEq :
        ∑ m ∈ Finset.range N,
          (B ((τ ^ (m + 1)) x) - B ((τ ^ m) x)) =
            ∑ _ ∈ Finset.range N, C := by
      refine Finset.sum_congr rfl ?_
      intro m _
      simpa [Nat.succ_eq_add_one] using hConstCycle m
    have hConstSumRange : ∑ _ ∈ Finset.range N, C = N • C := by
      have h := Finset.sum_const (s := Finset.range N) C
      have hCard : (Finset.range N).card = N := Finset.card_range N
      have hCard' : (Finset.range N).card • C = N • C := by simp [hCard, N]
      exact h.trans hCard'
    exact hSumEq.trans hConstSumRange
  -- The same sum telescopes, giving the net change along the orbit.
  have hTelescoping :=
    telescoping_sum (fun m => B ((τ ^ m) x)) N
  have hPow_eq : (τ ^ N) x = x := by
    have hPowOne : τ ^ N = (1 : Equiv.Perm (Fin k)) := by
      simpa [N] using pow_orderOf_eq_one τ
    simpa [N] using congrArg (fun σ : Equiv.Perm (Fin k) => σ x) hPowOne
  have hScalar : N • C = 0 := by
    have hEq : N • C = B ((τ ^ N) x) - B x :=
      (hTelescoping.symm.trans hSumConst).symm
    simpa [hPow_eq, N] using hEq
  exact NoZeroNatSmul.eq_zero_of_nsmul_eq_zero (β:=β) (orderOf_pos _) hScalar

/-- Lemma 5.5.D (every non-trivial permutation has a long cycle). -/
lemma lemma5_5_D_nontrivial_perm_has_long_cycle {k : ℕ} (P : Equiv.Perm (Fin k))
    (hP : P ≠ (1 : Equiv.Perm (Fin k))) :
    hasLongCycle P := by
  classical
  have hSupp_ne : P.support ≠ (∅ : Finset (Fin k)) := by
    intro hEmpty
    have : P = (1 : Equiv.Perm (Fin k)) := by
      simpa [Equiv.Perm.support_eq_empty_iff] using hEmpty
    exact hP this
  obtain ⟨x, hx⟩ := (Finset.nonempty_iff_ne_empty).2 hSupp_ne
  have hx_ne : P x ≠ x := by
    simpa [Equiv.Perm.mem_support] using hx
  let τ := P.cycleOf x
  have hCycle : τ.IsCycle := by
    simpa [τ] using (Equiv.Perm.isCycle_cycleOf (f := P) (x := x) hx_ne)
  have hτ_ne : τ ≠ (1 : Equiv.Perm (Fin k)) := by
    intro hτ
    have : P x = x := by
      simpa [τ] using
        (Equiv.Perm.cycleOf_eq_one_iff (f := P) (x := x)).1 hτ
    exact hx_ne this
  have hSubset : τ.support ⊆ P.support := by
    simpa [τ] using (Equiv.Perm.support_cycleOf_le (f := P) (x := x))
  refine ⟨τ, hCycle, hτ_ne, hSubset, ?_⟩
  intro y hy
  obtain ⟨hSame, _⟩ :=
    (Equiv.Perm.mem_support_cycleOf_iff (f := P) (x := x)).1
      (by simpa [τ] using hy)
  have hEval : P y = τ y := by
    simpa [τ] using
      ((Equiv.Perm.SameCycle.cycleOf_apply (f := P) (x := x) (y := y)) hSame).symm
  exact hEval

/-- Data required to state Lemma 5.5.  It records the family of permutations
`P` and the base vector `B` whose entries are pairwise distinct.  The
`alignment` hypothesis reflects the algebraic equalities obtained from the
affine dependency mappings in the manuscript. -/
structure lemma5_5_PermutationEquivalenceContext (β : Type*) [AddGroup β]
    [DecidableEq β] (n k : ℕ) where
  P : Fin (n + 1) → Equiv.Perm (Fin k)
  base : Fin k → β
  alignment :
    ∀ j : Fin n, ∀ i i' : Fin k,
      base ((P (Fin.succ j)).symm (P 0 i)) - base i =
      base ((P (Fin.succ j)).symm (P 0 i')) - base i'
  distinct : ∀ ⦃a b : Fin k⦄, a ≠ b → base a ≠ base b

/-- If the product `σ⁻¹ * τ` is the identity permutation, then `σ = τ`. -/
lemma perm_eq_of_symm_mul_eq_one {α : Type*}
    {σ τ : Equiv.Perm α} (h : σ.symm * τ = (1 : Equiv.Perm α)) :
    τ = σ := by
  have h' := congrArg (fun π => σ * π) h
  have : σ * (σ.symm * τ) = σ := by
    simpa [mul_assoc] using h'
  have hMul_assoc : σ * (σ.symm * τ) = (σ * σ.symm) * τ := by
    ext x
    simp [Equiv.Perm.mul_def, mul_assoc]
  have hId : (σ * σ.symm) = (1 : Equiv.Perm α) := by
    ext x; simp [Equiv.Perm.mul_def]
  have hFinal : (1 : Equiv.Perm α) * τ = σ := by
    simpa [hMul_assoc, hId]
  simpa using hFinal

/-- Lemma 5.5 (permutation equivalence).  Under the hypotheses of
`PermutationEquivalenceContext`, all permutations `P_j` coincide. -/
lemma lemma5_5_permutation_equivalence {β : Type*} [AddCommGroup β] [DecidableEq β]
    [NoZeroNatSmul β]
    {n k : ℕ} (ctx : lemma5_5_PermutationEquivalenceContext β n k) :
    ∀ j : Fin (n + 1), ctx.P j = ctx.P 0 := by
  classical
  intro j
  cases' j using Fin.cases with j
  · simp
  · obtain ⟨C, hConst⟩ :=
      lemma5_5_A_conjugate_perm_const_diff ctx.base (ctx.P 0) (ctx.P (Fin.succ j)) (ctx.alignment j)
    have : ctx.P (Fin.succ j) = ctx.P 0 := by
      by_contra hneq
      set Pconj := (ctx.P (Fin.succ j)).symm * ctx.P 0 with hPconjDef
      have hConst' : constantDifference ctx.base Pconj C := by
        simpa [Pconj, hPconjDef] using hConst
      have hPconj_ne : Pconj ≠ (1 : Equiv.Perm (Fin k)) := by
        intro h
        have hEq :=
          perm_eq_of_symm_mul_eq_one
            (σ := ctx.P (Fin.succ j)) (τ := ctx.P 0)
            (by simpa [Pconj, hPconjDef] using h)
        exact hneq hEq.symm
      have hC_ne : C ≠ 0 :=
        lemma5_5_B_nonzero_diff_of_neq_perm ctx.base Pconj ctx.distinct hPconj_ne hConst'
      have hLong : hasLongCycle Pconj :=
        lemma5_5_D_nontrivial_perm_has_long_cycle Pconj hPconj_ne
      have hC_zero : C = 0 :=
        lemma5_5_C_cycle_sum_is_zero ctx.base Pconj hConst' hLong
      exact (hC_ne hC_zero).elim
    simpa using this

end PermutationEquivalence

