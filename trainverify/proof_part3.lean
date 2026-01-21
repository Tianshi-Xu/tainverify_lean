import trainverify.proof_def
import trainverify.proof_part1
import trainverify.proof_part2
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace TrainVerify

open Classical

open Matrix

private def zeroIndex (n : ℕ) : Fin (n + 1) := ⟨0, Nat.succ_pos _⟩

@[simp] lemma basisVector_zero_get {n : ℕ} (t : Fin n) :
    (basisVector n (zeroIndex n)).get t = 0 := by
  simp [basisVector, zeroIndex]

lemma basisVector_zero_function {n : ℕ} :
    (fun s : Fin n => (basisVector n (zeroIndex n)).get s) = fun _ : Fin n => (0 : ℕ) := by
  funext s; simp [basisVector_zero_get]

lemma basisVector_succ_get {n : ℕ} (j : Fin n) (t : Fin n) :
    (basisVector n (Fin.succ j)).get t = (if t = j then 1 else 0) := by
  have hj : (Fin.succ j).val ≠ 0 := by exact Nat.succ_ne_zero _
  have hval : (Fin.succ j).val = j.val + 1 := rfl
  classical
  have hi : (basisVector n (Fin.succ j)).get t =
      if t.val = j.val then (1 : ℕ) else 0 := by
    simp [basisVector, zeroIndex, hj, hval, Nat.succ_eq_add_one]
  by_cases ht : t = j
  · subst ht
    simp [hi]
  · have hvalNe : t.val ≠ j.val := by
      intro h
      exact ht (Fin.ext h)
    have hsuccNe : t.val.succ ≠ j.val.succ := by
      intro hEq
      exact hvalNe (Nat.succ.inj hEq)
    simp [basisVector, List.Vector.get_ofFn, Fin.succ, Nat.succ_eq_add_one,
      ht, hvalNe, hsuccNe]

lemma basisVector_succ_function {n : ℕ} (j : Fin n) :
    (fun s : Fin n => (basisVector n (Fin.succ j)).get s) = Pi.single j (1 : ℕ) := by
  classical
  funext s
  by_cases h : s = j
  · subst h
    simp [basisVector_succ_get]
  · simp [basisVector_succ_get, h]

lemma matrix_mulVec_basisVector {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℕ) (j : Fin n) :
    Matrix.mulVec M (fun s : Fin n => (basisVector n (Fin.succ j)).get s) =
      fun t : Fin m => M t j := by
  classical
  have h := Matrix.mulVec_single_one (M := M) j
  have hTranspose : (Mᵀ j) = fun t : Fin m => M t j := by
    funext t
    simp [Matrix.transpose_apply]
  convert h using 1; simp [basisVector_succ_function, hTranspose]

lemma matrix_mulVec_zeroVector {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℕ) :
    Matrix.mulVec M (fun _ : Fin n => (0 : ℕ)) = fun _ : Fin m => (0 : ℕ) := by
  classical
  funext t
  unfold Matrix.mulVec
  simp

lemma basisVector_mem_vertexIndexSet (n : ℕ) (i : Fin (n + 1)) :
    basisVector n i ∈ def4_1_VertexIndexSet n := by
  change ∀ j : Fin n, (basisVector n i).get j = 0 ∨ (basisVector n i).get j = 1
  intro j
  by_cases h0 : i.val = 0
  · have : (basisVector n i).get j = 0 := by
      simp [basisVector, h0]
    exact Or.inl this
  · by_cases h1 : j.val + 1 = i.val
    · have : (basisVector n i).get j = 1 := by
        simp [basisVector, h0, h1]
      exact Or.inr this
    · have : (basisVector n i).get j = 0 := by
        simp [basisVector, h0, h1]
      exact Or.inl this

lemma noRepeatedIndices_castLength {n m k₁ k₂ : ℕ}
    (h : k₁ = k₂) (τ : def2_2_DependencyMapping n m k₁)
    (hDistinct : def3_5_NoRepeatedIndices τ) :
    def3_5_NoRepeatedIndices (def2_2_DependencyMapping.castLength h τ) := by
  intro i a b hneq
  have hneq' : Fin.cast h.symm a ≠ Fin.cast h.symm b := by
    intro hEq
    have hEq' : a = b := by
      simpa [Fin.cast_cast_symm] using congrArg (Fin.cast h) hEq
    exact hneq hEq'
  have hDistinct' :=
    hDistinct i (Fin.cast h.symm a) (Fin.cast h.symm b) hneq'
  simpa [dependency_cast_get] using hDistinct'

section AffineHelpers

variable {n m k : ℕ}

lemma affine_offsets_at_zero (aff : def2_4_AffineDependencyMapping n m k)
    (j : Fin k) (t : Fin m) :
    ((aff.toMapping (basisVector n (zeroIndex n))).get j).get t =
      (aff.offsets.get j).get t := by
  classical
  have h := aff.affine (basisVector n (zeroIndex n)) j t
  have hfun :
      (fun s : Fin n => (basisVector n (zeroIndex n)).get s) =
        fun _ : Fin n => (0 : ℕ) := basisVector_zero_function
  simpa [hfun, matrix_mulVec_zeroVector] using h

lemma affine_offsets_at_basisVector_succ
    (aff : def2_4_AffineDependencyMapping n m k)
    (r : Fin n) (j : Fin k) (t : Fin m) :
    ((aff.toMapping (basisVector n (Fin.succ r))).get j).get t =
      aff.M t r + (aff.offsets.get j).get t := by
  classical
  have h := aff.affine (basisVector n (Fin.succ r)) j t
  simpa [matrix_mulVec_basisVector] using h

def indexToInt (i : Index m) : Fin m → ℤ := fun t => (i.get t : ℤ)

@[simp] lemma indexToInt_apply (i : Index m) (t : Fin m) :
    indexToInt i t = (i.get t : ℤ) := rfl

lemma indexToInt_injective : Function.Injective (indexToInt : Index m → Fin m → ℤ) := by
  intro v w h
  refine List.Vector.ext ?_
  intro t
  have h' := congrArg (fun f : Fin m → ℤ => f t) h
  have h'' : Int.ofNat (v.get t) = Int.ofNat (w.get t) := by simpa using h'
  exact Int.ofNat.inj h''

lemma indexToInt_ne {i j : Index m} (hne : i ≠ j) : indexToInt i ≠ indexToInt j := by
  intro hEq; exact hne (indexToInt_injective hEq)

lemma dependency_indexToInt_injective
    {τ : def2_2_DependencyMapping n m k}
    (hDistinct : def3_5_NoRepeatedIndices τ) (i : Index n) :
    Function.Injective (fun a : Fin k => indexToInt ((τ i).get a)) := by
  intro a b hEq
  classical
  by_contra hne
  have hIdx : (τ i).get a = (τ i).get b :=
    indexToInt_injective hEq
  exact (hDistinct i a b hne) hIdx

end AffineHelpers

section MappingPermutation

variable {input_dims output_dims : List ℕ}

lemma lemma5_4_vertexPermutations
    (f g : def2_3_SIMDFunction input_dims output_dims)
    (hWellF : def3_4_WellFormedKernel f.kernel)
    (hWellG : def3_4_WellFormedKernel g.kernel)
    (hDistinctF : def3_5_NoRepeatedIndices f.dependency)
    (hDistinctG : def3_5_NoRepeatedIndices g.dependency)
    (hK : f.k = g.k)
    (hPremise : def4_1_SMTPremise input_dims output_dims
      (applySIMD input_dims output_dims f)
      (applySIMD input_dims output_dims g)) :
    ∀ j : Fin (output_dims.length + 1),
      ∃! P : Equiv.Perm (Fin g.k),
        List.Vector.ofFn (fun a =>
          (def2_2_DependencyMapping.castLength hK f.dependency
            (basisVector output_dims.length j)).get (P a)) =
          g.dependency (basisVector output_dims.length j) := by
  classical
  intro j
  have hEqVertex : ∀ x : def1_1_Tensor input_dims,
      applySIMD input_dims output_dims f x (basisVector output_dims.length j) =
        applySIMD input_dims output_dims g x (basisVector output_dims.length j) := by
    intro x
    exact hPremise x (basisVector output_dims.length j)
      (basisVector_mem_vertexIndexSet _ j)
  simpa using
    theorem5_2_dependencyPermutation_unique f g hWellF hWellG
      hDistinctF hDistinctG hK (basisVector output_dims.length j) hEqVertex

lemma lemma5_4_affine_alignment
    {n m k : ℕ}
    (affF affG : def2_4_AffineDependencyMapping n m k)
    (P : Fin (n + 1) → Equiv.Perm (Fin k))
    (hZero : ∀ i : Fin k,
      (affF.toMapping (basisVector n (zeroIndex n))).get (P (zeroIndex n) i) =
        (affG.toMapping (basisVector n (zeroIndex n))).get i)
    (hSucc : ∀ j : Fin n, ∀ i : Fin k,
      (affF.toMapping (basisVector n (Fin.succ j))).get (P (Fin.succ j) i) =
        (affG.toMapping (basisVector n (Fin.succ j))).get i) :
    (∀ i : Fin k,
      affF.offsets.get (P (zeroIndex n) i) = affG.offsets.get i) ∧
    (∀ j : Fin n, ∀ i : Fin k, ∀ t : Fin m,
      indexToInt ((affG.toMapping (basisVector n (zeroIndex n))).get
        ((P (Fin.succ j)).symm (P (zeroIndex n) i))) t -
        indexToInt ((affG.toMapping (basisVector n (zeroIndex n))).get i) t =
        (affF.M t j : ℤ) - (affG.M t j : ℤ)) := by
  classical
  set base := fun a : Fin k =>
    indexToInt ((affG.toMapping (basisVector n (zeroIndex n))).get a) with hBase
  set delta := fun j : Fin n => fun t : Fin m =>
    (affF.M t j : ℤ) - (affG.M t j : ℤ) with hDelta
  let P₀ : Equiv.Perm (Fin k) := P (zeroIndex n)
  -- Offsets coincide at the zero vertex.
  have hOffsets_eq : ∀ i : Fin k,
      affF.offsets.get (P₀ i) = affG.offsets.get i := by
    intro i
    apply List.Vector.ext
    intro t
    have hEq := congrArg (fun idx : Index m => idx.get t) (hZero i)
    have hF := affine_offsets_at_zero (aff := affF) (j := P₀ i) (t := t)
    have hG := affine_offsets_at_zero (aff := affG) (j := i) (t := t)
    have hEq' := hEq
    simp [P₀, base, hBase, hF, hG] at hEq'
    simpa using hEq'
  -- Constant differences along successor vertices.
  have hAlign : ∀ j : Fin n, ∀ i : Fin k, ∀ t : Fin m,
      base ((P (Fin.succ j)).symm (P₀ i)) t - base i t = delta j t := by
    intro j i t
    -- Expand affine dependencies at the successor vertex.
    have hSuccEq := congrArg (fun idx : Index m => idx.get t)
      (hSucc j ((P (Fin.succ j)).symm (P₀ i)))
    have hF := affine_offsets_at_basisVector_succ (aff := affF)
      (r := j) (j := P₀ i) (t := t)
    have hG := affine_offsets_at_basisVector_succ (aff := affG)
      (r := j) (j := (P (Fin.succ j)).symm (P₀ i)) (t := t)
    have hNat : affF.M t j + (affF.offsets.get (P₀ i)).get t =
        affG.M t j + (affG.offsets.get ((P (Fin.succ j)).symm (P₀ i))).get t := by
      have hPerm : P (Fin.succ j) ((P (Fin.succ j)).symm (P₀ i)) = P₀ i :=
        (P (Fin.succ j)).apply_symm_apply (P₀ i)
      have hSuccEq' :
          ((affF.toMapping (basisVector n (Fin.succ j))).get (P₀ i)).get t =
            ((affG.toMapping (basisVector n (Fin.succ j))).get
              ((P (Fin.succ j)).symm (P₀ i))).get t := by
        simpa [hPerm]
          using hSuccEq
      simpa [hF, hG] using hSuccEq'
    have hOffsets_int :
        ((affF.offsets.get (P₀ i)).get t : ℤ) =
          ((affG.offsets.get i).get t : ℤ) := by
      have := congrArg (fun idx : Index m => (idx.get t : ℤ)) (hOffsets_eq i)
      simpa [P₀]
        using this
    have hDiff :
        ((affG.offsets.get ((P (Fin.succ j)).symm (P₀ i))).get t : ℤ) -
          ((affG.offsets.get i).get t : ℤ) =
          (affF.M t j : ℤ) - (affG.M t j : ℤ) := by
      have h := sub_eq_sub_of_nat_add_eq hNat
      have h' := by
        simpa [P₀, hOffsets_int] using h.symm
      simpa [delta, hDelta] using h'
    have hBase_left :
        base ((P (Fin.succ j)).symm (P₀ i)) t =
          ((affG.offsets.get ((P (Fin.succ j)).symm (P₀ i))).get t : ℤ) := by
      unfold base
      simp [hBase, indexToInt, indexToInt_apply,
        affine_offsets_at_zero (aff := affG)
          (j := (P (Fin.succ j)).symm (P₀ i)) (t := t)]
    have hBase_right : base i t = ((affG.offsets.get i).get t : ℤ) := by
      unfold base
      simp [hBase, indexToInt, indexToInt_apply,
        affine_offsets_at_zero (aff := affG) (j := i) (t := t)]
    calc
      base ((P (Fin.succ j)).symm (P₀ i)) t - base i t
          = ((affG.offsets.get ((P (Fin.succ j)).symm (P₀ i))).get t : ℤ) -
              ((affG.offsets.get i).get t : ℤ) := by
                simp [hBase_left, hBase_right]
      _ = (affF.M t j : ℤ) - (affG.M t j : ℤ) := hDiff
      _ = delta j t := by simp [delta, hDelta]
  refine ⟨?_, ?_⟩
  · simpa [P₀] using hOffsets_eq
  · intro j i t
    simpa [P₀, delta, hDelta, base, hBase]
      using hAlign j i t

/-- Skeleton lemma: positive-arity case of Lemma 5.4. Proof to be supplied later. -/
lemma lemma5_4_construct_permutation_family
    (f g : def2_3_SIMDFunction input_dims output_dims)
    (hWellF : def3_4_WellFormedKernel f.kernel)
    (hWellG : def3_4_WellFormedKernel g.kernel)
    (hDistinctF : def3_5_NoRepeatedIndices f.dependency)
    (hDistinctG : def3_5_NoRepeatedIndices g.dependency)
    (hK : f.k = g.k)
    (hPremise : def4_1_SMTPremise input_dims output_dims
      (applySIMD input_dims output_dims f)
      (applySIMD input_dims output_dims g)) :
    ∃ P : Fin (output_dims.length + 1) → Equiv.Perm (Fin g.k),
      ∀ j : Fin (output_dims.length + 1),
        List.Vector.ofFn (fun a =>
          (def2_2_DependencyMapping.castLength hK f.dependency
            (basisVector output_dims.length j)).get (P j a)) =
          g.dependency (basisVector output_dims.length j) := by
  classical
  have hUnique : ∀ j : Fin (output_dims.length + 1),
      ∃! P : Equiv.Perm (Fin g.k),
        List.Vector.ofFn (fun a =>
          (def2_2_DependencyMapping.castLength hK f.dependency
            (basisVector output_dims.length j)).get (P a)) =
          g.dependency (basisVector output_dims.length j) :=
    lemma5_4_vertexPermutations f g hWellF hWellG hDistinctF hDistinctG hK hPremise
  refine
    ⟨fun j => Classical.choose (ExistsUnique.exists (hUnique j)), ?_⟩
  intro j
  exact Classical.choose_spec (ExistsUnique.exists (hUnique j))

/-- Skeleton lemma: using Lemma 5.5 to show the permutation family is uniform. -/
lemma lemma5_4_permutation_family_uniform
    (f g : def2_3_SIMDFunction input_dims output_dims)
    (affF : def2_4_AffineDependencyMapping output_dims.length input_dims.length f.k)
    (affG : def2_4_AffineDependencyMapping output_dims.length input_dims.length g.k)
    (hAffineF : affF.toMapping = f.dependency)
    (hAffineG : affG.toMapping = g.dependency)
    (hDistinctG : def3_5_NoRepeatedIndices g.dependency)
    (hK : f.k = g.k)
    (P : Fin (output_dims.length + 1) → Equiv.Perm (Fin g.k))
    (hFamily : ∀ j : Fin (output_dims.length + 1),
      List.Vector.ofFn (fun a =>
        (def2_2_DependencyMapping.castLength hK f.dependency
          (basisVector output_dims.length j)).get (P j a)) =
        g.dependency (basisVector output_dims.length j)) :
    ∀ j : Fin (output_dims.length + 1), P j = P (zeroIndex output_dims.length) := by
  classical
  let affF' := def2_4_AffineDependencyMapping.castLength hK affF
  have hFamily_get_raw :
      ∀ j : Fin (output_dims.length + 1), ∀ i : Fin g.k,
        (def2_2_DependencyMapping.castLength hK f.dependency
          (basisVector output_dims.length j)).get (P j i) =
        (g.dependency (basisVector output_dims.length j)).get i := by
    intro j i
    have h := hFamily j
    have hget := congrArg (fun v => v.get i) h
    simpa [List.Vector.ofFn, List.Vector.get_ofFn]
      using hget
  have hFamily_get_aff :
      ∀ j : Fin (output_dims.length + 1), ∀ i : Fin g.k,
        (affF'.toMapping (basisVector output_dims.length j)).get (P j i) =
        (affG.toMapping (basisVector output_dims.length j)).get i := by
    intro j i
    have h := hFamily_get_raw j i
    simpa [affF', hAffineF, hAffineG]
      using h
  have hZero : ∀ i : Fin g.k,
      (affF'.toMapping (basisVector output_dims.length (zeroIndex _))).get
          (P (zeroIndex _) i) =
        (affG.toMapping (basisVector output_dims.length (zeroIndex _))).get i := by
    intro i
    simpa using hFamily_get_aff (zeroIndex _) i
  have hSucc : ∀ j : Fin output_dims.length, ∀ i : Fin g.k,
      (affF'.toMapping (basisVector output_dims.length (Fin.succ j))).get
          (P (Fin.succ j) i) =
        (affG.toMapping (basisVector output_dims.length (Fin.succ j))).get i := by
    intro j i
    simpa using hFamily_get_aff (Fin.succ j) i
  obtain ⟨hOffsets, hAlign⟩ :=
    lemma5_4_affine_alignment (affF := affF') (affG := affG) (P := P)
      (n := output_dims.length) (m := input_dims.length)
      (k := g.k) hZero hSucc
  let base : Fin g.k → (Fin input_dims.length → ℤ) := fun a =>
    indexToInt ((affG.toMapping (basisVector output_dims.length (zeroIndex _))).get a)
  have hDistinct_base : ∀ a b : Fin g.k, a ≠ b → base a ≠ base b := by
    intro a b hne
    refine indexToInt_ne ?_
    have hIdx :=
      hDistinctG (basisVector output_dims.length (zeroIndex _)) a b hne
    simpa [hAffineG] using hIdx
  let delta := fun j : Fin output_dims.length =>
    fun t : Fin input_dims.length =>
      (affF'.M t j : ℤ) - (affG.M t j : ℤ)
  have hAlignment : ∀ j : Fin output_dims.length, ∀ i i' : Fin g.k,
      base ((P (Fin.succ j)).symm (P (zeroIndex _) i)) - base i =
        base ((P (Fin.succ j)).symm (P (zeroIndex _) i')) - base i' := by
    intro j i i'
    funext t
    have hAlign_i := hAlign j i t
    have hAlign_i' := hAlign j i' t
    have hDelta :
        indexToInt ((affG.toMapping (basisVector output_dims.length (zeroIndex _))).get
            ((P (Fin.succ j)).symm (P (zeroIndex _) i))) t -
          indexToInt ((affG.toMapping (basisVector output_dims.length (zeroIndex _))).get i) t =
        delta j t := by
      simpa [delta]
        using hAlign_i
    have hDelta' :
        indexToInt ((affG.toMapping (basisVector output_dims.length (zeroIndex _))).get
            ((P (Fin.succ j)).symm (P (zeroIndex _) i'))) t -
          indexToInt ((affG.toMapping (basisVector output_dims.length (zeroIndex _))).get i') t =
        delta j t := by
      simpa [delta]
        using hAlign_i'
    calc
      base ((P (Fin.succ j)).symm (P (zeroIndex _) i)) t - base i t
          = delta j t := by
                simpa [base, indexToInt] using hDelta
      _ = base ((P (Fin.succ j)).symm (P (zeroIndex _) i')) t - base i' t := by
                simpa [base, indexToInt] using hDelta'.symm
  let ctx : lemma5_5_PermutationEquivalenceContext
      (Fin input_dims.length → ℤ) output_dims.length g.k :=
    { P := P
      base := base
      alignment := hAlignment
      distinct := by
        intro a b hne
        exact hDistinct_base a b hne }
  have hPermEq :=
    lemma5_5_permutation_equivalence
      (β := Fin input_dims.length → ℤ) (ctx := ctx)
  intro j
  have := hPermEq j
  simpa [ctx, zeroIndex] using this

/-- Skeleton lemma: deducing mapping permutation equivalence from a uniform permutation. -/
lemma lemma5_4_mapping_equivalence_from_uniform
    (f g : def2_3_SIMDFunction input_dims output_dims)
    (affF : def2_4_AffineDependencyMapping output_dims.length input_dims.length f.k)
    (affG : def2_4_AffineDependencyMapping output_dims.length input_dims.length g.k)
    (hAffineF : affF.toMapping = f.dependency)
    (hAffineG : affG.toMapping = g.dependency)
    (hK : f.k = g.k)
    (P : Equiv.Perm (Fin g.k))
    (hFamily : ∀ j : Fin (output_dims.length + 1),
      List.Vector.ofFn (fun a =>
        (def2_2_DependencyMapping.castLength hK f.dependency
          (basisVector output_dims.length j)).get (P a)) =
        g.dependency (basisVector output_dims.length j)) :
    def3_2_MappingPermutationEquivalent
      (def2_2_DependencyMapping.castLength hK affF.toMapping)
      affG.toMapping := by
  classical
  by_cases hk0 : g.k = 0
  · have hk0' : f.k = 0 := by simpa [hk0] using hK
    refine ⟨P, ?_⟩
    intro x
    apply List.Vector.ext
    intro j
    have hFalse : False :=
      (Nat.not_lt_zero j.val) (by simpa [hk0] using j.is_lt)
    exact hFalse.elim
  · have hkPos : 0 < g.k := Nat.pos_of_ne_zero hk0
    let affF' := def2_4_AffineDependencyMapping.castLength hK affF
    let Pfamily : Fin (output_dims.length + 1) → Equiv.Perm (Fin g.k) := fun _ => P
    have hFamily_get_raw :
        ∀ j : Fin (output_dims.length + 1), ∀ i : Fin g.k,
          (def2_2_DependencyMapping.castLength hK f.dependency
            (basisVector output_dims.length j)).get (P i) =
          (g.dependency (basisVector output_dims.length j)).get i := by
      intro j i
      have h := hFamily j
      have hget := congrArg (fun v => v.get i) h
      simpa [List.Vector.ofFn, List.Vector.get_ofFn]
        using hget
    have hFamily_get_aff :
        ∀ j : Fin (output_dims.length + 1), ∀ i : Fin g.k,
          (affF'.toMapping (basisVector output_dims.length j)).get (P i) =
          (affG.toMapping (basisVector output_dims.length j)).get i := by
      intro j i
      have h := hFamily_get_raw j i
      simpa [affF', hAffineF, hAffineG] using h
    have hZero : ∀ i : Fin g.k,
        (affF'.toMapping (basisVector output_dims.length (zeroIndex _))).get (P i) =
          (affG.toMapping (basisVector output_dims.length (zeroIndex _))).get i := by
      intro i; simpa using hFamily_get_aff (zeroIndex _) i
    have hSucc : ∀ j : Fin output_dims.length, ∀ i : Fin g.k,
        (affF'.toMapping (basisVector output_dims.length (Fin.succ j))).get (P i) =
          (affG.toMapping (basisVector output_dims.length (Fin.succ j))).get i := by
      intro j i; simpa using hFamily_get_aff (Fin.succ j) i
    obtain ⟨hOffsets, hAlign⟩ :=
      lemma5_4_affine_alignment (affF := affF') (affG := affG) (P := Pfamily)
        (n := output_dims.length) (m := input_dims.length)
        (k := g.k) hZero hSucc
    let i₀ : Fin g.k := ⟨0, hkPos⟩
    have hMatrix_eq_int :
        ∀ t : Fin input_dims.length, ∀ j : Fin output_dims.length,
          (affF'.M t j : ℤ) = (affG.M t j : ℤ) := by
      intro t j
      have h := hAlign j i₀ t
      have hDiff : (affF'.M t j : ℤ) - (affG.M t j : ℤ) = 0 := by
        have := h.symm
        simpa [Pfamily, zeroIndex, Equiv.apply_symm_apply, indexToInt]
          using this
      have hEq := sub_eq_zero.mp hDiff
      simpa using hEq
    have hMatrix_eq : affF'.M = affG.M := by
      ext t j
      have h := hMatrix_eq_int t j
      exact Int.ofNat.inj h
    have hOffsets_eq : ∀ i : Fin g.k,
        affF'.offsets.get (P i) = affG.offsets.get i := by
      intro i
      have h := hOffsets i
      simpa [Pfamily, zeroIndex] using h
    refine ⟨P, ?_⟩
    intro x
    have hFinal :
        List.Vector.ofFn (fun a => (affF'.toMapping x).get (P a)) =
          affG.toMapping x := by
      apply List.Vector.ext
      intro i
      apply List.Vector.ext
      intro t
      have hF := affF'.affine x (P i) t
      have hG := affG.affine x i t
      have hOffset_vec := hOffsets_eq i
      have hOffset_coord :
          (affF'.offsets.get (P i)).get t = (affG.offsets.get i).get t := by
        simpa using congrArg (fun v => v.get t) hOffset_vec
      calc
        ((List.Vector.ofFn fun a => (affF'.toMapping x).get (P a)).get i).get t
            = ((affF'.toMapping x).get (P i)).get t := by
                  simp [List.Vector.ofFn, List.Vector.get_ofFn]
        _ = Matrix.mulVec affF'.M (fun s => x.get s) t +
              (affF'.offsets.get (P i)).get t := by
                  simpa using hF
        _ = Matrix.mulVec affG.M (fun s => x.get s) t +
              (affF'.offsets.get (P i)).get t := by
                  simp [hMatrix_eq]
        _ = Matrix.mulVec affG.M (fun s => x.get s) t +
              (affG.offsets.get i).get t := by
                  simp [hOffset_coord]
        _ = ((affG.toMapping x).get i).get t := by
                  simpa using hG.symm
    simpa [affF', hAffineF] using hFinal

lemma lemma5_4_mappingPermutation_equivalence
    (f g : def2_3_SIMDFunction input_dims output_dims)
    (hWellF : def3_4_WellFormedKernel f.kernel)
    (hWellG : def3_4_WellFormedKernel g.kernel)
    (hDistinctF : def3_5_NoRepeatedIndices f.dependency)
    (hDistinctG : def3_5_NoRepeatedIndices g.dependency)
    (affF : def2_4_AffineDependencyMapping output_dims.length input_dims.length f.k)
    (affG : def2_4_AffineDependencyMapping output_dims.length input_dims.length g.k)
    (hAffineF : affF.toMapping = f.dependency)
    (hAffineG : affG.toMapping = g.dependency)
    (hK : f.k = g.k)
    (hPremise : def4_1_SMTPremise input_dims output_dims
      (applySIMD input_dims output_dims f)
      (applySIMD input_dims output_dims g)) :
    def3_2_MappingPermutationEquivalent
      (def2_2_DependencyMapping.castLength hK affF.toMapping)
      affG.toMapping := by
  classical
  obtain ⟨Pfamily, hFamily⟩ :=
    lemma5_4_construct_permutation_family f g
      hWellF hWellG hDistinctF hDistinctG hK hPremise
  have hUniform : ∀ j : Fin (output_dims.length + 1),
      Pfamily j = Pfamily (zeroIndex output_dims.length) :=
    lemma5_4_permutation_family_uniform f g affF affG
      hAffineF hAffineG hDistinctG hK Pfamily hFamily
  let P := Pfamily (zeroIndex output_dims.length)
  have hFamilyUniform : ∀ j : Fin (output_dims.length + 1),
      List.Vector.ofFn (fun a =>
        (def2_2_DependencyMapping.castLength hK f.dependency
          (basisVector output_dims.length j)).get (P a)) =
        g.dependency (basisVector output_dims.length j) := by
    intro j
    have := hFamily j
    simpa [P, hUniform j] using this
  exact
    lemma5_4_mapping_equivalence_from_uniform f g affF affG
      hAffineF hAffineG hK P hFamilyUniform

end MappingPermutation
