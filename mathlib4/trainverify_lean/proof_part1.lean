import trainverify.proof_def

namespace TrainVerify

lemma lemma5_1_dependency_set_eq_proof_step
  (f g : def2_3_SIMDFunction input_dims output_dims)
  (hWellF : def3_4_WellFormedKernel f.kernel)
    (hDistinctF : def3_5_NoRepeatedIndices f.dependency)
    (hDistinctG : def3_5_NoRepeatedIndices g.dependency)
    (i : Index output_dims.length)
    (hEq : ∀ x : def1_1_Tensor input_dims,
      applySIMD input_dims output_dims f x i =
        applySIMD input_dims output_dims g x i)
    (a : Fin f.k) :
    ∃ b : Fin g.k, (g.dependency i).get b = (f.dependency i).get a := by
  classical
  set τf := f.dependency i
  set τg := g.dependency i
  have hDistinctτf : ∀ {u v : Fin f.k}, u ≠ v → τf.get u ≠ τf.get v := by
    intro u v huv
    simpa [τf] using hDistinctF i u v huv
  have hDistinctτg : ∀ {u v : Fin g.k}, u ≠ v → τg.get u ≠ τg.get v := by
    intro u v huv
    simpa [τg] using hDistinctG i u v huv
  let target := τf.get a
  by_contra hNone
  have hTarget_not_in_g : ∀ b : Fin g.k, τg.get b ≠ target := by
    intro b
    exact fun hb => hNone ⟨b, by simpa [target] using hb⟩
  have hTarget_not_in_f : ∀ {b : Fin f.k}, b ≠ a → τf.get b ≠ target := by
    intro b hb
    have : τf.get b ≠ τf.get a := hDistinctτf hb
    simpa [target]
  let x₀ : def1_1_Tensor input_dims := fun _ => (0 : ℝ)
  let x₁ : def1_1_Tensor input_dims := fun p => if p = target then (1 : ℝ) else 0
  let vecf₀ := List.Vector.map (fun p => x₀ p) τf
  let vecf₁ := List.Vector.map (fun p => x₁ p) τf
  let vecg₀ := List.Vector.map (fun p => x₀ p) τg
  let vecg₁ := List.Vector.map (fun p => x₁ p) τg
  have hKernel₀ : f.kernel vecf₀ = g.kernel vecg₀ := by
    simpa [vecf₀, vecg₀, τf, τg, applySIMD, applySIMDAt, x₀] using hEq x₀
  have hKernel₁ : f.kernel vecf₁ = g.kernel vecg₁ := by
    simpa [vecf₁, vecg₁, τf, τg, applySIMD, applySIMDAt, x₁] using hEq x₁
  have hVecf_agree : ∀ {b : Fin f.k}, b ≠ a → vecf₀.get b = vecf₁.get b := by
    intro b hb
    have hb' : τf.get b ≠ target := hTarget_not_in_f hb
    simp [vecf₀, vecf₁, x₀, x₁, hb', target]
  have hVecf_diff : vecf₀.get a ≠ vecf₁.get a := by
    simp [vecf₀, vecf₁, x₀, x₁, target]
  have hVecg_eq : vecg₀ = vecg₁ := by
    refine List.Vector.ext ?_
    intro b
    have hb : τg.get b ≠ target := hTarget_not_in_g b
    simp [vecg₀, vecg₁, x₀, x₁, hb, target]
  have hVecg_kernel_eq : g.kernel vecg₀ = g.kernel vecg₁ := by
    simp [hVecg_eq]
  have hKernel_eq : f.kernel vecf₀ = f.kernel vecf₁ := by
    calc
      f.kernel vecf₀ = g.kernel vecg₀ := hKernel₀
      _ = g.kernel vecg₁ := hVecg_kernel_eq
      _ = f.kernel vecf₁ := by simpa using hKernel₁.symm
  have hKernelF_diff :=
    hWellF a vecf₀ vecf₁ (by intro b hb; exact hVecf_agree hb) hVecf_diff
  exact hKernelF_diff hKernel_eq


/-- *Claim 6* (skeleton). If two well-formed SIMD functions agree on all inputs
at a fixed output index, then the corresponding dependency vectors differ only
by a unique permutation. -/
lemma theorem5_2_dependencyPermutation_unique
    (f g : def2_3_SIMDFunction input_dims output_dims)
    (hWellF : def3_4_WellFormedKernel f.kernel)
    (hWellG : def3_4_WellFormedKernel g.kernel)
    (hDistinctF : def3_5_NoRepeatedIndices f.dependency)
    (hDistinctG : def3_5_NoRepeatedIndices g.dependency)
    (hK : f.k = g.k)
    (i : Index output_dims.length)
    (hEq : ∀ x : def1_1_Tensor input_dims,
      applySIMD input_dims output_dims f x i =
        applySIMD input_dims output_dims g x i) :
    ∃! (P : Equiv.Perm (Fin g.k)),
      List.Vector.ofFn (fun j =>
        (def2_2_DependencyMapping.castLength hK f.dependency i).get (P j)) =
        g.dependency i := by
  classical
  set τf := f.dependency i
  set τg := g.dependency i
  set τfCast := def2_2_DependencyMapping.castLength hK f.dependency i
  have hDistinctτf : ∀ {u v : Fin f.k}, u ≠ v → τf.get u ≠ τf.get v := by
    intro u v huv
    simpa [τf] using hDistinctF i u v huv
  have hDistinctτg : ∀ {u v : Fin g.k}, u ≠ v → τg.get u ≠ τg.get v := by
    intro u v huv
    simpa [τg] using hDistinctG i u v huv
  have hDistinctτfCast : ∀ {a b : Fin g.k}, a ≠ b →
      τfCast.get a ≠ τfCast.get b := by
    intro a b hneq hEqVals
    have hVal : τf.get (Fin.cast hK.symm a) = τf.get (Fin.cast hK.symm b) := by
      simpa [τfCast, dependency_cast_get, τf] using hEqVals
    have hIdx : Fin.cast hK.symm a = Fin.cast hK.symm b := by
      by_contra hIdx
      exact (hDistinctτf hIdx) hVal
    have : a = b := by
      simpa [Fin.cast_cast_symm] using congrArg (Fin.cast hK) hIdx
    exact hneq this
  have hCover_fg : ∀ a : Fin f.k, ∃ b : Fin g.k, τg.get b = τf.get a :=
    lemma5_1_dependency_set_eq_proof_step f g hWellF hDistinctF hDistinctG i hEq
  have hEqSymm : ∀ x : def1_1_Tensor input_dims,
      applySIMD input_dims output_dims g x i =
        applySIMD input_dims output_dims f x i := by
    intro x
    simpa [applySIMD, applySIMDAt] using (hEq x).symm
  have hCover_gf : ∀ j : Fin g.k, ∃! a : Fin f.k, τf.get a = τg.get j := by
    intro j
    obtain ⟨a, ha⟩ :=
  lemma5_1_dependency_set_eq_proof_step g f hWellG hDistinctG hDistinctF i hEqSymm j
    refine ⟨a, ha, ?_⟩
    intro a' ha'
    have : τf.get a' = τf.get a := by
      simpa using ha'.trans ha.symm
    by_contra hneq
    exact (hDistinctτf hneq) this
  classical
  choose σ₀ hσ₀_eq hσ₀_unique using hCover_gf
  let σ : Fin g.k → Fin g.k := fun j => Fin.cast hK (σ₀ j)
  have hσ_eq : ∀ j : Fin g.k, τfCast.get (σ j) = τg.get j := by
    intro j
    have hCast : τfCast.get (σ j) =
        τf.get (Fin.cast hK.symm (Fin.cast hK (σ₀ j))) := by
      simp [τfCast, σ, dependency_cast_get, τf]
    simpa [σ, τf, Fin.cast_symm_cast] using hCast.trans (hσ₀_eq j)
  have hσ_injective : Function.Injective σ := by
    intro j₁ j₂ hσeq
    have hSame : τfCast.get (σ j₁) = τfCast.get (σ j₂) := by simp [hσeq]
    have hx : τg.get j₁ = τfCast.get (σ j₁) := (hσ_eq j₁).symm
    have hy : τfCast.get (σ j₂) = τg.get j₂ := hσ_eq j₂
    have : τg.get j₁ = τg.get j₂ := by
      calc
        τg.get j₁ = τfCast.get (σ j₁) := hx
        _ = τfCast.get (σ j₂) := hSame
        _ = τg.get j₂ := by simpa using hy
    classical
    by_contra hneq
    exact (hDistinctτg hneq) this
  have hσ_surjective : Function.Surjective σ := by
    intro b
    obtain ⟨j, hj⟩ := hCover_fg (Fin.cast hK.symm b)
    refine ⟨j, ?_⟩
    have hb : τf.get (Fin.cast hK.symm b) = τg.get j := by
      simpa using hj.symm
    have hCast : Fin.cast hK.symm b = σ₀ j := by
      simpa using hσ₀_unique j (Fin.cast hK.symm b) hb
    have hσeq : b = σ j := by
      unfold σ
      simpa [Fin.cast_cast_symm] using congrArg (Fin.cast hK) hCast
    exact hσeq.symm
  let P := Equiv.ofBijective σ ⟨hσ_injective, hσ_surjective⟩
  have hVectorEq :
      List.Vector.ofFn (fun j => τfCast.get (P j)) = τg := by
    refine List.Vector.ext ?_
    intro j
    simp [List.Vector.get_ofFn, P, hσ_eq]
  refine ⟨P, ?_, ?_⟩
  · simpa [τfCast] using hVectorEq
  · intro P' hP'
    apply Equiv.ext
    intro j
    have hValP : τfCast.get (P j) = τg.get j := by
      have := congrArg (fun v => v.get j) hVectorEq
      simpa [List.Vector.get_ofFn, P]
    have hValP' : τfCast.get (P' j) = τg.get j := by
      have := congrArg (fun v => v.get j) hP'
      simpa [τfCast, List.Vector.get_ofFn]
    have hEqIndices : P j = P' j := by
      classical
      by_contra hneq
      exact (hDistinctτfCast hneq) (by simp [hValP, hValP'])
    simp [hEqIndices]


/-! *Lemma 7* (skeleton). Equality on the zero vertex implies the two kernels
are equivalent up to a permutation set. -/
lemma lemma5_3_kernelPermutation_from_vertexPremise
    (f g : def2_3_SIMDFunction input_dims output_dims)
    (hWellF : def3_4_WellFormedKernel f.kernel)
    (hWellG : def3_4_WellFormedKernel g.kernel)
    (hDistinctF : def3_5_NoRepeatedIndices f.dependency)
    (hDistinctG : def3_5_NoRepeatedIndices g.dependency)
    (hK : f.k = g.k)
    (hPremise : def4_1_SMTPremise input_dims output_dims
      (applySIMD input_dims output_dims f)
      (applySIMD input_dims output_dims g)) :
    def3_3_KernelPermutationSetEquivalent
      (def2_1_KernelFunction.castLength hK f.kernel)
      g.kernel := by
  classical
  -- zero vertex where the SMT premise applies
  let i₀ : Index output_dims.length := List.Vector.ofFn fun _ => 0
  have hVertex : i₀ ∈ def4_1_VertexIndexSet output_dims.length := by
    intro j; exact Or.inl (by simp [i₀])
  have hEqZero : ∀ x : def1_1_Tensor input_dims,
      applySIMD input_dims output_dims f x i₀ =
        applySIMD input_dims output_dims g x i₀ :=
    fun x => hPremise x i₀ hVertex
  -- unpack dependency information at the zero vertex
  set τf := f.dependency i₀
  set τg := g.dependency i₀
  set τfCast := def2_2_DependencyMapping.castLength hK f.dependency i₀
  have hDistinctτf : ∀ {a b : Fin f.k}, a ≠ b → τf.get a ≠ τf.get b := by
    intro a b hneq
    simpa [τf] using hDistinctF i₀ a b hneq
  have hDistinctτg : ∀ {a b : Fin g.k}, a ≠ b → τg.get a ≠ τg.get b := by
    intro a b hneq
    simpa [τg] using hDistinctG i₀ a b hneq
  have hDistinctτfCast : ∀ {a b : Fin g.k}, a ≠ b → τfCast.get a ≠ τfCast.get b := by
    intro a b hneq hEqVals
    have : τf.get (Fin.cast hK.symm a) = τf.get (Fin.cast hK.symm b) := by
      simpa [τfCast, dependency_cast_get, τf] using hEqVals
    have hIdx : Fin.cast hK.symm a = Fin.cast hK.symm b := by
      by_contra hIdx
      exact (hDistinctτf hIdx) this
    have : a = b := by
      simpa [Fin.cast_cast_symm] using congrArg (Fin.cast hK) hIdx
    exact hneq this
  have hUniqueIdx : ∀ {a b : Fin g.k}, τfCast.get a = τfCast.get b → a = b := by
    intro a b h
    classical
    by_contra hneq
    exact (hDistinctτfCast hneq) h
  -- obtain the unique permutation aligning the dependency vectors
  obtain ⟨P, hVecEq, hUniqueP⟩ :=
    theorem5_2_dependencyPermutation_unique f g hWellF hWellG hDistinctF hDistinctG hK i₀ hEqZero
  have hAlign : ∀ j : Fin g.k, τg.get j = τfCast.get (P j) := by
    intro j
    have h := congrArg (fun v => v.get j) hVecEq
    simpa [τfCast, τg, List.Vector.get_ofFn] using h.symm
  -- build the permutation set consisting of this unique witness
  refine ⟨{P}, ?_, ?_⟩
  · exact Set.singleton_nonempty _
  · intro P' hP' xVec
    have hPP : P' = P := by
      simpa [Set.mem_singleton_iff] using hP'
    have hAlign' : ∀ j : Fin g.k, τg.get j = τfCast.get (P' j) := by
      intro j
      have := hAlign j
      simpa [hPP] using this
    -- construct a tensor realizing any given kernel input vector
    let xTensor : def1_1_Tensor input_dims := fun idx =>
      if h : ∃ a : Fin g.k, τfCast.get a = idx then
        xVec.get (Classical.choose h)
      else
        0
    have hxTensor_at : ∀ a : Fin g.k, xTensor (τfCast.get a) = xVec.get a := by
      intro a
      classical
      have hWitness : ∃ b : Fin g.k, τfCast.get b = τfCast.get a := ⟨a, rfl⟩
      have hChoice : τfCast.get (Classical.choose hWitness) = τfCast.get a :=
        Classical.choose_spec hWitness
      have hIdx : Classical.choose hWitness = a := hUniqueIdx hChoice
      simp [xTensor, hWitness, hIdx]
    have hxTensor_perm : ∀ j : Fin g.k, xTensor (τg.get j) = xVec.get (P' j) := by
      intro j
      simpa [hAlign' j, hPP] using hxTensor_at (P' j)
    have hxTensor_base : ∀ a : Fin f.k, xTensor (τf.get a) =
        xVec.get (Fin.cast hK a) := by
      intro a
      have := hxTensor_at (Fin.cast hK a)
      simpa [τfCast, τf, dependency_cast_get, Fin.cast_symm_cast] using this
    have hVec_fCast :
        List.Vector.map (fun idx => xTensor idx) τfCast = xVec := by
      refine List.Vector.ext ?_
      intro a
      have hx := hxTensor_at a
      simp [List.Vector.get_map, hx]
    have hVec_f :
        List.Vector.map (fun idx => xTensor idx) τf =
          List.Vector.ofFn (fun a : Fin f.k => xVec.get (Fin.cast hK a)) := by
      refine List.Vector.ext ?_
      intro a
      have hx := hxTensor_base a
      simp [List.Vector.get_map, List.Vector.get_ofFn, hx]
    have hVec_g :
        List.Vector.map (fun idx => xTensor idx) τg =
          List.Vector.ofFn (fun j => xVec.get (P' j)) := by
      refine List.Vector.ext ?_
      intro j
      have hx := hxTensor_perm j
      simp [List.Vector.get_map, List.Vector.get_ofFn, hx]
    have hSimd := hEqZero xTensor
    have hSimd' :
        f.kernel (List.Vector.map (fun idx => xTensor idx) τf) =
          g.kernel (List.Vector.map (fun idx => xTensor idx) τg) := by
      simpa [applySIMD, applySIMDAt, i₀, τf, τg, xTensor]
        using hSimd
    have hKernelEq :
        f.kernel (List.Vector.ofFn fun a : Fin f.k => xVec.get (Fin.cast hK a)) =
          g.kernel (List.Vector.ofFn fun j => xVec.get (P' j)) := by
      simpa [hVec_f, hVec_g]
        using hSimd'
    have hCastEval :
        def2_1_KernelFunction.castLength hK f.kernel xVec =
          f.kernel (List.Vector.ofFn fun a : Fin f.k => xVec.get (Fin.cast hK a)) := by
      simpa using def2_1_KernelFunction.castLength_eval hK f.kernel xVec
    exact hCastEval.trans (by simpa [hPP] using hKernelEq)
