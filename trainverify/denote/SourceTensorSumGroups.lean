import denote.Denote

namespace TrainVerify.Denote
noncomputable section

private theorem sumGroup_shape (xs : List Tensor) (sh : Shape)
    (hne : xs ≠ []) (hs : ∀ x ∈ xs, x.shape = sh) : (tensorSum xs).shape = sh := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs => exact (tensorSum_shape x xs).trans (hs x List.mem_cons_self)

private theorem sumGroup_value (xs : List Tensor) (i : Nat)
    (hi : i < prodShape (tensorSum xs).shape) :
    valAt (tensorSum xs) i = (xs.map (fun x => valAt x i)).sum := by
  have hv : valAt (tensorSum xs) i = xs.foldl (fun a x => a + valAt x i) 0 := by
    cases xs <;> rw [valAt_of_lt _ _ hi] <;> rfl
  rw [hv, List.foldl_add_eq_sum]

/-- Regroup a nonempty ordered tensor sum without dropping or reordering inputs.
Every group is nonempty and every contributor has the same output shape. -/
theorem source_tensorSum_groups (groups : List (List Tensor)) (sh : Shape)
    (hne : groups ≠ []) (hgroups : ∀ xs ∈ groups, xs ≠ [])
    (hsh : ∀ xs ∈ groups, ∀ x ∈ xs, x.shape = sh) :
    tensorSum (groups.map tensorSum) = tensorSum groups.flatten := by
  have hi : ∀ xs ∈ groups, (tensorSum xs).shape = sh :=
    fun xs hx => sumGroup_shape xs sh (hgroups xs hx) (hsh xs hx)
  have hleft : (tensorSum (groups.map tensorSum)).shape = sh := by
    apply sumGroup_shape _ sh (fun h => hne (List.map_eq_nil_iff.mp h))
    intro x hx
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx
    exact hi xs hxs
  have hflat : groups.flatten ≠ [] := by
    obtain ⟨xs, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hx := hgroups xs List.mem_cons_self
    cases xs with
    | nil => exact (hx rfl).elim
    | cons x xs => simp only [List.flatten_cons, List.cons_append, ne_eq, reduceCtorEq, not_false_eq_true]
  have hright : (tensorSum groups.flatten).shape = sh := by
    apply sumGroup_shape _ sh hflat
    intro x hx
    obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
    exact hsh xs hxs x hx
  apply Tensor.ext (t1 := tensorSum (groups.map tensorSum))
    (t2 := tensorSum groups.flatten) (hleft.trans hright.symm)
  intro i hidx
  have hib : i < prodShape sh := by rwa [hleft] at hidx
  rw [sumGroup_value _ _ hidx, sumGroup_value _ _ (by rw [hright]; exact hib)]
  rw [List.map_map]
  have heq : groups.map (fun xs => valAt (tensorSum xs) i) =
      groups.map (fun xs => (xs.map (fun x => valAt x i)).sum) := by
    apply List.map_congr_left
    intro xs hxs
    exact sumGroup_value xs i (by rw [hi xs hxs]; exact hib)
  dsimp only [Function.comp_def]
  rw [heq]
  simp only [List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]

#print axioms source_tensorSum_groups
end
end TrainVerify.Denote
