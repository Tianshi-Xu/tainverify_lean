import denote.KRankAddGather

namespace TrainVerify.Denote
noncomputable section

private theorem tensorSum_valAt_same_shape (xs : List Tensor) (sh : Shape)
    (hne : xs ≠ []) (hs : ∀ x ∈ xs, x.shape = sh) (i : Nat) :
    valAt (tensorSum xs) i = xs.foldl (fun acc x => acc + valAt x i) 0 := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs =>
    have hx := hs x (by simp)
    by_cases hi : i < prodShape sh
    · rw [valAt_of_lt _ _ (by simpa only [tensorSum_shape, hx] using hi)]
      rfl
    · have hzero : ∀ y ∈ x :: xs, valAt y i = 0 := by
        intro y hy
        simp only [valAt, hs y hy, dif_neg hi]
      have hz : ∀ (ys : List Tensor), (∀ y ∈ ys, valAt y i = 0) →
          ∀ a : Scalar, ys.foldl (fun acc y => acc + valAt y i) a = a := by
        intro ys hys a
        induction ys generalizing a with
        | nil => rfl
        | cons y ys ih =>
          simp only [List.foldl_cons, hys y (by simp), add_zero]
          exact ih (fun z hz => hys z (by simp [hz])) a
      rw [hz (x :: xs) hzero 0]
      simp only [valAt, tensorSum_shape, hx, dif_neg hi]

-- Rank-major output: preserve both operand order and rank order.
def tensorSumRanks (K : Nat) (columns : List (List Tensor)) : List Tensor :=
  List.ofFn (fun r : Fin K => tensorSum (columns.map (fun xs => xs.getD r (zeroTensor []))))

private theorem tensorSumRanks_shape (K : Nat) (columns : List (List Tensor))
    (sh : Shape) (hne : columns ≠ [])
    (hlen : ∀ xs ∈ columns, xs.length = K)
    (hs : ∀ xs ∈ columns, ∀ x ∈ xs, x.shape = sh) :
    ∀ x ∈ tensorSumRanks K columns, x.shape = sh := by
  intro x hx
  simp only [tensorSumRanks, List.mem_ofFn] at hx
  obtain ⟨r, rfl⟩ := hx
  cases columns with
  | nil => exact (hne rfl).elim
  | cons xs rest =>
    simp only [List.map_cons, tensorSum_shape]
    have hr : r.val < xs.length := by rw [hlen xs (by simp)]; exact r.isLt
    rw [List.getD, List.getElem?_eq_getElem hr]
    exact hs xs (by simp) xs[r.val] (List.getElem_mem hr)

/-- Ordered nonempty operand lists commute with an ordered K-rank gather.
No fixed arity, rank count, shape rank or gather axis is baked into the theorem. -/
theorem tensorSum_allGather_dim_K
    (dim K : Nat) (sh : Shape) (columns : List (List Tensor))
    (hK : 0 < K) (hne : columns ≠ []) (_hdim : dim < sh.length)
    (hlen : ∀ xs ∈ columns, xs.length = K)
    (hs : ∀ xs ∈ columns, ∀ x ∈ xs, x.shape = sh) :
    tensorSum (columns.map (allGatherPrimDimN dim K 0)) =
      allGatherPrimDimN dim K 0 (tensorSumRanks K columns) := by
  have hhead : ∀ xs ∈ columns, (xs.head?.map (fun t => t.shape)).getD [] = sh := by
    intro xs hxs
    have hp : 0 < xs.length := by rw [hlen xs hxs]; exact hK
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hp]
    simp only [Option.map_some, Option.getD_some]
    exact hs xs hxs _ (List.getElem_mem hp)
  have hrows := tensorSumRanks_shape K columns sh hne hlen hs
  have hrowslen : (tensorSumRanks K columns).length = K := by simp [tensorSumRanks]
  have hrowshead : ((tensorSumRanks K columns).head?.map (fun t => t.shape)).getD [] = sh := by
    have hp : 0 < (tensorSumRanks K columns).length := by rw [hrowslen]; exact hK
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hp]
    simp only [Option.map_some, Option.getD_some]
    exact hrows _ (List.getElem_mem hp)
  let full := sh.set dim (sh.getD dim 0 * K)
  have hfull : ∀ xs ∈ columns, (allGatherPrimDimN dim K 0 xs).shape = full := by
    intro xs hxs
    exact allGatherPrimDimN_shape dim K xs sh (hhead xs hxs)
  have hleft : (tensorSum (columns.map (allGatherPrimDimN dim K 0))).shape = full := by
    cases columns with
    | nil => exact (hne rfl).elim
    | cons xs rest => exact hfull xs (by simp)
  have hright : (allGatherPrimDimN dim K 0 (tensorSumRanks K columns)).shape = full :=
    allGatherPrimDimN_shape dim K _ sh hrowshead
  apply Tensor.ext
  · exact hleft.trans hright.symm
  · intro i hi
    have hifull : i < prodShape full := by rwa [hleft] at hi
    rw [tensorSum_valAt_same_shape _ full (by simpa using hne)
      (by intro x hx; obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx; exact hfull xs hxs)]
    rw [valAt_of_lt _ _ (by rwa [hright])]
    simp only [allGatherPrimDimN, Tensor.mkShape, hrowshead]
    let ds := sh.getD dim 0
    let ps := List.foldl (· * ·) 1 (sh.drop (dim + 1))
    let fds := ds * K * ps
    let r := if ds = 0 then 0 else (if ps = 0 then 0 else (if fds = 0 then 0 else i % fds) / ps) / ds
    let loc := (if fds = 0 then 0 else i / fds) * (ds * ps) +
      (if ds = 0 then 0 else (if ps = 0 then 0 else (if fds = 0 then 0 else i % fds) / ps) % ds) * ps +
      (if ps = 0 then 0 else (if fds = 0 then 0 else i % fds) % ps)
    change _ = valAt ((tensorSumRanks K columns).getD r (zeroTensor sh)) loc
    have hv : ∀ xs ∈ columns, valAt (allGatherPrimDimN dim K 0 xs) i =
        valAt (xs.getD r (zeroTensor sh)) loc := by
      intro xs hxs
      rw [valAt_of_lt _ _ (by rwa [hfull xs hxs])]
      simp only [allGatherPrimDimN, Tensor.mkShape, hhead xs hxs]
      rfl
    simp only [List.foldl_map]
    by_cases hr : r < K
    · have hrrows : r < (tensorSumRanks K columns).length := by rwa [hrowslen]
      rw [List.getD, List.getElem?_eq_getElem hrrows]
      simp only [Option.getD_some, tensorSumRanks, List.getElem_ofFn]
      rw [tensorSum_valAt_same_shape _ sh (by simpa using hne) (by
        intro x hx
        obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx
        have hrxs : r < xs.length := by rwa [hlen xs hxs]
        rw [List.getD, List.getElem?_eq_getElem hrxs]
        exact hs xs hxs _ (List.getElem_mem hrxs))]
      simp only [List.foldl_map]
      have heq : ∀ xs ∈ columns, valAt (allGatherPrimDimN dim K 0 xs) i =
          valAt (xs.getD r (zeroTensor [])) loc := by
        intro xs hxs
        rw [hv xs hxs]
        have hrxs : r < xs.length := by rwa [hlen xs hxs]
        simp only [List.getD, List.getElem?_eq_getElem hrxs, Option.getD_some]
      have hmap := List.map_congr_left heq
      have hsum := congrArg (fun vs : List Scalar => vs.foldl (· + ·) 0) hmap
      simpa only [List.foldl_map] using hsum
    · have hrrows : (tensorSumRanks K columns).length ≤ r := by rw [hrowslen]; omega
      rw [List.getD, List.getElem?_eq_none hrrows]
      simp [Option.getD_none, zeroTensor, Tensor.mkShape, valAt]
      have hzero : ∀ xs ∈ columns, valAt (allGatherPrimDimN dim K 0 xs) i = 0 := by
        intro xs hxs
        rw [hv xs hxs, List.getD, List.getElem?_eq_none (by rw [hlen xs hxs]; omega)]
        simp [Option.getD_none, zeroTensor, Tensor.mkShape, valAt]
      have hfold : ∀ (ys : List (List Tensor)), (∀ xs ∈ ys, valAt (allGatherPrimDimN dim K 0 xs) i = 0) →
          ∀ a : Scalar, ys.foldl (fun acc xs => acc + valAt (allGatherPrimDimN dim K 0 xs) i) a = a := by
        intro ys hys a
        induction ys generalizing a with
        | nil => rfl
        | cons x xs ih =>
          simp only [List.foldl_cons, hys x (by simp), add_zero]
          exact ih (fun y hy => hys y (by simp [hy])) a
      exact hfold columns hzero 0

end
end TrainVerify.Denote
