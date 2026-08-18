import denote.Denote

namespace TrainVerify.Denote

private theorem foldl_mul_init_generic (a : Nat) (xs : List Nat) :
    xs.foldl (· * ·) a = a * xs.foldl (· * ·) 1 := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (a * x), ih (1 * x)]
    ring

private theorem prodShape_cons_generic (a : Nat) (bs : List Nat) :
    prodShape (a :: bs) = a * prodShape bs := by
  simp only [prodShape, List.foldl]
  rw [foldl_mul_init_generic]
  simp

private theorem prodShape_split_generic (sh : Shape) (dim : Nat)
    (hdim : dim < sh.length) :
    prodShape sh = (sh.take dim).foldl (· * ·) 1 * sh.getD dim 0 *
      (sh.drop (dim + 1)).foldl (· * ·) 1 := by
  induction sh generalizing dim with
  | nil => simp at hdim
  | cons d ds ih =>
    cases dim with
    | zero =>
      simp only [List.take, List.drop, List.getD_cons_zero, List.foldl]
      rw [prodShape_cons_generic]
      simp [prodShape]
    | succ dim =>
      simp only [List.length_cons] at hdim
      have hdim' : dim < ds.length := by omega
      rw [prodShape_cons_generic, ih dim hdim']
      simp only [List.take, List.drop, List.getD_cons_succ, List.foldl]
      rw [foldl_mul_init_generic (1 * d)]
      ring

private theorem getD_set_self_generic (sh : Shape) (dim v : Nat)
    (hdim : dim < sh.length) : (sh.set dim v).getD dim 0 = v := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hdim), List.getElem_set_self]
  rfl

private theorem prodShape_set_generic (sh : Shape) (dim v : Nat)
    (hdim : dim < sh.length) :
    prodShape (sh.set dim v) =
      (sh.take dim).foldl (· * ·) 1 * v *
        (sh.drop (dim + 1)).foldl (· * ·) 1 := by
  rw [prodShape_split_generic (sh.set dim v) dim (by simpa using hdim)]
  rw [List.take_set_of_le (Nat.le_refl dim)]
  rw [getD_set_self_generic sh dim v hdim]
  rw [List.drop_set_of_lt (Nat.lt_succ_self dim)]

private theorem ofFn_head_shape {K : Nat} (hK : 0 < K) (f : Fin K → Tensor) :
    ((List.ofFn f).head?.map (fun t => t.shape)).getD [] = (f ⟨0, hK⟩).shape := by
  cases K with
  | zero => omega
  | succ n =>
    rw [List.ofFn_succ]
    simp

private theorem ofFn_getD {K : Nat} (f : Fin K → Tensor) (r : Nat) (hr : r < K)
    (fallback : Tensor) : (List.ofFn f).getD r fallback = f ⟨r, hr⟩ := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hr), List.getElem_ofFn]
  rfl

/-- Gathering all ordered chunks of a tensor along a valid divisible dimension
reconstructs the original tensor shape. -/
private theorem allGatherPrimDimN_chunks_ofFn_shape
    (dim numParts : Nat) (x : Tensor)
    (hparts : 0 < numParts)
    (hdim : dim < x.shape.length)
    (hdiv : x.shape.getD dim 0 % numParts = 0) :
    (allGatherPrimDimN dim numParts 0
      (List.ofFn fun r : Fin numParts =>
        chunkPrimDimN dim numParts r.1 x)).shape = x.shape := by
  let chunks := List.ofFn fun r : Fin numParts => chunkPrimDimN dim numParts r.1 x
  let shardSize := x.shape.getD dim 0 / numParts
  have hchunk (r : Fin numParts) :
      (chunkPrimDimN dim numParts r.1 x).shape = x.shape.set dim shardSize := by
    exact chunkPrimDimN_shape dim numParts r.1 x x.shape rfl (Nat.ne_of_gt hparts)
  have hhead : (chunks.head?.map (fun t => t.shape)).getD [] =
      x.shape.set dim shardSize := by
    rw [show chunks = List.ofFn (fun r : Fin numParts =>
      chunkPrimDimN dim numParts r.1 x) from rfl]
    rw [ofFn_head_shape hparts]
    exact hchunk ⟨0, hparts⟩
  rw [allGatherPrimDimN_shape dim numParts chunks (x.shape.set dim shardSize) hhead]
  rw [getD_set_self_generic x.shape dim shardSize hdim]
  have hdvd : numParts ∣ x.shape.getD dim 0 := Nat.dvd_of_mod_eq_zero hdiv
  have hmul : shardSize * numParts = x.shape.getD dim 0 := Nat.div_mul_cancel hdvd
  rw [hmul, List.set_set]
  exact List.set_getD_self x.shape dim

/-- Gathering the ordered `numParts` chunks of a tensor along any valid,
divisible dimension reconstructs the tensor exactly. -/
theorem allGatherPrimDimN_chunks_ofFn
    (dim numParts : Nat) (x : Tensor)
    (hparts : 0 < numParts)
    (hdim : dim < x.shape.length)
    (hdiv : x.shape.getD dim 0 % numParts = 0) :
    allGatherPrimDimN dim numParts 0
      (List.ofFn fun r : Fin numParts =>
        chunkPrimDimN dim numParts r.1 x) = x := by
  classical
  let sh := x.shape
  let dimSize := sh.getD dim 0
  let shardSize := dimSize / numParts
  let postStride := (sh.drop (dim + 1)).foldl (· * ·) 1
  let preDim := (sh.take dim).foldl (· * ·) 1
  let chunks := List.ofFn fun r : Fin numParts =>
    chunkPrimDimN dim numParts r.1 x
  have hshape : (allGatherPrimDimN dim numParts 0 chunks).shape = sh := by
    exact allGatherPrimDimN_chunks_ofFn_shape dim numParts x hparts hdim hdiv
  have hchunk (r : Fin numParts) :
      (chunkPrimDimN dim numParts r.1 x).shape = sh.set dim shardSize := by
    exact chunkPrimDimN_shape dim numParts r.1 x sh rfl (Nat.ne_of_gt hparts)
  have hhead : (chunks.head?.map (fun t => t.shape)).getD [] =
      sh.set dim shardSize := by
    rw [show chunks = List.ofFn (fun r : Fin numParts =>
      chunkPrimDimN dim numParts r.1 x) from rfl]
    rw [ofFn_head_shape hparts]
    exact hchunk ⟨0, hparts⟩
  have hpost_set : ((sh.set dim shardSize).drop (dim + 1)).foldl (· * ·) 1 =
      postStride := by
    rw [List.drop_set_of_lt (Nat.lt_succ_self dim)]
  have hget_set : (sh.set dim shardSize).getD dim 0 = shardSize :=
    getD_set_self_generic sh dim shardSize hdim
  have hdvd : numParts ∣ dimSize := Nat.dvd_of_mod_eq_zero hdiv
  have hmul : shardSize * numParts = dimSize := Nat.div_mul_cancel hdvd
  have hprod : prodShape sh = preDim * dimSize * postStride :=
    prodShape_split_generic sh dim hdim
  apply Tensor.ext (by simpa [chunks, sh] using hshape)
  intro idx hidx
  have hidxX : idx < prodShape sh := by
    rw [← hshape]
    exact hidx
  have htotal : 0 < preDim * dimSize * postStride := by
    rw [← hprod]
    omega
  have hpre_pos : 0 < preDim := by
    by_contra h
    have hz : preDim = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.zero_mul, Nat.zero_mul] at htotal
    omega
  have hdim_pos : 0 < dimSize := by
    by_contra h
    have hz : dimSize = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero, Nat.zero_mul] at htotal
    omega
  have hpost_pos : 0 < postStride := by
    by_contra h
    have hz : postStride = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at htotal
    omega
  have hshard_pos : 0 < shardSize := by
    by_contra h
    have hz : shardSize = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.zero_mul] at hmul
    omega
  have hdimStride_pos : 0 < dimSize * postStride := Nat.mul_pos hdim_pos hpost_pos
  have hshardStride_pos : 0 < shardSize * postStride :=
    Nat.mul_pos hshard_pos hpost_pos
  let preIdx := idx / (dimSize * postStride)
  let remainder := idx % (dimSize * postStride)
  let jFull := remainder / postStride
  let k := remainder % postStride
  let rank := jFull / shardSize
  let jLocal := jFull % shardSize
  have hremainder : remainder < dimSize * postStride :=
    Nat.mod_lt idx hdimStride_pos
  have hpreIdx : preIdx < preDim := by
    apply Nat.div_lt_of_lt_mul
    calc
      idx < preDim * dimSize * postStride := by rw [← hprod]; exact hidxX
      _ = dimSize * postStride * preDim := by ring
  have hjFull : jFull < dimSize := by
    apply Nat.div_lt_of_lt_mul
    simpa [Nat.mul_comm] using hremainder
  have hk : k < postStride := Nat.mod_lt remainder hpost_pos
  have hrank : rank < numParts := by
    apply Nat.div_lt_of_lt_mul
    rw [hmul]
    exact hjFull
  have hjLocal : jLocal < shardSize := Nat.mod_lt jFull hshard_pos
  have htop : preIdx * (dimSize * postStride) + remainder = idx := by
    simpa [preIdx, remainder, Nat.mul_comm] using
      Nat.div_add_mod idx (dimSize * postStride)
  have hmid : jFull * postStride + k = remainder := by
    simpa [jFull, k, Nat.mul_comm] using Nat.div_add_mod remainder postStride
  have hjdecomp : rank * shardSize + jLocal = jFull := by
    simpa [rank, jLocal, Nat.mul_comm] using Nat.div_add_mod jFull shardSize
  have hidx_decomp :
      preIdx * (dimSize * postStride) +
          (rank * shardSize + jLocal) * postStride + k = idx := by
    calc
      preIdx * (dimSize * postStride) +
          (rank * shardSize + jLocal) * postStride + k
          = preIdx * (dimSize * postStride) + (jFull * postStride + k) := by
              rw [hjdecomp]
              ring
      _ = preIdx * (dimSize * postStride) + remainder := by rw [hmid]
      _ = idx := htop
  have hlocal_low : jLocal * postStride + k < shardSize * postStride := by
    calc
      jLocal * postStride + k < jLocal * postStride + postStride :=
        Nat.add_lt_add_left hk _
      _ = (jLocal + 1) * postStride := by ring
      _ ≤ shardSize * postStride := Nat.mul_le_mul_right postStride hjLocal
  have hlocal_idx : preIdx * (shardSize * postStride) +
      jLocal * postStride + k < preDim * shardSize * postStride := by
    rw [show preIdx * (shardSize * postStride) + jLocal * postStride + k =
      (jLocal * postStride + k) + (shardSize * postStride) * preIdx by ring]
    calc
      (jLocal * postStride + k) + (shardSize * postStride) * preIdx
          < (shardSize * postStride) + (shardSize * postStride) * preIdx :=
            Nat.add_lt_add_right hlocal_low _
      _ = (preIdx + 1) * (shardSize * postStride) := by ring
      _ ≤ preDim * (shardSize * postStride) :=
        Nat.mul_le_mul_right (shardSize * postStride) hpreIdx
      _ = preDim * shardSize * postStride := by ring
  have hhead_raw :
      (((List.ofFn fun r : Fin numParts => chunkPrimDimN dim numParts r.1 x).head?).map
        (fun t => t.shape)).getD [] = sh.set dim shardSize := by
    simpa [chunks] using hhead
  rw [valAt_of_lt _ idx hidx, valAt_of_lt _ idx hidxX]
  unfold allGatherPrimDimN
  simp only [hhead_raw, Tensor.mkShape, hpost_set, hget_set, hmul,
    Nat.ne_of_gt hdimStride_pos, Nat.ne_of_gt hpost_pos,
    Nat.ne_of_gt hshard_pos, ite_false]
  change valAt
      ((List.ofFn fun r : Fin numParts => chunkPrimDimN dim numParts r.1 x).getD
        rank (zeroTensor (sh.set dim shardSize)))
      (preIdx * (shardSize * postStride) + jLocal * postStride + k) =
    x.val ⟨idx, hidxX⟩
  rw [ofFn_getD (fun r : Fin numParts => chunkPrimDimN dim numParts r.1 x)
    rank hrank (zeroTensor (sh.set dim shardSize))]
  have hchunk_bound :
      preIdx * (shardSize * postStride) + jLocal * postStride + k <
        prodShape (chunkPrimDimN dim numParts rank x).shape := by
    rw [hchunk ⟨rank, hrank⟩, prodShape_set_generic sh dim shardSize hdim]
    exact hlocal_idx
  rw [valAt_of_lt _ _ hchunk_bound]
  have hdivShard :
      (preIdx * (shardSize * postStride) + jLocal * postStride + k) /
          (shardSize * postStride) = preIdx := by
    rw [show preIdx * (shardSize * postStride) + jLocal * postStride + k =
      (jLocal * postStride + k) + (shardSize * postStride) * preIdx by ring,
      Nat.add_mul_div_left _ _ hshardStride_pos,
      Nat.div_eq_of_lt hlocal_low, Nat.zero_add]
  have hmodShard :
      (preIdx * (shardSize * postStride) + jLocal * postStride + k) %
          (shardSize * postStride) = jLocal * postStride + k := by
    rw [show preIdx * (shardSize * postStride) + jLocal * postStride + k =
      (jLocal * postStride + k) + (shardSize * postStride) * preIdx by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlocal_low]
  have hdivPost : (jLocal * postStride + k) / postStride = jLocal := by
    rw [show jLocal * postStride + k = k + postStride * jLocal by ring,
      Nat.add_mul_div_left _ _ hpost_pos, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hmodPost : (jLocal * postStride + k) % postStride = k := by
    rw [show jLocal * postStride + k = k + postStride * jLocal by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, show x.shape = sh from rfl,
    Nat.ne_of_gt hparts, ite_false,
    show (sh.drop (dim + 1)).foldl (· * ·) 1 = postStride from rfl,
    show sh.getD dim 0 = dimSize from rfl,
    show dimSize / numParts = shardSize from rfl,
    Nat.mod_eq_of_lt hrank,
    Nat.ne_of_gt hshardStride_pos, Nat.ne_of_gt hpost_pos]
  rw [hdivShard, hmodShard, hdivPost, hmodPost]
  rw [hidx_decomp]
  exact valAt_of_lt x idx hidxX

/-- Ordered AllToAll rank outputs, indexed by the source-list length, reconstruct
on `odim` the full tensor previously gathered on `idim`. -/
theorem allGatherPrimDimN_allToAllPrimWithDims_ofFn
    (idim odim : Nat) (xs : List Tensor)
    (hparts : 0 < xs.length)
    (hodim : odim < (allGatherPrimDimN idim xs.length 0 xs).shape.length)
    (hdiv : (allGatherPrimDimN idim xs.length 0 xs).shape.getD odim 0 %
      xs.length = 0) :
    allGatherPrimDimN odim xs.length 0
      (List.ofFn fun r : Fin xs.length =>
        allToAllPrimWithDims xs.length r.1 xs idim odim) =
      allGatherPrimDimN idim xs.length 0 xs := by
  simpa only [allToAllPrimWithDims] using
    allGatherPrimDimN_chunks_ofFn odim xs.length
      (allGatherPrimDimN idim xs.length 0 xs) hparts hodim hdiv

#check allGatherPrimDimN_chunks_ofFn
#print axioms allGatherPrimDimN_chunks_ofFn
#check allGatherPrimDimN_allToAllPrimWithDims_ofFn
#print axioms allGatherPrimDimN_allToAllPrimWithDims_ofFn

end TrainVerify.Denote
