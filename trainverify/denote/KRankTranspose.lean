import denote.Denote

namespace TrainVerify.Denote

set_option maxHeartbeats 500000 in
theorem transpose12_index_lt
    (d0 d1 d2 d3 idx : Nat) (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) (hd3 : d3 ≠ 0)
    (hidx : idx < d0*d2*d1*d3) :
    idx / (d2*d1*d3) * (d1*d2*d3)
        + idx % (d2*d1*d3) % (d1*d3) / d3 * (d2*d3)
        + idx % (d2*d1*d3) / (d1*d3) * d3
        + idx % (d2*d1*d3) % (d1*d3) % d3 < d0*d1*d2*d3 := by
  have p1 : 0 < d1 := Nat.pos_of_ne_zero hd1
  have p2 : 0 < d2 := Nat.pos_of_ne_zero hd2
  have p3 : 0 < d3 := Nat.pos_of_ne_zero hd3
  have p13 : 0 < d1*d3 := Nat.mul_pos p1 p3
  have p213 : 0 < d2*d1*d3 := by positivity
  have hidx' : idx < (d2*d1*d3) * d0 := by nlinarith
  have hq : idx / (d2*d1*d3) < d0 := Nat.div_lt_of_lt_mul hidx'
  have hi2 : idx % (d2*d1*d3) / (d1*d3) < d2 := by
    apply Nat.div_lt_of_lt_mul
    have := Nat.mod_lt idx p213
    nlinarith
  have hi1 : idx % (d2*d1*d3) % (d1*d3) / d3 < d1 := by
    apply Nat.div_lt_of_lt_mul
    have := Nat.mod_lt (idx % (d2*d1*d3)) p13
    nlinarith
  have hi3 : idx % (d2*d1*d3) % (d1*d3) % d3 < d3 := Nat.mod_lt _ p3
  have htail2 : idx % (d2*d1*d3) / (d1*d3) * d3 +
      idx % (d2*d1*d3) % (d1*d3) % d3 < d2*d3 := by nlinarith
  have htail1 : idx % (d2*d1*d3) % (d1*d3) / d3 * (d2*d3) +
      idx % (d2*d1*d3) / (d1*d3) * d3 +
      idx % (d2*d1*d3) % (d1*d3) % d3 < d1*(d2*d3) := by nlinarith
  nlinarith

set_option maxHeartbeats 500000 in
theorem allGatherPrimDimN_2_valAt_rank4
    (xs : List Tensor) (K d0 d1 d2 d3 idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0,d1,d2,d3])
    (hK : K ≠ 0) (hd2 : d2 ≠ 0) (hd3 : d3 ≠ 0)
    (hidx : idx < d0*d1*(d2*K)*d3) :
    valAt (allGatherPrimDimN 2 K 0 xs) idx =
      valAt (xs.getD (((idx % (d2*K*d3)) / d3) / d2)
        (zeroTensor [d0,d1,d2,d3]))
        (idx / (d2*K*d3) * (d2*d3) +
          ((idx % (d2*K*d3) / d3) % d2) * d3 + idx % (d2*K*d3) % d3) := by
  have hshape : (allGatherPrimDimN 2 K 0 xs).shape = [d0,d1,d2*K,d3] := by
    rw [allGatherPrimDimN_shape 2 K xs [d0,d1,d2,d3] hhead]
    simp [List.set, List.getD]
  have hp : idx < prodShape (allGatherPrimDimN 2 K 0 xs).shape := by
    rw [hshape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hp]
  have hmul : d2 * K ≠ 0 := Nat.mul_ne_zero hd2 hK
  have hblock : d2 * d3 ≠ 0 := Nat.mul_ne_zero hd2 hd3
  have hfull : (d2 * K) * d3 ≠ 0 := Nat.mul_ne_zero hmul hd3
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceAdd, Nat.one_mul, Nat.mul_one,
    Nat.div_one, Nat.mod_one, Nat.add_zero, hmul, hd2, hd3, hblock, hfull,
    Nat.one_ne_zero, if_false]


set_option maxHeartbeats 500000 in
theorem allGatherPrimDimN_1_valAt_rank4
    (xs : List Tensor) (K d0 d1 d2 d3 idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0,d1,d2,d3])
    (hK : K ≠ 0) (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) (hd3 : d3 ≠ 0)
    (hidx : idx < d0*(d1*K)*d2*d3) :
    valAt (allGatherPrimDimN 1 K 0 xs) idx =
      valAt (xs.getD (((idx % (d1*K*(d2*d3))) / (d2*d3)) / d1)
        (zeroTensor [d0,d1,d2,d3]))
        (idx / (d1*K*(d2*d3)) * (d1*(d2*d3)) +
          ((idx % (d1*K*(d2*d3)) / (d2*d3)) % d1) * (d2*d3) +
          idx % (d1*K*(d2*d3)) % (d2*d3)) := by
  have hshape : (allGatherPrimDimN 1 K 0 xs).shape = [d0,d1*K,d2,d3] := by
    rw [allGatherPrimDimN_shape 1 K xs [d0,d1,d2,d3] hhead]
    simp [List.set, List.getD]
  have hp : idx < prodShape (allGatherPrimDimN 1 K 0 xs).shape := by
    rw [hshape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hp]
  have hmul : d1 * K ≠ 0 := Nat.mul_ne_zero hd1 hK
  have hinner : d2 * d3 ≠ 0 := Nat.mul_ne_zero hd2 hd3
  have hblock : d1 * (d2 * d3) ≠ 0 := Nat.mul_ne_zero hd1 hinner
  have hfull : (d1 * K) * (d2 * d3) ≠ 0 := Nat.mul_ne_zero hmul hinner
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceAdd, Nat.one_mul, Nat.mul_one,
    Nat.div_one, Nat.mod_one, Nat.add_zero, hmul, hd1, hd2, hd3, hinner,
    hblock, hfull, Nat.one_ne_zero, if_false]


set_option maxHeartbeats 500000 in
theorem allGatherPrimDimN_3_valAt_rank4
    (xs : List Tensor) (K d0 d1 d2 d3 idx : Nat)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0,d1,d2,d3])
    (hK : K ≠ 0) (hd3 : d3 ≠ 0)
    (hidx : idx < d0*d1*d2*(d3*K)) :
    valAt (allGatherPrimDimN 3 K 0 xs) idx =
      valAt (xs.getD ((idx % (d3*K)) / d3) (zeroTensor [d0,d1,d2,d3]))
        (idx / (d3*K) * d3 + idx % (d3*K) % d3) := by
  have hshape : (allGatherPrimDimN 3 K 0 xs).shape = [d0,d1,d2,d3*K] := by
    rw [allGatherPrimDimN_shape 3 K xs [d0,d1,d2,d3] hhead]
    simp [List.set, List.getD]
  have hp : idx < prodShape (allGatherPrimDimN 3 K 0 xs).shape := by
    rw [hshape]
    simpa [prodShape, Nat.mul_assoc] using hidx
  rw [valAt_of_lt _ _ hp]
  have hmul : d3 * K ≠ 0 := Nat.mul_ne_zero hd3 hK
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.reduceAdd, Nat.mul_one,
    Nat.div_one, Nat.mod_one, Nat.add_zero, hmul, hd3, Nat.one_ne_zero, if_false]


set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_allGather_dim3_rank4
    (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ [])
    (hshapes : ∀ x ∈ xs, x.shape = [d0,d1,d2,d3]) :
    transposeAxes 1 2 (allGatherPrimDimN 3 xs.length 0 xs) =
      allGatherPrimDimN 3 xs.length 0 (xs.map (transposeAxes 1 2)) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0,d1,d2,d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmaphead : (((xs.map (transposeAxes 1 2)).head?.map (fun t => t.shape)).getD []) =
      [d0,d2,d1,d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest =>
      have hx := hshapes x (by simp)
      simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hK : xs.length ≠ 0 := by
    intro hz
    apply hne
    exact List.length_eq_zero_iff.mp hz
  have hgshape : (allGatherPrimDimN 3 xs.length 0 xs).shape =
      [d0,d1,d2,d3*xs.length] := by
    rw [allGatherPrimDimN_shape 3 xs.length xs [d0,d1,d2,d3] hhead]
    simp [List.set, List.getD]
  have hlshape : (transposeAxes 1 2 (allGatherPrimDimN 3 xs.length 0 xs)).shape =
      [d0,d2,d1,d3*xs.length] := by
    simp [transposeAxes, Tensor.mkShape, hgshape, listSwapAt, List.getD, List.set]
  have hrshape : (allGatherPrimDimN 3 xs.length 0 (xs.map (transposeAxes 1 2))).shape =
      [d0,d2,d1,d3*xs.length] := by
    rw [allGatherPrimDimN_shape 3 xs.length _ [d0,d2,d1,d3] hmaphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < d0*d2*d1*(d3*xs.length) := by
    simpa [hlshape, prodShape, Nat.mul_assoc] using hidx
  by_cases hd1 : d1 = 0
  · subst d1
    simp at hbound
  by_cases hd2 : d2 = 0
  · subst d2
    simp at hbound
  by_cases hd3 : d3 = 0
  · subst d3
    simp at hbound
  rw [transposeAxes_1_2_valAt_gen _ d0 d1 d2 (d3*xs.length) idx hgshape
    hd1 hd2 (Nat.mul_ne_zero hd3 hK) hbound]
  let sourceIdx := idx / (d2*d1*(d3*xs.length)) * (d1*d2*(d3*xs.length))
        + idx % (d2*d1*(d3*xs.length)) % (d1*(d3*xs.length)) / (d3*xs.length) * (d2*(d3*xs.length))
        + idx % (d2*d1*(d3*xs.length)) / (d1*(d3*xs.length)) * (d3*xs.length)
        + idx % (d2*d1*(d3*xs.length)) % (d1*(d3*xs.length)) % (d3*xs.length)
  rw [allGatherPrimDimN_3_valAt_rank4 xs xs.length d0 d1 d2 d3 sourceIdx hhead hK hd3 (by
    dsimp [sourceIdx]
    exact transpose12_index_lt d0 d1 d2 (d3*xs.length) idx hd1 hd2
      (Nat.mul_ne_zero hd3 hK) hbound)]
  rw [allGatherPrimDimN_3_valAt_rank4 (xs.map (transposeAxes 1 2)) xs.length d0 d2 d1 d3 idx
    hmaphead hK hd3 hbound]
  let r := idx % (d3*xs.length) / d3
  let loc := idx / (d3*xs.length) * d3 + idx % (d3*xs.length) % d3
  have hr : r < xs.length := by
    dsimp [r]
    apply Nat.div_lt_of_lt_mul
    have hm := Nat.mod_lt idx (Nat.mul_pos (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hK))
    nlinarith
  have hselect : (xs.map (transposeAxes 1 2)).getD r (zeroTensor [d0,d2,d1,d3]) =
      transposeAxes 1 2 (xs.getD r (zeroTensor [d0,d1,d2,d3])) := by
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_eq_getElem hr]
    simp
  rw [hselect]
  have hpiece : (xs.getD r (zeroTensor [d0,d1,d2,d3])).shape = [d0,d1,d2,d3] := by
    unfold List.getD
    rw [List.getElem?_eq_getElem hr]
    simpa using hshapes xs[r] (List.getElem_mem ..)
  have hloc : loc < d0*d2*d1*d3 := by
    dsimp [loc]
    have hp : 0 < d3*xs.length := Nat.mul_pos (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hK)
    have hq : idx / (d3*xs.length) < d0*d2*d1 := by
      apply Nat.div_lt_of_lt_mul
      nlinarith
    have hm := Nat.mod_lt idx hp
    have hm3 := Nat.mod_lt (idx % (d3*xs.length)) (Nat.pos_of_ne_zero hd3)
    nlinarith
  rw [transposeAxes_1_2_valAt_gen _ d0 d1 d2 d3 loc hpiece hd1 hd2 hd3 hloc]
  let E := d3 * xs.length
  let a := idx / (d2 * d1 * E)
  let b := idx % (d2 * d1 * E) % (d1 * E) / E
  let c := idx % (d2 * d1 * E) / (d1 * E)
  let t := idx % (d2 * d1 * E) % (d1 * E) % E
  have hE : 0 < E := Nat.mul_pos (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hK)
  have ht : t < E := by
    exact Nat.mod_lt _ hE
  have hsrc : sourceIdx = E * ((a * d1 + b) * d2 + c) + t := by
    dsimp [sourceIdx, E, a, b, c, t]
    ring
  have htidx : t = idx % E := by
    dsimp [t]
    calc
      idx % (d2 * d1 * E) % (d1 * E) % E =
          idx % (d2 * d1 * E) % E :=
        Nat.mod_mod_of_dvd _ ⟨d1, by ring⟩
      _ = idx % E := Nat.mod_mod_of_dvd _ ⟨d2 * d1, by ring⟩
  have hsource_div : sourceIdx / E = (a * d1 + b) * d2 + c := by
    rw [hsrc, Nat.mul_add_div hE, Nat.div_eq_of_lt ht, Nat.add_zero]
  have hsource_mod : sourceIdx % E = t := by
    rw [hsrc, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt ht]
  change valAt (xs.getD (sourceIdx % E / d3) (zeroTensor [d0,d1,d2,d3]))
      (sourceIdx / E * d3 + sourceIdx % E % d3) = _
  let q := idx / E
  let z := idx % E % d3
  have hz : z < d3 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd3)
  have ha : a = q / (d2 * d1) := by
    dsimp [a, q]
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  have hbase : idx % (d2 * d1 * E) / E = q % (d2 * d1) := by
    dsimp [q]
    simpa only [Nat.mul_assoc] using Nat.mod_mul_left_div_self idx E (d2 * d1)
  have hb : b = q % (d2 * d1) % d1 := by
    dsimp [b]
    rw [Nat.mod_mul_left_div_self]
    exact congrArg (fun n => n % d1) hbase
  have hc : c = q % (d2 * d1) / d1 := by
    dsimp [c]
    rw [show d1 * E = E * d1 by ring, ← Nat.div_div_eq_div_mul]
    exact congrArg (fun n => n / d1) hbase
  have append_div (u N w d : Nat) (hd : 0 < d) (hw : w < d) :
      (u * d + w) / (N * d) = u / N := by
    rw [show N * d = d * N by ring, ← Nat.div_div_eq_div_mul,
      show u * d = d * u by ring, Nat.mul_add_div hd, Nat.div_eq_of_lt hw,
      Nat.add_zero]
  have append_mod (u N w d : Nat) (hN : 0 < N) (hd : 0 < d) (hw : w < d) :
      (u * d + w) % (N * d) = (u % N) * d + w := by
    have hur : u % N < N := Nat.mod_lt _ hN
    have hrem : (u % N) * d + w < N * d := by nlinarith
    have hu : N * (u / N) + u % N = u := Nat.div_add_mod u N
    calc
      (u * d + w) % (N * d) =
          ((N * (u / N) + u % N) * d + w) % (N * d) := by rw [hu]
      _ = ((N * d) * (u / N) + ((u % N) * d + w)) % (N * d) := by
        congr 1
        ring
      _ = ((u % N) * d + w) % (N * d) := Nat.mul_add_mod_self_left _ _ _
      _ = (u % N) * d + w := Nat.mod_eq_of_lt hrem
  have append_div_self (u w d : Nat) (hd : 0 < d) (hw : w < d) :
      (u * d + w) / d = u := by
    rw [show u * d = d * u by ring, Nat.mul_add_div hd, Nat.div_eq_of_lt hw,
      Nat.add_zero]
  have append_mod_self (u w d : Nat) (hw : w < d) :
      (u * d + w) % d = w := by
    rw [show u * d = d * u by ring, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt hw]
  rw [hsource_div, hsource_mod, htidx, ha, hb, hc]
  dsimp [r, loc, E, q, z]
  congr 1
  rw [append_div _ (d2 * d1) _ d3 (Nat.pos_of_ne_zero hd3) hz]
  rw [append_mod _ (d2 * d1) _ d3
    (Nat.mul_pos (Nat.pos_of_ne_zero hd2) (Nat.pos_of_ne_zero hd1))
    (Nat.pos_of_ne_zero hd3) hz]
  rw [append_mod _ d1 _ d3 (Nat.pos_of_ne_zero hd1)
    (Nat.pos_of_ne_zero hd3) hz]
  rw [append_div_self _ z d3 (Nat.pos_of_ne_zero hd3) hz]
  rw [append_div _ d1 z d3 (Nat.pos_of_ne_zero hd3) hz]
  rw [append_mod_self _ z d3 hz]
  ring


set_option maxHeartbeats 3200000 in
theorem transposeAxes_1_2_allGather_dim2_to_dim1_rank4
    (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ [])
    (hshapes : ∀ x ∈ xs, x.shape = [d0,d1,d2,d3]) :
    transposeAxes 1 2 (allGatherPrimDimN 2 xs.length 0 xs) =
      allGatherPrimDimN 1 xs.length 0 (xs.map (transposeAxes 1 2)) := by
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0,d1,d2,d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmaphead : (((xs.map (transposeAxes 1 2)).head?.map (fun t => t.shape)).getD []) =
      [d0,d2,d1,d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest =>
      have hx := hshapes x (by simp)
      simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hK : xs.length ≠ 0 := by
    intro hz
    apply hne
    exact List.length_eq_zero_iff.mp hz
  have hgshape : (allGatherPrimDimN 2 xs.length 0 xs).shape =
      [d0,d1,d2*xs.length,d3] := by
    rw [allGatherPrimDimN_shape 2 xs.length xs [d0,d1,d2,d3] hhead]
    simp [List.set, List.getD]
  have hlshape : (transposeAxes 1 2 (allGatherPrimDimN 2 xs.length 0 xs)).shape =
      [d0,d2*xs.length,d1,d3] := by
    simp [transposeAxes, Tensor.mkShape, hgshape, listSwapAt, List.getD, List.set]
  have hrshape : (allGatherPrimDimN 1 xs.length 0 (xs.map (transposeAxes 1 2))).shape =
      [d0,d2*xs.length,d1,d3] := by
    rw [allGatherPrimDimN_shape 1 xs.length _ [d0,d2,d1,d3] hmaphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < d0*(d2*xs.length)*d1*d3 := by
    simpa [hlshape, prodShape, Nat.mul_assoc] using hidx
  by_cases hd1 : d1 = 0
  · subst d1
    simp at hbound
  by_cases hd2 : d2 = 0
  · subst d2
    simp at hbound
  by_cases hd3 : d3 = 0
  · subst d3
    simp at hbound
  let D := d2 * xs.length
  have hD : 0 < D := Nat.mul_pos (Nat.pos_of_ne_zero hd2) (Nat.pos_of_ne_zero hK)
  let z := idx % d3
  let q0 := idx / d3
  let b := q0 % d1
  let q1 := q0 / d1
  let g := q1 % D
  let a := q1 / D
  have hz : z < d3 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd3)
  have hb : b < d1 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd1)
  have hg : g < D := Nat.mod_lt _ hD
  have hcoords : idx = (((a * D + g) * d1 + b) * d3 + z) := by
    have h0 : q0 * d3 + z = idx := by
      simpa [q0, z, Nat.mul_comm] using Nat.div_add_mod idx d3
    have h1 : q1 * d1 + b = q0 := by
      simpa [q1, b, Nat.mul_comm] using Nat.div_add_mod q0 d1
    have h2 : a * D + g = q1 := by
      simpa [a, g, Nat.mul_comm] using Nat.div_add_mod q1 D
    rw [← h0, ← h1, ← h2]
  let r := g / d2
  let p := g % d2
  have hp : p < d2 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd2)
  have hgp : r * d2 + p = g := by
    simpa [r, p, Nat.mul_comm] using Nat.div_add_mod g d2
  have hr : r < xs.length := by
    apply Nat.div_lt_of_lt_mul
    simpa [D, Nat.mul_comm] using hg
  have hselect : (xs.map (transposeAxes 1 2)).getD r (zeroTensor [d0,d2,d1,d3]) =
      transposeAxes 1 2 (xs.getD r (zeroTensor [d0,d1,d2,d3])) := by
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_eq_getElem hr]
    simp
  have hpiece : (xs.getD r (zeroTensor [d0,d1,d2,d3])).shape = [d0,d1,d2,d3] := by
    unfold List.getD
    rw [List.getElem?_eq_getElem hr]
    simpa using hshapes xs[r] (List.getElem_mem ..)
  have haeq : a = idx / (D*d1*d3) := by
    dsimp [a, q1, q0]
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    congr 1
    ring
  have ha : a < d0 := by
    rw [haeq]
    apply Nat.div_lt_of_lt_mul
    simpa [D, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbound
  have hidxCanonical :
      (((a * D + (r*d2+p)) * d1 + b) * d3 + z) < d0*D*d1*d3 := by
    rw [hgp, ← hcoords]
    simpa [D, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbound
  rw [hcoords, ← hgp]
  have hglobal : r*d2+p < D := by simpa [hgp] using hg
  have append_div (u N w d : Nat) (hd : 0 < d) (hw : w < d) :
      (u*d+w)/(N*d)=u/N := by
    rw [show N*d=d*N by ring, ← Nat.div_div_eq_div_mul,
      show u*d=d*u by ring, Nat.mul_add_div hd, Nat.div_eq_of_lt hw, Nat.add_zero]
  have append_mod (u N w d : Nat) (hN : 0 < N) (hd : 0 < d) (hw : w < d) :
      (u*d+w)%(N*d)=(u%N)*d+w := by
    have hur := Nat.mod_lt u hN
    have hrem : (u%N)*d+w < N*d := by nlinarith
    have hu : N*(u/N)+u%N=u := Nat.div_add_mod u N
    calc
      (u*d+w)%(N*d)=((N*(u/N)+u%N)*d+w)%(N*d) := by rw [hu]
      _=((N*d)*(u/N)+((u%N)*d+w))%(N*d) := by congr 1 <;> ring
      _=((u%N)*d+w)%(N*d) := Nat.mul_add_mod_self_left _ _ _
      _=(u%N)*d+w := Nat.mod_eq_of_lt hrem
  have append_div_self (u w d : Nat) (hd : 0 < d) (hw : w < d) :
      (u*d+w)/d=u := by
    rw [show u*d=d*u by ring, Nat.mul_add_div hd, Nat.div_eq_of_lt hw, Nat.add_zero]
  have append_mod_self (u w d : Nat) (hw : w < d) :
      (u*d+w)%d=w := by
    rw [show u*d=d*u by ring, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hw]
  let out := (((a*D+(r*d2+p))*d1+b)*d3+z)
  have hout_div : out/(D*d1*d3)=a := by
    dsimp [out]
    rw [show D*d1*d3=(D*d1)*d3 by ring,
      append_div _ (D*d1) z d3 (Nat.pos_of_ne_zero hd3) hz,
      append_div _ D b d1 (Nat.pos_of_ne_zero hd1) hb,
      append_div_self a (r*d2+p) D hD hglobal]
  have hUmod : (((a*D+(r*d2+p))*d1+b)%(D*d1))=(r*d2+p)*d1+b := by
    rw [append_mod _ D b d1 hD (Nat.pos_of_ne_zero hd1) hb,
      append_mod_self a (r*d2+p) D hglobal]
  have hout_g : out%(D*d1*d3)/(d1*d3)=r*d2+p := by
    dsimp [out]
    rw [show D*d1*d3=(D*d1)*d3 by ring,
      append_mod _ (D*d1) z d3 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd1))
        (Nat.pos_of_ne_zero hd3) hz,
      append_div _ d1 z d3 (Nat.pos_of_ne_zero hd3) hz,
      hUmod, append_div_self (r*d2+p) b d1 (Nat.pos_of_ne_zero hd1) hb]
  have hout_inner : out%(D*d1*d3)%(d1*d3)=b*d3+z := by
    dsimp [out]
    rw [show D*d1*d3=(D*d1)*d3 by ring,
      append_mod _ (D*d1) z d3 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd1))
        (Nat.pos_of_ne_zero hd3) hz,
      append_mod _ d1 z d3 (Nat.pos_of_ne_zero hd1)
        (Nat.pos_of_ne_zero hd3) hz,
      hUmod, append_mod_self (r*d2+p) b d1 hb]
  have hout_b : out%(D*d1*d3)%(d1*d3)/d3=b := by
    rw [hout_inner, append_div_self b z d3 (Nat.pos_of_ne_zero hd3) hz]
  have hout_z : out%(D*d1*d3)%(d1*d3)%d3=z := by
    rw [hout_inner, append_mod_self b z d3 hz]
  have htranspose :
      valAt (transposeAxes 1 2 (allGatherPrimDimN 2 xs.length 0 xs))
          (((a * D + (r*d2+p)) * d1 + b) * d3 + z) =
        valAt (allGatherPrimDimN 2 xs.length 0 xs)
          (((a*d1+b)*D+(r*d2+p))*d3+z) := by
    rw [transposeAxes_1_2_valAt_gen _ d0 d1 D d3
      (((a * D + (r*d2+p)) * d1 + b) * d3 + z) hgshape hd1
      (Nat.ne_of_gt hD) hd3 hidxCanonical]
    change _ = valAt _ _
    rw [hout_div, hout_b, hout_g, hout_z]
    congr 1
    ring
  rw [htranspose]
  have hright :
      valAt (allGatherPrimDimN 1 xs.length 0 (xs.map (transposeAxes 1 2)))
          (((a * D + (r*d2+p)) * d1 + b) * d3 + z) =
        valAt ((xs.map (transposeAxes 1 2)).getD r (zeroTensor [d0,d2,d1,d3]))
          (((a*d2+p)*d1+b)*d3+z) := by
    rw [allGatherPrimDimN_1_valAt_rank4 (xs.map (transposeAxes 1 2)) xs.length
      d0 d2 d1 d3 (((a * D + (r*d2+p)) * d1 + b) * d3 + z)
      hmaphead hK hd2 hd1 hd3 (by simpa [D, Nat.mul_assoc] using hidxCanonical)]
    have hsel : (r*d2+p)/d2=r := append_div_self r p d2
      (Nat.pos_of_ne_zero hd2) hp
    have hrem : (r*d2+p)%d2=p := append_mod_self r p d2 hp
    change valAt _ _ = valAt _ _
    rw [show d2*xs.length=D by rfl, show D*(d1*d3)=D*d1*d3 by ring,
      hout_g, hsel, hout_div, hrem, hout_inner]
    congr 1
    ring
  rw [hright]
  have hleft :
      valAt (allGatherPrimDimN 2 xs.length 0 xs)
          (((a*d1+b)*D+(r*d2+p))*d3+z) =
        valAt (xs.getD r (zeroTensor [d0,d1,d2,d3]))
          (((a*d1+b)*d2+p)*d3+z) := by
    rw [allGatherPrimDimN_2_valAt_rank4 xs xs.length d0 d1 d2 d3 _
      hhead hK hd2 hd3 (by
        have houter : a*d1+b < d0*d1 := by
          have hstep : a*d1+b < (a+1)*d1 := by nlinarith
          exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d1 (Nat.succ_le_iff.mpr ha))
        have hprefix : (a*d1+b)*D+(r*d2+p) < (d0*d1)*D := by
          have hstep : (a*d1+b)*D+(r*d2+p) < ((a*d1+b)+1)*D := by nlinarith
          exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right D (Nat.succ_le_iff.mpr houter))
        have hstep : ((a*d1+b)*D+(r*d2+p))*d3+z <
            (((a*d1+b)*D+(r*d2+p))+1)*d3 := by nlinarith
        exact lt_of_lt_of_le hstep
          (Nat.mul_le_mul_right d3 (Nat.succ_le_iff.mpr hprefix)))]
    let src := (((a*d1+b)*D+(r*d2+p))*d3+z)
    have hsrc_div : src/(D*d3)=a*d1+b := by
      dsimp [src]
      rw [append_div _ D z d3 (Nat.pos_of_ne_zero hd3) hz,
        append_div_self (a*d1+b) (r*d2+p) D hD hglobal]
    have hsrc_g : src%(D*d3)/d3=r*d2+p := by
      dsimp [src]
      rw [append_mod _ D z d3 hD (Nat.pos_of_ne_zero hd3) hz,
        append_mod_self (a*d1+b) (r*d2+p) D hglobal,
        append_div_self (r*d2+p) z d3 (Nat.pos_of_ne_zero hd3) hz]
    have hsrc_z : src%(D*d3)%d3=z := by
      dsimp [src]
      rw [append_mod _ D z d3 hD (Nat.pos_of_ne_zero hd3) hz,
        append_mod_self (a*d1+b) (r*d2+p) D hglobal,
        append_mod_self (r*d2+p) z d3 hz]
    have hsel : (r*d2+p)/d2=r := append_div_self r p d2
      (Nat.pos_of_ne_zero hd2) hp
    have hrem : (r*d2+p)%d2=p := append_mod_self r p d2 hp
    change valAt _ _ = valAt _ _
    rw [show d2*xs.length=D by rfl, hsrc_g, hsel, hsrc_div, hrem, hsrc_z]
    congr 2 <;> ring
  rw [hleft, hselect]
  have hlocal : (((a * d2 + p) * d1 + b) * d3 + z) < d0*d2*d1*d3 := by
    have hab : a * d2 + p < d0 * d2 := by
      have hstep : a*d2+p < (a+1)*d2 := by nlinarith
      have hle := Nat.mul_le_mul_right d2 (Nat.succ_le_iff.mpr ha)
      exact lt_of_lt_of_le hstep hle
    have hrow : (a*d2+p)*d1+b < (d0*d2)*d1 := by
      have hstep : (a*d2+p)*d1+b < ((a*d2+p)+1)*d1 := by nlinarith
      exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d1 (Nat.succ_le_iff.mpr hab))
    nlinarith
  rw [transposeAxes_1_2_valAt_gen _ d0 d1 d2 d3
    (((a*d2+p)*d1+b)*d3+z) hpiece hd1 hd2 hd3 hlocal]
  have hlocal_div : (((a*d2+p)*d1+b)*d3+z)/(d2*d1*d3)=a := by
    rw [show d2*d1*d3=(d2*d1)*d3 by ring,
      append_div _ (d2*d1) z d3 (Nat.pos_of_ne_zero hd3) hz,
      append_div _ d2 b d1 (Nat.pos_of_ne_zero hd1) hb,
      append_div_self a p d2 (Nat.pos_of_ne_zero hd2) hp]
  have hlocal_p : (((a*d2+p)*d1+b)*d3+z)%(d2*d1*d3)/(d1*d3)=p := by
    rw [show d2*d1*d3=(d2*d1)*d3 by ring,
      append_mod _ (d2*d1) z d3
        (Nat.mul_pos (Nat.pos_of_ne_zero hd2) (Nat.pos_of_ne_zero hd1))
        (Nat.pos_of_ne_zero hd3) hz,
      append_div _ d1 z d3 (Nat.pos_of_ne_zero hd3) hz,
      append_mod _ d2 b d1 (Nat.pos_of_ne_zero hd2)
        (Nat.pos_of_ne_zero hd1) hb,
      append_mod_self a p d2 hp,
      append_div_self p b d1 (Nat.pos_of_ne_zero hd1) hb]
  have hlocal_b : (((a*d2+p)*d1+b)*d3+z)%(d2*d1*d3)%(d1*d3)/d3=b := by
    have hinner : (((a*d2+p)*d1+b)*d3+z)%(d2*d1*d3)%(d1*d3)=b*d3+z := by
      rw [show d2*d1*d3=(d2*d1)*d3 by ring,
        append_mod _ (d2*d1) z d3
          (Nat.mul_pos (Nat.pos_of_ne_zero hd2) (Nat.pos_of_ne_zero hd1))
          (Nat.pos_of_ne_zero hd3) hz,
        append_mod _ d1 z d3 (Nat.pos_of_ne_zero hd1)
          (Nat.pos_of_ne_zero hd3) hz,
        append_mod _ d2 b d1 (Nat.pos_of_ne_zero hd2)
          (Nat.pos_of_ne_zero hd1) hb,
        append_mod_self a p d2 hp, append_mod_self p b d1 hb]
    rw [hinner, append_div_self b z d3 (Nat.pos_of_ne_zero hd3) hz]
  have hlocal_z : (((a*d2+p)*d1+b)*d3+z)%(d2*d1*d3)%(d1*d3)%d3=z := by
    have hinner : (((a*d2+p)*d1+b)*d3+z)%(d2*d1*d3)%(d1*d3)=b*d3+z := by
      rw [show d2*d1*d3=(d2*d1)*d3 by ring,
        append_mod _ (d2*d1) z d3
          (Nat.mul_pos (Nat.pos_of_ne_zero hd2) (Nat.pos_of_ne_zero hd1))
          (Nat.pos_of_ne_zero hd3) hz,
        append_mod _ d1 z d3 (Nat.pos_of_ne_zero hd1)
          (Nat.pos_of_ne_zero hd3) hz,
        append_mod _ d2 b d1 (Nat.pos_of_ne_zero hd2)
          (Nat.pos_of_ne_zero hd1) hb,
        append_mod_self a p d2 hp, append_mod_self p b d1 hb]
    rw [hinner, append_mod_self b z d3 hz]
  rw [hlocal_div, hlocal_b, hlocal_p, hlocal_z]
  congr 2 <;> ring


end TrainVerify.Denote
