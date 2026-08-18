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


end TrainVerify.Denote
