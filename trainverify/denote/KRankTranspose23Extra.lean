import denote.RelationCompiler

namespace TrainVerify.Denote

set_option maxHeartbeats 3200000 in
theorem transposeAxes_2_3_allGather_dim3_to_dim2_rank4
    (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ [])
    (hshapes : ∀ x ∈ xs, x.shape = [d0,d1,d2,d3]) :
    transposeAxes 2 3 (allGatherPrimDimN 3 xs.length 0 xs) =
      allGatherPrimDimN 2 xs.length 0 (xs.map (transposeAxes 2 3)) := by
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
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0,d1,d2,d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmaphead : (((xs.map (transposeAxes 2 3)).head?.map (fun t => t.shape)).getD []) =
      [d0,d1,d3,d2] := by
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
  have hlshape : (transposeAxes 2 3 (allGatherPrimDimN 3 xs.length 0 xs)).shape =
      [d0,d1,d3*xs.length,d2] := by
    simp [transposeAxes, Tensor.mkShape, hgshape, listSwapAt, List.getD, List.set]
  have hrshape : (allGatherPrimDimN 2 xs.length 0 (xs.map (transposeAxes 2 3))).shape =
      [d0,d1,d3*xs.length,d2] := by
    rw [allGatherPrimDimN_shape 2 xs.length _ [d0,d1,d3,d2] hmaphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < d0*d1*(d3*xs.length)*d2 := by
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
  let D := d3 * xs.length
  have hD : 0 < D := Nat.mul_pos (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hK)
  let p := idx % d2
  let q0 := idx / d2
  let g := q0 % D
  let q1 := q0 / D
  let b := q1 % d1
  let a := q1 / d1
  have hp : p < d2 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd2)
  have hg : g < D := Nat.mod_lt _ hD
  have hb : b < d1 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd1)
  have hcoords : idx = (((a*d1+b)*D+g)*d2+p) := by
    have h0 : q0*d2+p=idx := by
      simpa [q0, p, Nat.mul_comm] using Nat.div_add_mod idx d2
    have h1 : q1*D+g=q0 := by
      simpa [q1, g, Nat.mul_comm] using Nat.div_add_mod q0 D
    have h2 : a*d1+b=q1 := by
      simpa [a, b, Nat.mul_comm] using Nat.div_add_mod q1 d1
    rw [← h0, ← h1, ← h2]
  let r := g / d3
  let c := g % d3
  have hc : c < d3 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd3)
  have hgc : r*d3+c=g := by
    simpa [r, c, Nat.mul_comm] using Nat.div_add_mod g d3
  have hr : r < xs.length := by
    apply Nat.div_lt_of_lt_mul
    simpa [D, Nat.mul_comm] using hg
  have hselect : (xs.map (transposeAxes 2 3)).getD r (zeroTensor [d0,d1,d3,d2]) =
      transposeAxes 2 3 (xs.getD r (zeroTensor [d0,d1,d2,d3])) := by
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_eq_getElem hr]
    simp
  have hpiece : (xs.getD r (zeroTensor [d0,d1,d2,d3])).shape = [d0,d1,d2,d3] := by
    unfold List.getD
    rw [List.getElem?_eq_getElem hr]
    simpa using hshapes xs[r] (List.getElem_mem ..)
  have hcanonical : (((a*d1+b)*D+(r*d3+c))*d2+p) < d0*d1*D*d2 := by
    rw [hgc, ← hcoords]
    simpa [D, Nat.mul_assoc] using hbound
  rw [hcoords, ← hgc]
  let out := (((a*d1+b)*D+(r*d3+c))*d2+p)
  have hout_div : out/(d1*D*d2)=a := by
    dsimp [out]
    rw [show d1*D*d2=(d1*D)*d2 by ring,
      append_div _ (d1*D) p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_div _ d1 (r*d3+c) D hD (by simpa [hgc] using hg),
      append_div_self a b d1 (Nat.pos_of_ne_zero hd1) hb]
  have hout_b : out%(d1*D*d2)/(D*d2)=b := by
    dsimp [out]
    rw [show d1*D*d2=(d1*D)*d2 by ring,
      append_mod _ (d1*D) p d2 (Nat.mul_pos (Nat.pos_of_ne_zero hd1) hD)
        (Nat.pos_of_ne_zero hd2) hp,
      append_div _ D p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d1 (r*d3+c) D (Nat.pos_of_ne_zero hd1) hD (by simpa [hgc] using hg),
      append_mod_self a b d1 hb,
      append_div_self b (r*d3+c) D hD (by simpa [hgc] using hg)]
  have hinner : out%(d1*D*d2)%(D*d2)=(r*d3+c)*d2+p := by
    dsimp [out]
    rw [show d1*D*d2=(d1*D)*d2 by ring,
      append_mod _ (d1*D) p d2 (Nat.mul_pos (Nat.pos_of_ne_zero hd1) hD)
        (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ D p d2 hD (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d1 (r*d3+c) D (Nat.pos_of_ne_zero hd1) hD (by simpa [hgc] using hg),
      append_mod_self a b d1 hb, append_mod_self b (r*d3+c) D (by simpa [hgc] using hg)]
  have hout_p : out%(d1*D*d2)%(D*d2)%d2=p := by
    rw [hinner, append_mod_self (r*d3+c) p d2 hp]
  have hout_g : out%(d1*D*d2)%(D*d2)/d2=r*d3+c := by
    rw [hinner, append_div_self (r*d3+c) p d2 (Nat.pos_of_ne_zero hd2) hp]
  have htranspose :
      valAt (transposeAxes 2 3 (allGatherPrimDimN 3 xs.length 0 xs)) out =
        valAt (allGatherPrimDimN 3 xs.length 0 xs)
          (((a*d1+b)*d2+p)*D+(r*d3+c)) := by
    rw [transposeAxes_2_3_valAt_gen _ d0 d1 d2 D out hgshape hd1 hd2
      (Nat.ne_of_gt hD) (by simpa [out] using hcanonical)]
    rw [hout_div, hout_b, hout_p, hout_g]
    congr 1
    ring
  rw [htranspose]
  have ha : a < d0 := by
    rw [← hout_div]
    apply Nat.div_lt_of_lt_mul
    calc
      out < d0*d1*D*d2 := by simpa [out] using hcanonical
      _ = (d1*D*d2)*d0 := by ring
  have hleft :
      valAt (allGatherPrimDimN 3 xs.length 0 xs)
          (((a*d1+b)*d2+p)*D+(r*d3+c)) =
        valAt (xs.getD r (zeroTensor [d0,d1,d2,d3]))
          (((a*d1+b)*d2+p)*d3+c) := by
    rw [allGatherPrimDimN_3_valAt_rank4 xs xs.length d0 d1 d2 d3 _
      hhead hK hd3 (by
        have hab : a*d1+b < d0*d1 := by
          have hstep : a*d1+b < (a+1)*d1 := by nlinarith
          exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d1 (Nat.succ_le_iff.mpr ha))
        have habp : (a*d1+b)*d2+p < (d0*d1)*d2 := by
          have hstep : (a*d1+b)*d2+p < ((a*d1+b)+1)*d2 := by nlinarith
          exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d2 (Nat.succ_le_iff.mpr hab))
        have hstep : ((a*d1+b)*d2+p)*D+(r*d3+c) <
            (((a*d1+b)*d2+p)+1)*D := by rw [hgc]; nlinarith
        exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right D (Nat.succ_le_iff.mpr habp)))]
    change valAt _ _ = valAt _ _
    rw [show d3*xs.length=D by rfl,
      append_div_self ((a*d1+b)*d2+p) (r*d3+c) D hD (by simpa [hgc] using hg),
      append_mod_self ((a*d1+b)*d2+p) (r*d3+c) D (by simpa [hgc] using hg),
      append_div_self r c d3 (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self r c d3 hc]
  rw [hleft]
  have hright_div : out/(D*d2)=a*d1+b := by
    dsimp [out]
    rw [append_div _ D p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_div_self (a*d1+b) (r*d3+c) D hD (by simpa [hgc] using hg)]
  have hright_g : out%(D*d2)/d2=r*d3+c := by
    dsimp [out]
    rw [append_mod _ D p d2 hD (Nat.pos_of_ne_zero hd2) hp,
      append_mod_self (a*d1+b) (r*d3+c) D (by simpa [hgc] using hg),
      append_div_self (r*d3+c) p d2 (Nat.pos_of_ne_zero hd2) hp]
  have hright_p : out%(D*d2)%d2=p := by
    dsimp [out]
    rw [append_mod _ D p d2 hD (Nat.pos_of_ne_zero hd2) hp,
      append_mod_self (a*d1+b) (r*d3+c) D (by simpa [hgc] using hg),
      append_mod_self (r*d3+c) p d2 hp]
  have hright :
      valAt (allGatherPrimDimN 2 xs.length 0 (xs.map (transposeAxes 2 3))) out =
        valAt ((xs.map (transposeAxes 2 3)).getD r (zeroTensor [d0,d1,d3,d2]))
          (((a*d1+b)*d3+c)*d2+p) := by
    rw [allGatherPrimDimN_2_valAt_rank4 (xs.map (transposeAxes 2 3)) xs.length
      d0 d1 d3 d2 out hmaphead hK hd3 hd2 (by simpa [out, D, Nat.mul_assoc] using hcanonical)]
    change valAt _ _ = valAt _ _
    rw [show d3*xs.length=D by rfl, hright_div, hright_g,
      append_div_self r c d3 (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self r c d3 hc, hright_p]
    congr 1
    ring
  rw [hright, hselect]
  have hlocal : (((a*d1+b)*d3+c)*d2+p) < d0*d1*d3*d2 := by
    have hab : a*d1+b < d0*d1 := by
      have hstep : a*d1+b < (a+1)*d1 := by nlinarith
      exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d1 (Nat.succ_le_iff.mpr ha))
    have habc : (a*d1+b)*d3+c < (d0*d1)*d3 := by
      have hstep : (a*d1+b)*d3+c < ((a*d1+b)+1)*d3 := by nlinarith
      exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 (Nat.succ_le_iff.mpr hab))
    nlinarith
  rw [transposeAxes_2_3_valAt_gen _ d0 d1 d2 d3 _ hpiece hd1 hd2 hd3 hlocal]
  have hlocal_div : (((a*d1+b)*d3+c)*d2+p)/(d1*d3*d2)=a := by
    rw [show d1*d3*d2=(d1*d3)*d2 by ring,
      append_div _ (d1*d3) p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_div _ d1 c d3 (Nat.pos_of_ne_zero hd3) hc,
      append_div_self a b d1 (Nat.pos_of_ne_zero hd1) hb]
  have hlocal_b : (((a*d1+b)*d3+c)*d2+p)%(d1*d3*d2)/(d3*d2)=b := by
    rw [show d1*d3*d2=(d1*d3)*d2 by ring,
      append_mod _ (d1*d3) p d2
        (Nat.mul_pos (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_div _ d3 p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d1 c d3 (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a b d1 hb,
      append_div_self b c d3 (Nat.pos_of_ne_zero hd3) hc]
  have hlocal_inner : (((a*d1+b)*d3+c)*d2+p)%(d1*d3*d2)%(d3*d2)=c*d2+p := by
    rw [show d1*d3*d2=(d1*d3)*d2 by ring,
      append_mod _ (d1*d3) p d2
        (Nat.mul_pos (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d3 p d2 (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d1 c d3 (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a b d1 hb, append_mod_self b c d3 hc]
  rw [hlocal_div, hlocal_b, hlocal_inner,
    append_mod_self c p d2 hp,
    append_div_self c p d2 (Nat.pos_of_ne_zero hd2) hp]
  congr 1
  ring


set_option maxHeartbeats 3200000 in
theorem transposeAxes_2_3_allGather_dim1_rank4
    (xs : List Tensor) (d0 d1 d2 d3 : Nat)
    (hne : xs ≠ [])
    (hshapes : ∀ x ∈ xs, x.shape = [d0, d1, d2, d3]) :
    transposeAxes 2 3 (allGatherPrimDimN 1 xs.length 0 xs) =
      allGatherPrimDimN 1 xs.length 0 (xs.map (transposeAxes 2 3)) := by
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
  have hhead : (xs.head?.map (fun t => t.shape)).getD [] = [d0, d1, d2, d3] := by
    cases xs with
    | nil => simp at hne
    | cons x rest => simpa using hshapes x (by simp)
  have hmaphead : (((xs.map (transposeAxes 2 3)).head?.map (fun t => t.shape)).getD []) =
      [d0, d1, d3, d2] := by
    cases xs with
    | nil => simp at hne
    | cons x rest =>
      have hx := hshapes x (by simp)
      simp [transposeAxes, Tensor.mkShape, hx, listSwapAt, List.getD, List.set]
  have hK : xs.length ≠ 0 := by
    intro hz
    apply hne
    exact List.length_eq_zero_iff.mp hz
  have hgshape : (allGatherPrimDimN 1 xs.length 0 xs).shape =
      [d0, d1*xs.length, d2, d3] := by
    rw [allGatherPrimDimN_shape 1 xs.length xs [d0, d1, d2, d3] hhead]
    simp [List.set, List.getD]
  have hlshape : (transposeAxes 2 3 (allGatherPrimDimN 1 xs.length 0 xs)).shape =
      [d0, d1*xs.length, d3, d2] := by
    simp [transposeAxes, Tensor.mkShape, hgshape, listSwapAt, List.getD, List.set]
  have hrshape : (allGatherPrimDimN 1 xs.length 0 (xs.map (transposeAxes 2 3))).shape =
      [d0, d1*xs.length, d3, d2] := by
    rw [allGatherPrimDimN_shape 1 xs.length _ [d0, d1, d3, d2] hmaphead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlshape, hrshape])
  intro idx hidx
  have hbound : idx < d0*(d1*xs.length)*d3*d2 := by
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
  let D := d1 * xs.length
  have hD : 0 < D := Nat.mul_pos (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hK)
  let p := idx % d2
  let q0 := idx / d2
  let c := q0 % d3
  let q1 := q0 / d3
  let g := q1 % D
  let a := q1 / D
  have hp : p < d2 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd2)
  have hc : c < d3 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd3)
  have hg : g < D := Nat.mod_lt _ hD
  have hcoords : idx = (((a*D+g)*d3+c)*d2+p) := by
    have h0 : q0*d2+p=idx := by
      simpa [q0, p, Nat.mul_comm] using Nat.div_add_mod idx d2
    have h1 : q1*d3+c=q0 := by
      simpa [q1, c, Nat.mul_comm] using Nat.div_add_mod q0 d3
    have h2 : a*D+g=q1 := by
      simpa [a, g, Nat.mul_comm] using Nat.div_add_mod q1 D
    rw [← h0, ← h1, ← h2]
  let r := g / d1
  let b := g % d1
  have hb : b < d1 := Nat.mod_lt _ (Nat.pos_of_ne_zero hd1)
  have hgb : r*d1+b=g := by
    simpa [r, b, Nat.mul_comm] using Nat.div_add_mod g d1
  have hr : r < xs.length := by
    apply Nat.div_lt_of_lt_mul
    simpa [D, Nat.mul_comm] using hg
  have hselect : (xs.map (transposeAxes 2 3)).getD r (zeroTensor [d0, d1, d3, d2]) =
      transposeAxes 2 3 (xs.getD r (zeroTensor [d0, d1, d2, d3])) := by
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_eq_getElem hr]
    simp
  have hpiece : (xs.getD r (zeroTensor [d0, d1, d2, d3])).shape = [d0, d1, d2, d3] := by
    unfold List.getD
    rw [List.getElem?_eq_getElem hr]
    simpa using hshapes xs[r] (List.getElem_mem ..)
  have hcanonical : (((a*D+(r*d1+b))*d3+c)*d2+p) < d0*D*d3*d2 := by
    rw [hgb, ← hcoords]
    simpa [D, Nat.mul_assoc] using hbound
  rw [hcoords, ← hgb]
  let out := (((a*D+(r*d1+b))*d3+c)*d2+p)
  have hout_div : out/(D*d3*d2)=a := by
    dsimp [out]
    rw [show D*d3*d2=(D*d3)*d2 by ring,
      append_div _ (D*d3) p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_div _ D c d3 (Nat.pos_of_ne_zero hd3) hc,
      append_div_self a (r*d1+b) D hD (by simpa [hgb] using hg)]
  have hout_g : out%(D*d3*d2)/(d3*d2)=r*d1+b := by
    dsimp [out]
    rw [show D*d3*d2=(D*d3)*d2 by ring,
      append_mod _ (D*d3) p d2 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_div _ d3 p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ D c d3 hD (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a (r*d1+b) D (by simpa [hgb] using hg),
      append_div_self (r*d1+b) c d3 (Nat.pos_of_ne_zero hd3) hc]
  have hinner : out%(D*d3*d2)%(d3*d2)=c*d2+p := by
    dsimp [out]
    rw [show D*d3*d2=(D*d3)*d2 by ring,
      append_mod _ (D*d3) p d2 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d3 p d2 (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ D c d3 hD (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a (r*d1+b) D (by simpa [hgb] using hg),
      append_mod_self (r*d1+b) c d3 hc]
  have hout_p : out%(D*d3*d2)%(d3*d2)%d2=p := by
    rw [hinner, append_mod_self c p d2 hp]
  have hout_c : out%(D*d3*d2)%(d3*d2)/d2=c := by
    rw [hinner, append_div_self c p d2 (Nat.pos_of_ne_zero hd2) hp]
  have htranspose :
      valAt (transposeAxes 2 3 (allGatherPrimDimN 1 xs.length 0 xs)) out =
        valAt (allGatherPrimDimN 1 xs.length 0 xs)
          (((a*D+(r*d1+b))*d2+p)*d3+c) := by
    rw [transposeAxes_2_3_valAt_gen _ d0 D d2 d3 out hgshape
      (Nat.ne_of_gt hD) hd2 hd3 (by simpa [out] using hcanonical)]
    rw [hout_div, hout_g, hout_p, hout_c]
    congr 1
    ring
  rw [htranspose]
  have ha : a < d0 := by
    rw [← hout_div]
    apply Nat.div_lt_of_lt_mul
    calc
      out < d0*D*d3*d2 := by simpa [out] using hcanonical
      _ = (D*d3*d2)*d0 := by ring
  have hleft :
      valAt (allGatherPrimDimN 1 xs.length 0 xs)
          (((a*D+(r*d1+b))*d2+p)*d3+c) =
        valAt (xs.getD r (zeroTensor [d0, d1, d2, d3]))
          (((a*d1+b)*d2+p)*d3+c) := by
    rw [allGatherPrimDimN_1_valAt_rank4 xs xs.length d0 d1 d2 d3 _
      hhead hK hd1 hd2 hd3 (by
        have hag : a*D+(r*d1+b) < d0*D := by
          have hstep : a*D+(r*d1+b) < (a+1)*D := by rw [hgb]; nlinarith
          exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right D (Nat.succ_le_iff.mpr ha))
        have hagp : (a*D+(r*d1+b))*d2+p < (d0*D)*d2 := by
          have hstep : (a*D+(r*d1+b))*d2+p < ((a*D+(r*d1+b))+1)*d2 := by nlinarith
          exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d2 (Nat.succ_le_iff.mpr hag))
        have hstep : ((a*D+(r*d1+b))*d2+p)*d3+c <
            (((a*D+(r*d1+b))*d2+p)+1)*d3 := by nlinarith
        exact lt_of_lt_of_le hstep
          (Nat.mul_le_mul_right d3 (Nat.succ_le_iff.mpr hagp)))]
    change valAt _ _ = valAt _ _
    rw [show d1*xs.length=D by rfl]
    have hsrc_div : (((a*D+(r*d1+b))*d2+p)*d3+c)/(D*(d2*d3))=a := by
      rw [show D*(d2*d3)=(D*d2)*d3 by ring,
        append_div _ (D*d2) c d3 (Nat.pos_of_ne_zero hd3) hc,
        append_div _ D p d2 (Nat.pos_of_ne_zero hd2) hp,
        append_div_self a (r*d1+b) D hD (by simpa [hgb] using hg)]
    have hsrc_g : (((a*D+(r*d1+b))*d2+p)*d3+c)%(D*(d2*d3))/(d2*d3)=r*d1+b := by
      rw [show D*(d2*d3)=(D*d2)*d3 by ring,
        append_mod _ (D*d2) c d3 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd2))
          (Nat.pos_of_ne_zero hd3) hc,
        append_div _ d2 c d3 (Nat.pos_of_ne_zero hd3) hc,
        append_mod _ D p d2 hD (Nat.pos_of_ne_zero hd2) hp,
        append_mod_self a (r*d1+b) D (by simpa [hgb] using hg),
        append_div_self (r*d1+b) p d2 (Nat.pos_of_ne_zero hd2) hp]
    have hsrc_inner : (((a*D+(r*d1+b))*d2+p)*d3+c)%(D*(d2*d3))%(d2*d3)=p*d3+c := by
      rw [show D*(d2*d3)=(D*d2)*d3 by ring,
        append_mod _ (D*d2) c d3 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd2))
          (Nat.pos_of_ne_zero hd3) hc,
        append_mod _ d2 c d3 (Nat.pos_of_ne_zero hd2) (Nat.pos_of_ne_zero hd3) hc,
        append_mod _ D p d2 hD (Nat.pos_of_ne_zero hd2) hp,
        append_mod_self a (r*d1+b) D (by simpa [hgb] using hg),
        append_mod_self (r*d1+b) p d2 hp]
    rw [hsrc_div, hsrc_g, append_div_self r b d1 (Nat.pos_of_ne_zero hd1) hb,
      append_mod_self r b d1 hb, hsrc_inner]
    congr 1
    ring
  rw [hleft]
  have hright_div : out/(D*(d3*d2))=a := by
    dsimp [out]
    rw [show D*(d3*d2)=(D*d3)*d2 by ring,
      append_div _ (D*d3) p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_div _ D c d3 (Nat.pos_of_ne_zero hd3) hc,
      append_div_self a (r*d1+b) D hD (by simpa [hgb] using hg)]
  have hright_g : out%(D*(d3*d2))/(d3*d2)=r*d1+b := by
    dsimp [out]
    rw [show D*(d3*d2)=(D*d3)*d2 by ring,
      append_mod _ (D*d3) p d2 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_div _ d3 p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ D c d3 hD (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a (r*d1+b) D (by simpa [hgb] using hg),
      append_div_self (r*d1+b) c d3 (Nat.pos_of_ne_zero hd3) hc]
  have hright_inner : out%(D*(d3*d2))%(d3*d2)=c*d2+p := by
    dsimp [out]
    rw [show D*(d3*d2)=(D*d3)*d2 by ring,
      append_mod _ (D*d3) p d2 (Nat.mul_pos hD (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d3 p d2 (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ D c d3 hD (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a (r*d1+b) D (by simpa [hgb] using hg),
      append_mod_self (r*d1+b) c d3 hc]
  have hright :
      valAt (allGatherPrimDimN 1 xs.length 0 (xs.map (transposeAxes 2 3))) out =
        valAt ((xs.map (transposeAxes 2 3)).getD r (zeroTensor [d0, d1, d3, d2]))
          (((a*d1+b)*d3+c)*d2+p) := by
    rw [allGatherPrimDimN_1_valAt_rank4 (xs.map (transposeAxes 2 3)) xs.length
      d0 d1 d3 d2 out hmaphead hK hd1 hd3 hd2
      (by simpa [out, D, Nat.mul_assoc] using hcanonical)]
    change valAt _ _ = valAt _ _
    rw [show d1*xs.length=D by rfl, hright_div, hright_g,
      append_div_self r b d1 (Nat.pos_of_ne_zero hd1) hb,
      append_mod_self r b d1 hb, hright_inner]
    congr 1
    ring
  rw [hright, hselect]
  have hlocal : (((a*d1+b)*d3+c)*d2+p) < d0*d1*d3*d2 := by
    have hab : a*d1+b < d0*d1 := by
      have hstep : a*d1+b < (a+1)*d1 := by nlinarith
      exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d1 (Nat.succ_le_iff.mpr ha))
    have habc : (a*d1+b)*d3+c < (d0*d1)*d3 := by
      have hstep : (a*d1+b)*d3+c < ((a*d1+b)+1)*d3 := by nlinarith
      exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right d3 (Nat.succ_le_iff.mpr hab))
    nlinarith
  rw [transposeAxes_2_3_valAt_gen _ d0 d1 d2 d3 _ hpiece hd1 hd2 hd3 hlocal]
  have hlocal_div : (((a*d1+b)*d3+c)*d2+p)/(d1*d3*d2)=a := by
    rw [show d1*d3*d2=(d1*d3)*d2 by ring,
      append_div _ (d1*d3) p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_div _ d1 c d3 (Nat.pos_of_ne_zero hd3) hc,
      append_div_self a b d1 (Nat.pos_of_ne_zero hd1) hb]
  have hlocal_b : (((a*d1+b)*d3+c)*d2+p)%(d1*d3*d2)/(d3*d2)=b := by
    rw [show d1*d3*d2=(d1*d3)*d2 by ring,
      append_mod _ (d1*d3) p d2
        (Nat.mul_pos (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_div _ d3 p d2 (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d1 c d3 (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a b d1 hb,
      append_div_self b c d3 (Nat.pos_of_ne_zero hd3) hc]
  have hlocal_inner : (((a*d1+b)*d3+c)*d2+p)%(d1*d3*d2)%(d3*d2)=c*d2+p := by
    rw [show d1*d3*d2=(d1*d3)*d2 by ring,
      append_mod _ (d1*d3) p d2
        (Nat.mul_pos (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3))
        (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d3 p d2 (Nat.pos_of_ne_zero hd3) (Nat.pos_of_ne_zero hd2) hp,
      append_mod _ d1 c d3 (Nat.pos_of_ne_zero hd1) (Nat.pos_of_ne_zero hd3) hc,
      append_mod_self a b d1 hb, append_mod_self b c d3 hc]
  rw [hlocal_div, hlocal_b, hlocal_inner,
    append_mod_self c p d2 hp,
    append_div_self c p d2 (Nat.pos_of_ne_zero hd2) hp]
  congr 1
  ring

/-- Rank-4 transpose of axes 2 and 3 transports dim-3 sharding to dim 2. -/
theorem RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : RelationCompiler.ShardedRel full shards 3
      [d0, d1, d2, d3 * shards.length] [d0, d1, d2, d3]) :
    RelationCompiler.ShardedRel
      (transposeAxes 2 3 full) (shards.map (transposeAxes 2 3)) 2
      [d0, d1, d3 * shards.length, d2] [d0, d1, d3, d2] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      transposeAxes_2_3_allGather_dim3_to_dim2_rank4 shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · simp [transposeAxes, Tensor.mkShape, h.full_shape, listSwapAt, List.getD, List.set]
  · intro hnil
    cases shards with
    | nil => exact h.shards_nonempty rfl
    | cons shard rest => simp at hnil
  · simp
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    simp [transposeAxes, Tensor.mkShape, h.shard_shapes source hsource,
      listSwapAt, List.getD, List.set]
  · simp [List.set, List.getD]

/-- Rank-4 transpose of axes 2 and 3 preserves dim-1 sharding. -/
theorem RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : RelationCompiler.ShardedRel full shards 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3]) :
    RelationCompiler.ShardedRel
      (transposeAxes 2 3 full) (shards.map (transposeAxes 2 3)) 1
      [d0, d1 * shards.length, d3, d2] [d0, d1, d3, d2] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      transposeAxes_2_3_allGather_dim1_rank4 shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · simp [transposeAxes, Tensor.mkShape, h.full_shape, listSwapAt, List.getD, List.set]
  · intro hnil
    cases shards with
    | nil => exact h.shards_nonempty rfl
    | cons shard rest => simp at hnil
  · simp
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    simp [transposeAxes, Tensor.mkShape, h.shard_shapes source hsource,
      listSwapAt, List.getD, List.set]
  · simp [List.set, List.getD]

end TrainVerify.Denote
