import denote.KRankLinearGather

namespace TrainVerify.Denote
noncomputable section
open scoped BigOperators

-- Bounded scalar-sum helpers, following KRankBWLayernormParam.
set_option maxHeartbeats 500000 in
private theorem sequence_map_sum_eq_range_sum
    (ts : List Tensor) (f : Tensor → Scalar) (default : Tensor) :
    (ts.map f).sum = ∑ r ∈ Finset.range ts.length, f (ts.getD r default) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map, List.sum_cons, List.length_cons]
      rw [Finset.sum_range_succ', ih]
      have h0 : (t :: ts).getD 0 default = t := by simp [List.getD]
      have hsucc : ∀ r, (t :: ts).getD (r + 1) default = ts.getD r default := by
        intro r
        simp [List.getD]
      simp only [h0, hsucc]
      rw [add_comm]

set_option maxHeartbeats 500000 in
private theorem sequence_tensorSum_valAt (ts : List Tensor) (j : Nat)
    (hj : j < prodShape (tensorSum ts).shape) :
    valAt (tensorSum ts) j =
      ∑ r ∈ Finset.range ts.length, valAt (ts.getD r (zeroTensor [])) j := by
  have hfold : valAt (tensorSum ts) j =
      ts.foldl (fun acc t => acc + valAt t j) 0 := by
    cases ts with
    | nil => rw [valAt_of_lt _ _ hj]; rfl
    | cons t ts => rw [valAt_of_lt _ _ hj]; rfl
  rw [hfold, List.foldl_add_eq_sum]
  exact sequence_map_sum_eq_range_sum ts (fun t => valAt t j) (zeroTensor [])

set_option maxHeartbeats 500000 in
/-- Sequence-sharded rank-3 linear weight gradients reduce across any positive
rank count. The proof uses the actual dW kernel and interchanges the batch and
rank sums: a dimension-1 gather is not flat concatenation when `b > 1`. -/
theorem bw_linear_dw_sequence_reduction_rank3
    (K b s o i : Nat) (gs xs : List Tensor) (w : Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (ho : 0 < o) (hi : 0 < i)
    (hglen : gs.length = K) (hxlen : xs.length = K)
    (hgsh : ∀ g ∈ gs, g.shape = [b, s, o])
    (hxsh : ∀ x ∈ xs, x.shape = [b, s, i])
    (hw : w.shape = [o, i]) :
    (bw_linear (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) w).2 =
      tensorSum (List.zipWith (fun g x => (bw_linear g x w).2) gs xs) := by
  classical
  have hgne : gs ≠ [] := by intro h; simp [h] at hglen; omega
  have hxne : xs ≠ [] := by intro h; simp [h] at hxlen; omega
  have hghead : (gs.head?.map (fun t => t.shape)).getD [] = [b, s, o] := by
    obtain ⟨g, rest, rfl⟩ := List.exists_cons_of_ne_nil hgne
    exact hgsh g (by simp)
  have hxhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, s, i] := by
    obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hxne
    exact hxsh x (by simp)
  have hgfull : (allGatherPrimDimN 1 K 0 gs).shape = [b, s * K, o] := by
    rw [allGatherPrimDimN_shape 1 K gs [b, s, o] hghead]
    simp [List.set, List.getD]
  have hxfull : (allGatherPrimDimN 1 K 0 xs).shape = [b, s * K, i] := by
    rw [allGatherPrimDimN_shape 1 K xs [b, s, i] hxhead]
    simp [List.set, List.getD]
  let pieces := List.zipWith (fun g x => (bw_linear g x w).2) gs xs
  have hplen : pieces.length = K := by
    simp only [pieces, List.length_zipWith, hglen, hxlen, Nat.min_self]
  have hphead : (pieces.head?.map (fun t => t.shape)).getD [] = [o, i] := by
    obtain ⟨g, gr, rfl⟩ := List.exists_cons_of_ne_nil hgne
    obtain ⟨x, xr, rfl⟩ := List.exists_cons_of_ne_nil hxne
    change (bw_linear g x w).2.shape = [o, i]
    exact bw_linear_3d_snd_shape b s o i g x w
      (hgsh g (by simp)) (hxsh x (by simp)) hw
  have hlhs : (bw_linear (allGatherPrimDimN 1 K 0 gs)
      (allGatherPrimDimN 1 K 0 xs) w).2.shape = [o, i] :=
    bw_linear_3d_snd_shape b (s * K) o i _ _ w hgfull hxfull hw
  have hrhs : (tensorSum pieces).shape = [o, i] := by
    have hpne : pieces ≠ [] := by intro h; simp [h] at hplen; omega
    obtain ⟨t, ts, he⟩ := List.exists_cons_of_ne_nil hpne
    rw [he, tensorSum_shape]
    rw [he] at hphead
    exact hphead
  apply Tensor.ext (by rw [hlhs, hrhs])
  intro idx hidx
  have hbound : idx < o * i := by
    rw [hlhs] at hidx
    simpa only [prodShape, List.foldl, Nat.one_mul] using hidx
  let c := idx / i
  let k := idx % i
  have hc : c < o := Nat.div_lt_of_lt_mul (by
    simpa only [Nat.mul_comm] using hbound)
  have hk : k < i := Nat.mod_lt idx hi
  have heq : idx = c * i + k := by
    simpa only [c, k, Nat.mul_comm] using (Nat.div_add_mod idx i).symm
  have hcoord : c * i + k < o * i := by rw [← heq]; exact hbound
  change valAt (bw_linear _ _ w).2 idx = valAt (tensorSum pieces) idx
  rw [heq, bw_linear_dw_valAt3d _ _ w b (s * K) o i hgfull hxfull hw c hc k hk,
    sequence_tensorSum_valAt pieces (c * i + k) (by
      rw [hrhs]
      simpa only [prodShape, List.foldl, Nat.one_mul] using hcoord), hplen]
  let F := fun row =>
    valAt (allGatherPrimDimN 1 K 0 gs) (row * o + c) *
      valAt (allGatherPrimDimN 1 K 0 xs) (row * i + k)
  have hlocal : ∀ r, r < K →
      valAt (pieces.getD r (zeroTensor [])) (c * i + k) =
        ∑ q ∈ Finset.range b, ∑ p ∈ Finset.range s,
          F (q * (s * K) + (r * s + p)) := by
    intro r hr
    have hgr : r < gs.length := by rw [hglen]; exact hr
    have hxr : r < xs.length := by rw [hxlen]; exact hr
    have hpr : r < pieces.length := by rw [hplen]; exact hr
    have hglocal : (gs.getD r (zeroTensor [b, s, o])).shape = [b, s, o] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgr]
      exact hgsh gs[r] (List.getElem_mem hgr)
    have hxlocal : (xs.getD r (zeroTensor [b, s, i])).shape = [b, s, i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxr]
      exact hxsh xs[r] (List.getElem_mem hxr)
    have hget : pieces.getD r (zeroTensor []) =
        (bw_linear (gs.getD r (zeroTensor [b, s, o]))
          (xs.getD r (zeroTensor [b, s, i])) w).2 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr,
        List.getElem?_eq_getElem hgr, List.getElem?_eq_getElem hxr, Option.getD_some]
      exact List.getElem_zipWith
    rw [hget, bw_linear_dw_valAt3d _ _ w b s o i hglocal hxlocal hw c hc k hk,
      Finset.sum_range_mul_eq_sum_sum b s]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [F]
    rw [allGatherPrimDimN1_3d_valAt K b s o gs hK hb hs ho hghead
        q (Finset.mem_range.mp hq) r hr p (Finset.mem_range.mp hp) c hc,
      allGatherPrimDimN1_3d_valAt K b s i xs hK hb hs hi hxhead
        q (Finset.mem_range.mp hq) r hr p (Finset.mem_range.mp hp) k hk]
  change (∑ row ∈ Finset.range (b * (s * K)), F row) = _
  calc
    (∑ row ∈ Finset.range (b * (s * K)), F row) =
        ∑ q ∈ Finset.range b, ∑ r ∈ Finset.range K,
          ∑ p ∈ Finset.range s, F (q * (s * K) + (r * s + p)) := by
      rw [Finset.sum_range_mul_eq_sum_sum b (s * K)]
      apply Finset.sum_congr rfl
      intro q _
      have hsplit := Finset.sum_range_mul_eq_sum_sum K s
        (fun t => F (q * (s * K) + t))
      simpa only [Nat.mul_comm K s] using hsplit
    _ = ∑ r ∈ Finset.range K, ∑ q ∈ Finset.range b,
          ∑ p ∈ Finset.range s, F (q * (s * K) + (r * s + p)) := Finset.sum_comm
    _ = ∑ r ∈ Finset.range K, valAt (pieces.getD r (zeroTensor [])) (c * i + k) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hlocal r (Finset.mem_range.mp hr)).symm

end
end TrainVerify.Denote
