import denote.ZigzagCollective

/-! Single-sequence, arbitrary-positive-K inverse of the existing faithful CP
collective. This leaf does not widen compiler acceptance or model ring attention.
Index authority: nnScaler d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf,
`nnscaler/customized_ops/ring_attention/varlen_utils.py`, lines 90–158. -/

namespace TrainVerify.Denote.ZigzagCollective

-- One complete sequence, arbitrary positive CP count and half-shard width.
-- Uses the existing authority-backed index functions, not a new permutation model.
theorem zigzag_single_index_inverse (K d g : Nat)
    (hK : 0 < K) (hd : 0 < d) (hg : g < K * (2 * d)) :
    let r := destRank [0, K * (2 * d)] K g
    let k := zigzagInvOffset [0, K * (2 * d)] K r g
    r < K ∧ k < 2 * d ∧ zigzagPos [0, K * (2 * d)] K r k = g := by
  have hslice : K * (2 * d) / (2 * K) = d := by
    rw [show K * (2 * d) = d * (2 * K) by ring]
    exact Nat.mul_div_cancel d (by omega)
  have hq : g / d < 2 * K := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    nlinarith [hg]
  have hm : g % d < d := Nat.mod_lt g hd
  have hdecomp : g % d + (g / d) * d = g := by
    rw [Nat.mul_comm (g / d) d]
    exact Nat.mod_add_div g d
  have hrem : g - (g / d) * d = g % d := by omega
  simp only [destRank, zigzagInvOffset, zigzagPos, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    destRankAux, zigzagInvOffsetAux, sliceSizeAt, List.getD_cons_zero,
    List.getD_cons_succ, Nat.zero_add, Nat.sub_zero, hslice,
    hg, if_pos, Nat.ne_of_gt hd, if_false, hrem]
  by_cases hfront : g / d < K
  · simp only [hfront, if_pos, zigzagPosAux, sliceSizeAt,
      List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add,
      Nat.sub_zero, hslice, hm]
    exact ⟨trivial, by omega, by omega⟩
  · have hr : 2 * K - 1 - g / d < K := by omega
    have hback : ¬ d + g % d < d := by omega
    have hk : d + g % d < 2 * d := by omega
    have hmirror : 2 * K - (2 * K - 1 - g / d) - 1 = g / d := by omega
    simp only [hfront, if_false, zigzagPosAux, sliceSizeAt,
      List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add,
      Nat.sub_zero, hslice, hback, hk, if_pos, hmirror]
    exact ⟨hr, trivial, by omega⟩

private theorem foldl_mul_init (a : Nat) (xs : List Nat) :
    xs.foldl (· * ·) a = a * xs.foldl (· * ·) 1 := by
  induction xs generalizing a with
  | nil => simp only [List.foldl, Nat.mul_one]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (a * x), ih (1 * x)]
    ring

private theorem prodShape_cons (a : Nat) (tail : Shape) :
    prodShape (a :: tail) = a * prodShape tail := by
  simp only [prodShape, List.foldl, Nat.one_mul]
  exact foldl_mul_init a tail

-- A genuine list-valued tensor inverse, not merely shape preservation.
theorem fw_maybe_unshuffle_shuffle_collective_single
    (xs : List Tensor) (K d rank : Nat) (tail : Shape)
    (hK : 0 < K) (hd : 0 < d) (hrank : rank < K)
    (hlen : xs.length = K)
    (hshapes : ∀ x ∈ xs, x.shape = (2 * d) :: tail) :
    fw_maybe_unshuffle_collective
      ((List.range K).map (fw_maybe_shuffle_collective xs [0, K * (2 * d)] K))
      [0, K * (2 * d)] K rank = xs.getD rank (zeroTensor []) := by
  let cu := [0, K * (2 * d)]
  let zs := (List.range K).map (fw_maybe_shuffle_collective xs cu K)
  have hselect (r : Nat) (hr : r < K) :
      zs.getD r (zeroTensor []) = fw_maybe_shuffle_collective xs cu K r := by
    dsimp [zs]
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hr)]
    simp only [List.getElem_range, Option.map_some, Option.getD_some]
  have hsource (r : Nat) (hr : r < K) :
      (xs.getD r (zeroTensor [])).shape = (2 * d) :: tail := by
    unfold List.getD
    rw [List.getElem?_eq_getElem (by omega)]
    exact hshapes xs[r] (List.getElem_mem ..)
  have hzshape (r : Nat) (hr : r < K) :
      (zs.getD r (zeroTensor [])).shape = (2 * d) :: tail := by
    rw [hselect r hr, fw_maybe_shuffle_collective_shape]
    exact hsource r hr
  change fw_maybe_unshuffle_collective zs cu K rank = _
  by_cases hunit : K = 1
  · have hrzero : rank = 0 := by omega
    simp only [hunit] at hselect ⊢
    rw [fw_maybe_unshuffle_collective_cpSize_one _ _ _ hrzero,
      hselect rank (by omega), fw_maybe_shuffle_collective_cpSize_one _ _ _ hrzero]
  apply Tensor.ext
  · rw [fw_maybe_unshuffle_collective_shape, hzshape rank hrank, hsource rank hrank]
  · intro i hi
    rw [fw_maybe_unshuffle_collective_shape, hzshape rank hrank,
      prodShape_cons] at hi
    let stride := prodShape tail
    have hib : i < (2 * d) * stride := hi
    have hs : 0 < stride := by
      by_contra h
      have hz : stride = 0 := by omega
      simp only [hz, Nat.mul_zero] at hib
      exact Nat.not_lt_zero i hib
    let token := i / stride
    let h := i % stride
    have ht : token < 2 * d := (Nat.div_lt_iff_lt_mul hs).mpr hib
    have hh : h < stride := Nat.mod_lt i hs
    have hieq : token * stride + h = i := by
      dsimp [token, h]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod i stride
    let g := rank * (2 * d) + token
    have hg : g < K * (2 * d) := by dsimp [g]; nlinarith
    let r := destRank cu K g
    let k := zigzagInvOffset cu K r g
    have hinv := zigzag_single_index_inverse K d g hK hd hg
    change r < K ∧ k < 2 * d ∧ zigzagPos cu K r k = g at hinv
    rcases hinv with ⟨hr, hk, hfwd⟩
    have hkbound : k * stride + h < prodShape ((2 * d) :: tail) := by
      rw [prodShape_cons]
      change k * stride + h < (2 * d) * stride
      nlinarith
    rw [fw_maybe_unshuffle_collective_valAt zs cu K rank i hunit
      (by rw [hzshape rank hrank, prodShape_cons]; exact hi)]
    simp only [hzshape rank hrank, List.tail_cons, List.getD_cons_zero]
    change valAt (zs.getD r (zeroTensor [])) (k * stride + h) = _
    rw [hselect r hr, fw_maybe_shuffle_collective_valAt xs cu K r
      (k * stride + h) hunit (by rw [hsource r hr]; exact hkbound)]
    simp only [hsource r hr, List.tail_cons, List.getD_cons_zero]
    have hkdiv : (k * stride + h) / stride = k := by
      rw [Nat.add_comm (k * stride) h, Nat.mul_comm k stride,
        Nat.add_mul_div_left h k hs, Nat.div_eq_of_lt hh, Nat.zero_add]
    have hkmod : (k * stride + h) % stride = h := by
      rw [Nat.add_comm (k * stride) h, Nat.mul_comm k stride,
        Nat.add_mul_mod_self_left h stride k, Nat.mod_eq_of_lt hh]
    change gatherFromRank xs (2 * d) stride
      (zigzagPos cu K r ((k * stride + h) / stride)) ((k * stride + h) % stride) = _
    rw [hkdiv, hkmod, hfwd]
    unfold gatherFromRank
    have hgdiv : g / (2 * d) = rank := by
      dsimp [g]
      rw [Nat.add_comm, Nat.mul_comm rank (2 * d),
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
    have hgmod : g % (2 * d) = token := by
      dsimp [g]
      rw [Nat.add_comm, Nat.mul_comm rank (2 * d),
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    rw [hgdiv, hgmod]
    change valAt (xs.getD rank (zeroTensor [])) (token * stride + h) = _
    rw [hieq]

end TrainVerify.Denote.ZigzagCollective
