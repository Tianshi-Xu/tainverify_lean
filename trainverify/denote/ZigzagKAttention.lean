import denote.ZigzagKExit
import denote.KRankAllToAll

/-! Arbitrary-rank, single-sequence attention relations for the existing global
Denote collective. This module does not assert equivalence with a pinned Python
front/end kernel, nor enable a compiler rule. The ordinary output witnesses are
the actual ordered chunks of the full attention result. -/

namespace TrainVerify.Denote.RelationCompiler

open ZigzagCollective

private theorem uniform_getD_shape
    {xs : List Tensor} {sh : Shape} {r : Nat}
    (hsh : ∀ x ∈ xs, x.shape = sh) (hr : r < xs.length) :
    (xs.getD r (zeroTensor [])).shape = sh := by
  unfold List.getD
  rw [List.getElem?_eq_getElem hr, Option.getD_some]
  exact hsh _ (List.getElem_mem hr)

private theorem sharded_single_getD
    {full : Tensor} {xs : List Tensor} {fullShape shardShape : Shape}
    (h : ShardedRel full xs 0 fullShape shardShape)
    (hlen : xs.length = 1) : full = xs.getD 0 (zeroTensor []) := by
  cases xs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons x xs =>
    cases xs with
    | nil =>
      have hx := h.shard_shapes x (List.mem_singleton_self x)
      have hdim : 0 < x.shape.length := by rw [hx]; exact h.gather_dim_lt
      have hv := h.full_value
      rw [List.length_singleton, allGatherPrimDimN_singleton_eq 0 x hdim] at hv
      exact hv
    | cons y ys => simp only [List.length_cons] at hlen; omega

/-- Actual dim-0 chunks, including all shapes and exact gathered values, give
an ordinary relation for any positive rank count. -/
theorem ShardedRel.attention_chunks
    (full : Tensor) (K d qh vd : Nat)
    (hK : 0 < K) (hshape : full.shape = [K * (2 * d), qh, vd]) :
    ShardedRel full
      ((List.range K).map (fun r => chunkPrimDimN 0 K r full))
      0 [K * (2 * d), qh, vd] [2 * d, qh, vd] := by
  let chunks := (List.range K).map (fun r => chunkPrimDimN 0 K r full)
  have hlen : chunks.length = K := by rw [List.length_map, List.length_range]
  have hchunk (r : Nat) :
      (chunkPrimDimN 0 K r full).shape = [2 * d, qh, vd] := by
    rw [chunkPrimDimN_shape 0 K r full _ hshape (Nat.ne_of_gt hK)]
    change [K * (2 * d) / K, qh, vd] = [2 * d, qh, vd]
    rw [Nat.mul_div_cancel_left (2 * d) hK]
  have hofFn : chunks =
      List.ofFn (fun r : Fin K => chunkPrimDimN 0 K r.val full) := by
    apply List.ext_getElem
    · rw [hlen, List.length_ofFn]
    · intro r hl hr
      simp only [chunks, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  refine {
    full_value := ?_
    full_shape := hshape
    shards_nonempty := ?_
    gather_dim_lt := by decide
    shard_shapes := ?_
    shape_contract := ?_
  }
  · change full = allGatherPrimDimN 0 chunks.length 0 chunks
    rw [hlen, hofFn]
    exact (allGatherPrimDimN_chunks_ofFn 0 K full hK
      (by rw [hshape]; decide)
      (by
        rw [hshape]
        change K * (2 * d) % K = 0
        simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod])).symm
  · intro hempty
    have hz := congrArg List.length hempty
    change chunks.length = 0 at hz
    rw [hlen] at hz
    omega
  · intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    exact hchunk r
  · change [K * (2 * d), qh, vd] =
      [2 * d, qh, vd].set 0 ([2 * d, qh, vd].getD 0 0 * chunks.length)
    rw [hlen]
    change [K * (2 * d), qh, vd] = [(2 * d) * K, qh, vd]
    rw [Nat.mul_comm K (2 * d)]

-- Only the global Denote mathematics is claimed here. The caller's metadata
-- equality specifies a single sequence; K/V remain ordinary dim-0 shards.
set_option maxHeartbeats 500000 in
theorem ZigzagKRel.attn_zigzag_sharded_kv_single
    (fullQ fullK fullV cu cuKV : Tensor) (qs ks vs : List Tensor)
    (K d qh kvh qd vd : Nat)
    (hq : ZigzagKRel fullQ qs cu [K * (2 * d), qh, qd] [2 * d, qh, qd])
    (hk : ShardedRel fullK ks 0 [K * (2 * d), kvh, qd] [2 * d, kvh, qd])
    (hv : ShardedRel fullV vs 0 [K * (2 * d), kvh, vd] [2 * d, kvh, vd])
    (hqs : qs.length = K) (hks : ks.length = K) (hvs : vs.length = K)
    (hdecode : decodeCuSeqlens cu = [0, K * (2 * d)])
    (hK : 0 < K) (hd : 0 < d)
    (_hqh : 0 < qh) (_hkvh : 0 < kvh) (_hqd : 0 < qd) (_hvd : 0 < vd) :
    ZigzagKRel
      (fw_attn_varlen fullQ fullK fullV cu cuKV qh kvh qd vd true 0)
      ((List.range K).map (fun rank =>
        fw_attn_zigzag_collective_sharded_kv qs ks vs cu cuKV
          qh kvh qd vd true 0 K rank))
      cu [K * (2 * d), qh, vd] [2 * d, qh, vd] := by
  have hlinear := hq.to_sharded_unshuffle_single hd (by rw [hqs]; exact hdecode)
  rw [hqs] at hlinear
  let linearQ := (List.range K).map (fun rank =>
    fw_maybe_unshuffle_collective qs (decodeCuSeqlens cu) K rank)

  have hqvalue : fullQ = allGatherPrimDimN 0 K 0 linearQ := by
    have hh := hlinear.full_value
    simpa only [List.length_map, List.length_range] using hh
  have hkvalue : fullK = allGatherPrimDimN 0 K 0 ks := by
    have hh := hk.full_value
    rw [hks] at hh
    exact hh
  have hvvalue : fullV = allGatherPrimDimN 0 K 0 vs := by
    have hh := hv.full_value
    rw [hvs] at hh
    exact hh
  let fullOut := fw_attn_varlen fullQ fullK fullV cu cuKV qh kvh qd vd true 0
  let chunks := (List.range K).map (fun rank => chunkPrimDimN 0 K rank fullOut)
  have hfull : fullOut.shape = [K * (2 * d), qh, vd] := by
    apply fw_attn_varlen_shape
    rw [hlinear.full_shape]
    rfl
  have hchunks : ShardedRel fullOut chunks 0
      [K * (2 * d), qh, vd] [2 * d, qh, vd] :=
    ShardedRel.attention_chunks fullOut K d qh vd hK hfull
  have hlen : chunks.length = K := by rw [List.length_map, List.length_range]
  have hwf : ZigzagCuWF (decodeCuSeqlens cu) chunks chunks.length := by
    obtain ⟨sources, _, _, hcu, _⟩ := hq
    rw [hqs] at hcu
    have hfirst : (chunks.getD 0 (zeroTensor [])).shape = [2 * d, qh, vd] :=
      uniform_getD_shape hchunks.shard_shapes (by rw [hlen]; exact hK)
    refine {
      cp_pos := by rw [hlen]; exact hK
      ranks := rfl
      cu_starts_zero := hcu.cu_starts_zero
      cu_has_endpoint := hcu.cu_has_endpoint
      monotone := hcu.monotone
      divisible := ?_
      shapes_nonempty := ?_
      same_shape := ?_
      local_tokens := ?_
    }
    · rw [hlen]
      exact hcu.divisible
    · intro x hx
      rw [hchunks.shard_shapes x hx]
      exact List.cons_ne_nil _ _
    · intro x hx
      rw [hchunks.shard_shapes x hx, hfirst]
    · rw [hfirst, hlen, hdecode]
      change (2 * d) * K = K * (2 * d)
      exact Nat.mul_comm (2 * d) K
  have hentry := ZigzagKRel.of_sharded hchunks hwf
  rw [hlen] at hentry
  have hrangeone : List.range 1 = [0] := rfl
  have houtputs :
      (List.range K).map (fun rank =>
        fw_attn_zigzag_collective_sharded_kv qs ks vs cu cuKV
          qh kvh qd vd true 0 K rank) =
      (List.range K).map (fun rank =>
        fw_maybe_shuffle_collective chunks (decodeCuSeqlens cu) K rank) := by
    apply List.map_congr_left
    intro rank hrank
    have hr : rank < K := List.mem_range.mp hrank
    by_cases hone : K = 1
    · have hrzero : rank = 0 := by omega
      have hqone : fullQ = qs.getD 0 (zeroTensor []) := by
        have hh := sharded_single_getD hlinear (by rw [List.length_map, List.length_range, hone])
        simpa only [hone, hrangeone, List.map_cons, List.map_nil,
          List.getD_cons_zero, fw_maybe_unshuffle_collective, if_pos rfl] using hh
      have hkone := sharded_single_getD hk (hks.trans hone)
      have hvone := sharded_single_getD hv (hvs.trans hone)
      have hchunkone : chunkPrimDimN 0 1 0 fullOut = fullOut :=
        chunkPrimDimN_one_eq 0 fullOut (by rw [hfull]; decide)
      simp only [hone, hrzero, fw_attn_zigzag_collective_sharded_kv,
        fw_maybe_shuffle_collective, if_pos rfl]
      change fw_attn_varlen (qs.getD 0 (zeroTensor []))
        (ks.getD 0 (zeroTensor [])) (vs.getD 0 (zeroTensor []))
        cu cuKV qh kvh qd vd true 0 = chunks.getD 0 (zeroTensor [])
      rw [← hqone, ← hkone, ← hvone]
      change fullOut = chunks.getD 0 (zeroTensor [])
      simp only [chunks, hone, hrangeone, List.map_cons, List.map_nil,
        List.getD_cons_zero, hchunkone]
    · simp only [fw_attn_zigzag_collective_sharded_kv, hone, if_false]
      change fw_maybe_shuffle_collective
        ((List.range K).map (fun r => chunkPrimDimN 0 K r
          (fw_attn_varlen (allGatherPrimDimN 0 K 0 linearQ)
            (allGatherPrimDimN 0 K 0 ks) (allGatherPrimDimN 0 K 0 vs)
            cu cuKV qh kvh qd vd true 0))) (decodeCuSeqlens cu) K rank = _
      rw [← hqvalue, ← hkvalue, ← hvvalue]
  rw [houtputs]
  exact hentry

end TrainVerify.Denote.RelationCompiler
