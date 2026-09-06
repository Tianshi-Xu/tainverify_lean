import denote.ZigzagKAttentionRows
import denote.ZigzagKAttentionTensor

/-! Tensor-level refinement of the single-sequence Real front/end model.
The actual zigzag Q relation supplies all local Q values; independent ordinary
K/V relations supply the rank-ordered gathers. No source-row equality is added
as a caller assumption. This is not a proof of GPU floating-point execution. -/

namespace TrainVerify.Denote.RelationCompiler
open ZigzagCollective ZigzagAttentionSource

set_option maxHeartbeats 500000 in
-- Combine per-row ownership, local dot products, source scatter and output relation.
theorem ZigzagKRel.sourceOutput_eq_collective
    (fullQ fullK fullV cu : Tensor) (qs ks vs : List Tensor)
    (K rank d qh kvh qd vd : Nat)
    (hq : ZigzagKRel fullQ qs cu [K * (2 * d), qh, qd] [2 * d, qh, qd])
    (hk : ShardedRel fullK ks 0 [K * (2 * d), kvh, qd] [2 * d, kvh, qd])
    (hv : ShardedRel fullV vs 0 [K * (2 * d), kvh, vd] [2 * d, kvh, vd])
    (hqs : qs.length = K) (hks : ks.length = K) (hvs : vs.length = K)
    (hcu : decodeCuSeqlens cu = [0, K * (2 * d)])
    (hK : 1 < K) (hr : rank < K) (hd : 0 < d)
    (hqh : 0 < qh) (hkvh : 0 < kvh) (hqd : 0 < qd) (hvd : 0 < vd)
    (_hgqa : qh % kvh = 0) :
    sourceOutput (qs.getD rank (zeroTensor []))
      (allGatherPrimDimN 0 K 0 ks) (allGatherPrimDimN 0 K 0 vs) K rank d qh kvh qd vd =
      fw_attn_zigzag_collective_sharded_kv qs ks vs cu cu qh kvh qd vd true 0 K rank := by
  have hkvalue : fullK = allGatherPrimDimN 0 K 0 ks := by
    have h := hk.full_value
    rw [hks] at h
    exact h
  have hvvalue : fullV = allGatherPrimDimN 0 K 0 vs := by
    have h := hv.full_value
    rw [hvs] at h
    exact h
  rw [← hkvalue, ← hvvalue]
  let outs := (List.range K).map (fun r =>
    fw_attn_zigzag_collective_sharded_kv qs ks vs cu cu qh kvh qd vd true 0 K r)
  have houts : outs.length = K := by simp only [outs, List.length_map, List.length_range]
  have hout := ZigzagKRel.attn_zigzag_sharded_kv_single fullQ fullK fullV cu cu
    qs ks vs K d qh kvh qd vd hq hk hv hqs hks hvs hcu (by omega) hd hqh hkvh hqd hvd
  change ZigzagKRel _ outs cu _ _ at hout
  have hselect : outs.getD rank (zeroTensor []) =
      fw_attn_zigzag_collective_sharded_kv qs ks vs cu cu qh kvh qd vd true 0 K rank := by
    dsimp only [outs]
    unfold List.getD
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa only [List.length_range] using hr)]
    simp only [List.getElem_range, Option.map_some, Option.getD_some]
  have hyshape := (hout.full_row_spec houts hcu hK hd hqh hvd rank 0 0 0
    hr (by omega) hqh hvd).1
  have hfullshape := (hq.full_row_spec hqs hcu hK hd hqh hqd rank 0 0 0
    hr (by omega) hqh hqd).2.1
  have hhead : fullQ.shape.head? = some (K * (2 * d)) := by rw [hfullshape]; rfl
  rw [← hselect]
  apply Tensor.ext
  · exact hyshape.symm
  · intro index hindex
    change index < prodShape [2 * d, qh, vd] at hindex
    simp only [prodShape, List.foldl, Nat.one_mul] at hindex
    let token := index / vd / qh
    let head := index / vd % qh
    let channel := index % vd
    have ht : token < 2 * d :=
      (Nat.div_lt_iff_lt_mul hqh).mpr ((Nat.div_lt_iff_lt_mul hvd).mpr hindex)
    have hh : head < qh := Nat.mod_lt _ hqh
    have hc : channel < vd := Nat.mod_lt _ hvd
    have hcoord : (token * qh + head) * vd + channel = index := by
      dsimp only [token, head, channel]
      rw [Nat.mul_comm (index / vd / qh) qh, Nat.div_add_mod,
        Nat.mul_comm (index / vd) vd, Nat.div_add_mod]
    rw [← hcoord, sourceOutput_valAt _ _ _ K rank d qh kvh qd vd token head channel ht hh hc,
      hout.full_row_value houts hcu hK hd hqh hvd rank token head channel hr ht hh hc]
    have hrow (c : Nat) (hc' : c < qd) :=
      hq.full_row_value hqs hcu hK hd hqh hqd rank token head c hr ht hh hc'
    rw [hcu, zigzagPos_single_eq K d rank token (by omega) ht]
    by_cases hf : token < d
    · rw [if_pos hf, if_pos hf]
      have hp : rank * d + d ≤ K * (2 * d) := by
        calc
          rank * d + d = (rank + 1) * d := by ring
          _ ≤ (2 * K) * d := Nat.mul_le_mul_right d (by omega)
          _ = _ := by ring
      have hpref : (rank + 1) * d = rank * d + d := by ring
      rw [hpref]
      apply sourceBranchRow_eq_full _ fullQ fullK fullV cu (K * (2 * d))
        qh kvh qd vd token head channel (rank * d) d token hhead hcu hh hc hf hp
      intro c hc'
      have h := hrow c hc'
      rw [hcu, zigzagPos_single_eq K d rank token (by omega) ht, if_pos hf] at h
      exact h
    · rw [if_neg hf, if_neg hf]
      have hi : token - d < d := by omega
      have hpref : (2 * K - rank) * d = (2 * K - rank - 1) * d + d := by
        have hblock : 2 * K - rank = (2 * K - rank - 1) + 1 := by omega
        calc
          (2 * K - rank) * d = ((2 * K - rank - 1) + 1) * d := congrArg (· * d) hblock
          _ = _ := by ring
      have hp : (2 * K - rank - 1) * d + d ≤ K * (2 * d) := by
        rw [← hpref]
        calc
          (2 * K - rank) * d ≤ (2 * K) * d := Nat.mul_le_mul_right d (Nat.sub_le _ _)
          _ = _ := by ring
      rw [hpref]
      apply sourceBranchRow_eq_full _ fullQ fullK fullV cu (K * (2 * d))
        qh kvh qd vd token head channel ((2 * K - rank - 1) * d) d (token - d)
        hhead hcu hh hc hi hp
      intro c hc'
      have h := hrow c hc'
      rw [hcu, zigzagPos_single_eq K d rank token (by omega) ht, if_neg hf] at h
      exact h

end TrainVerify.Denote.RelationCompiler
