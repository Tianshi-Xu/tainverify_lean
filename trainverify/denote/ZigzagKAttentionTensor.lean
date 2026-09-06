import denote.ZigzagKAttentionSource

namespace TrainVerify.Denote.ZigzagAttentionSource

/-- Coordinate form of the actual Denote row, retaining its GQA head mapping. -/
theorem fw_attn_varlen_row_at (q k v cu : Tensor) (N qh kvh qd vd i head channel : Nat)
    (hq : q.shape.head? = some N) (hcu : decodeCuSeqlens cu = [0, N])
    (hi : i < N) (hh : head < qh) (hc : channel < vd) :
    valAt (fw_attn_varlen q k v cu cu qh kvh qd vd true 0)
      ((i * qh + head) * vd + channel) =
    causalRow N i
      (fun j => expFn (attnDotQK q k qh kvh qd i head j
        (if (if kvh = 0 then 1 else qh / kvh) = 0 then head
         else head / (if kvh = 0 then 1 else qh / kvh)) * attnScale qd))
      (fun j => valAt v ((j * kvh +
        (if (if kvh = 0 then 1 else qh / kvh) = 0 then head
         else head / (if kvh = 0 then 1 else qh / kvh))) * vd + channel)) := by
  have hqh : 0 < qh := by omega
  have hvd : 0 < vd := by omega
  have hdiv : ((i * qh + head) * vd + channel) / vd = i * qh + head := by
    rw [Nat.add_comm, Nat.mul_comm (i * qh + head) vd,
      Nat.add_mul_div_left channel _ hvd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have himod : (i * qh + head) % qh = head := by
    rw [Nat.add_comm, Nat.mul_comm i qh, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh]
  have hidiv : (i * qh + head) / qh = i := by
    rw [Nat.add_comm, Nat.mul_comm i qh, Nat.add_mul_div_left head i hqh,
      Nat.div_eq_of_lt hh, Nat.zero_add]
  have hcmod : ((i * qh + head) * vd + channel) % vd = channel := by
    rw [Nat.add_comm, Nat.mul_comm (i * qh + head) vd,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have hb : (i * qh + head) * vd + channel < prodShape [N, qh, vd] := by
    simp only [prodShape, List.foldl, Nat.one_mul]
    have hih : i * qh + head < N * qh := by nlinarith
    nlinarith
  rw [fw_attn_varlen_row q k v cu N qh kvh qd vd _ hq hcu hb (by rw [hdiv, hidiv]; exact hi)]
  rw [hdiv, hidiv, himod, hcmod]

/-- The source branch reads the rank-local Q row and ordinary global K/V.
The prefix length and local branch row are supplied by its front/end metadata.
This is exact Real arithmetic, not a model of FlashAttention rounding. -/
noncomputable def sourceBranchRow (qLocal k v : Tensor)
    (qh kvh qd vd token head channel prefLen half idx : Nat) : Scalar :=
  let groupFactor := if kvh = 0 then 1 else qh / kvh
  let kvHead := if groupFactor = 0 then head else head / groupFactor
  branchRow prefLen half idx
    (fun j => expFn (attnDotQK qLocal k qh kvh qd token head j kvHead * attnScale qd))
    (fun j => valAt v ((j * kvh + kvHead) * vd + channel))

/-- The two source branch calls, followed by scatter into the original local Q
positions. Single-sequence equal lengths and no-window causal mode are fixed. -/
noncomputable def sourceOutput (qLocal k v : Tensor) (K rank d qh kvh qd vd : Nat) : Tensor :=
  Tensor.mkShape [2 * d, qh, vd] (fun outIdx =>
    let token := outIdx.val / vd / qh
    let head := outIdx.val / vd % qh
    let channel := outIdx.val % vd
    if token < d then
      sourceBranchRow qLocal k v qh kvh qd vd token head channel ((rank + 1) * d) d token
    else
      sourceBranchRow qLocal k v qh kvh qd vd token head channel ((2 * K - rank) * d) d (token - d))

/-- Actual Q-row values suffice to transport every Q/K dot product; K is not
reordered or replaced by a replicated-input assumption. -/
theorem attnDotQK_row_congr (qLocal qFull k : Tensor)
    (qh kvh qd token globalRow head key kvHead : Nat)
    (hrow : ∀ c, c < qd →
      valAt qLocal ((token * qh + head) * qd + c) =
      valAt qFull ((globalRow * qh + head) * qd + c)) :
    attnDotQK qLocal k qh kvh qd token head key kvHead =
      attnDotQK qFull k qh kvh qd globalRow head key kvHead := by
  unfold attnDotQK
  apply Finset.sum_congr rfl
  intro c hc
  rw [hrow c (Finset.mem_range.mp hc)]

/-- Refine one actual source branch row to Denote after its Q extraction is
proved by a value-level row equality. Metadata and logical offset stay explicit. -/
theorem sourceBranchRow_eq_full (qLocal qFull k v cu : Tensor)
    (N qh kvh qd vd token head channel offset half idx : Nat)
    (hq : qFull.shape.head? = some N) (hcu : decodeCuSeqlens cu = [0, N])
    (hh : head < qh) (hc : channel < vd)
    (hi : idx < half) (hp : offset + half ≤ N)
    (hrow : ∀ c, c < qd →
      valAt qLocal ((token * qh + head) * qd + c) =
      valAt qFull (((offset + idx) * qh + head) * qd + c)) :
    sourceBranchRow qLocal k v qh kvh qd vd token head channel
      (offset + half) half idx =
    valAt (fw_attn_varlen qFull k v cu cu qh kvh qd vd true 0)
      (((offset + idx) * qh + head) * vd + channel) := by
  dsimp only [sourceBranchRow]
  have hw : (fun j => expFn (attnDotQK qLocal k qh kvh qd token head j
      (if (if kvh = 0 then 1 else qh / kvh) = 0 then head
       else head / (if kvh = 0 then 1 else qh / kvh)) * attnScale qd)) =
    (fun j => expFn (attnDotQK qFull k qh kvh qd (offset + idx) head j
      (if (if kvh = 0 then 1 else qh / kvh) = 0 then head
       else head / (if kvh = 0 then 1 else qh / kvh)) * attnScale qd)) := by
    funext j
    rw [attnDotQK_row_congr qLocal qFull k qh kvh qd token (offset + idx) head j _ hrow]
  rw [hw, branch_row_eq offset half N idx _ _ hi hp]
  exact (fw_attn_varlen_row_at qFull k v cu N qh kvh qd vd (offset + idx) head channel
    hq hcu (by omega) hh hc).symm

/-- Scalar observation of the actual front/end output scatter. -/
theorem sourceOutput_valAt (qLocal k v : Tensor) (K rank d qh kvh qd vd token head channel : Nat)
    (ht : token < 2 * d) (hh : head < qh) (hc : channel < vd) :
    valAt (sourceOutput qLocal k v K rank d qh kvh qd vd) ((token * qh + head) * vd + channel) =
      if token < d then
        sourceBranchRow qLocal k v qh kvh qd vd token head channel ((rank + 1) * d) d token
      else
        sourceBranchRow qLocal k v qh kvh qd vd token head channel ((2 * K - rank) * d) d (token - d) := by
  have hqh : 0 < qh := by omega
  have hvd : 0 < vd := by omega
  have hdiv : ((token * qh + head) * vd + channel) / vd = token * qh + head := by
    rw [Nat.add_comm, Nat.mul_comm (token * qh + head) vd,
      Nat.add_mul_div_left channel _ hvd, Nat.div_eq_of_lt hc, Nat.zero_add]
  have himod : (token * qh + head) % qh = head := by
    rw [Nat.add_comm, Nat.mul_comm token qh, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh]
  have hidiv : (token * qh + head) / qh = token := by
    rw [Nat.add_comm, Nat.mul_comm token qh, Nat.add_mul_div_left head token hqh,
      Nat.div_eq_of_lt hh, Nat.zero_add]
  have hcmod : ((token * qh + head) * vd + channel) % vd = channel := by
    rw [Nat.add_comm, Nat.mul_comm (token * qh + head) vd,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have hb : (token * qh + head) * vd + channel < prodShape [2 * d, qh, vd] := by
    simp only [prodShape, List.foldl, Nat.one_mul]
    have hih : token * qh + head < (2 * d) * qh := by nlinarith
    nlinarith
  rw [valAt_of_lt _ _ hb]
  dsimp only [sourceOutput, Tensor.mkShape]
  rw [hdiv, hidiv, himod, hcmod]

end TrainVerify.Denote.ZigzagAttentionSource
