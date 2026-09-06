import denote.ZigzagKAttentionSource

open TrainVerify.Denote TrainVerify.Denote.ZigzagAttentionSource

namespace TrainVerify.Denote.ZigzagAttentionSourceWitness
noncomputable section

-- Nonconstant Q/K/V with unequal query and KV head counts.
def q : Tensor := Tensor.mkShape [12, 2, 2] (fun i => (i.val + 1 : Nat))
def k : Tensor := Tensor.mkShape [12, 1, 2] (fun i => (2 * i.val + 1 : Nat))
def v : Tensor := Tensor.mkShape [12, 1, 2] (fun i => (3 * i.val + 2 : Nat))
def cu : Tensor := Tensor.mkShape [2] (fun i => if i.val = 0 then 0 else 12)

theorem decode_cu : decodeCuSeqlens cu = [0, 12] := by
  unfold decodeCuSeqlens cu
  change (List.range 2).map _ = _
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.map_append]
  simp only [valAt, Tensor.mkShape, prodShape]
  norm_num [scalarToNat]

def weight (query j : Nat) : Scalar :=
  expFn (attnDotQK q k 2 1 2 query 1 j 0 * attnScale 2)
def value (j : Nat) : Scalar := valAt v (j * 2 + 1)

-- CP3 rank1 front row: global Q=3, query head1, output channel1.
theorem actual_front :
    valAt (fw_attn_varlen q k v cu cu 2 1 2 2 true 0) ((3 * 2 + 1) * 2 + 1) =
      branchRow 4 2 1 (weight 3) value := by
  rw [fw_attn_varlen_row q k v cu 12 2 1 2 2 _ rfl decode_cu (by decide) (by decide)]
  change causalRow 12 3 (weight 3) value = branchRow 4 2 1 (weight 3) value
  exact (front_row_eq 3 1 2 1 (weight 3) value (by decide) (by decide)).symm

-- Same rank end row: global Q=9, same head/channel; no constant-value shortcut.
theorem actual_end :
    valAt (fw_attn_varlen q k v cu cu 2 1 2 2 true 0) ((9 * 2 + 1) * 2 + 1) =
      branchRow 10 2 1 (weight 9) value := by
  rw [fw_attn_varlen_row q k v cu 12 2 1 2 2 _ rfl decode_cu (by decide) (by decide)]
  change causalRow 12 9 (weight 9) value = branchRow 10 2 1 (weight 9) value
  exact (end_row_eq 3 1 2 1 (weight 9) value (by decide) (by decide)).symm

theorem cp5_front (w x : Nat → Scalar) :
    branchRow 6 2 1 w x = causalRow 20 5 w x :=
  front_row_eq 5 2 2 1 w x (by decide) (by decide)

theorem cp5_end (w x : Nat → Scalar) :
    branchRow 16 2 1 w x = causalRow 20 15 w x :=
  end_row_eq 5 2 2 1 w x (by decide) (by decide)

end
end TrainVerify.Denote.ZigzagAttentionSourceWitness
