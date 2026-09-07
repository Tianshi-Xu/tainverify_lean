import denote.KRankViewFlatten

namespace TrainVerify.Denote

noncomputable section

set_option maxHeartbeats 500000

-- 元素总数相等时，view 保持所有零扩展的平坦读值。
private theorem viewUnflatten_valAt_of_prod
    (target : Shape) (x : Tensor) (idx : Nat)
    (hprod : prodShape target = prodShape x.shape) :
    valAt (fw_view target x) idx = valAt x idx := by
  unfold fw_view valAt
  simp only [Tensor.mkShape]
  split <;> split <;> simp_all

-- 从实际 Tensor 值证明往返恒等，不把输出相等作为假设。
private theorem viewUnflatten_roundtrip
    (target source : Shape) (x : Tensor)
    (hshape : x.shape = source)
    (hprod : prodShape target = prodShape source) :
    fw_view source (fw_view target x) = x := by
  have hinner : prodShape target = prodShape x.shape := by
    rw [hshape]
    exact hprod
  have houter : prodShape source = prodShape (fw_view target x).shape :=
    hprod.symm
  apply Tensor.ext
  · exact hshape.symm
  · intro idx _
    rw [viewUnflatten_valAt_of_prod _ _ idx houter,
      viewUnflatten_valAt_of_prod _ _ idx hinner]

private theorem viewUnflatten_map_roundtrip
    (target source : Shape) (xs : List Tensor)
    (hprod : prodShape target = prodShape source) :
    (∀ x ∈ xs, x.shape = source) →
    (xs.map (fun x => fw_view target x)).map (fun x => fw_view source x) = xs := by
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x rest ih =>
      intro hshape
      have hx := viewUnflatten_roundtrip target source x
        (hshape x (List.mem_cons_self ..)) hprod
      have hr := ih (fun y hy => hshape y (List.mem_cons_of_mem x hy))
      change fw_view source (fw_view target x) ::
        (rest.map (fun y => fw_view target y)).map (fun y => fw_view source y) =
          x :: rest
      rw [hx, hr]

/-- 沿序列轴（dim 1）聚合与 rank3 → rank4 的 FW_view 交换。
任意正 K,b,s,n,d；每个 shard 的输入形状为 [b,s,n*d]。
例如 K=2,b=1,s=8,n=4,d=16 对应 fresh TP2 的
SM [1,16,64] → [1,16,4,16]，PM [1,8,64] → [1,8,4,16]。 -/
theorem fw_view_unflatten_allGather_dim1_rank3
    (K b s n d : Nat) (xs : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hn : 0 < n) (hd : 0 < d)
    (hlen : xs.length = K)
    (hshape : ∀ x ∈ xs, x.shape = [b, s, n * d]) :
    fw_view [b, s * K, n, d] (allGatherPrimDimN 1 K 0 xs) =
      allGatherPrimDimN 1 K 0 (xs.map (fun x => fw_view [b, s, n, d] x)) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  let ys := (x0 :: rest).map (fun x => fw_view [b, s, n, d] x)
  have hylen : ys.length = K := (List.length_map ..).trans hlen
  have hyshape : ∀ y ∈ ys, y.shape = [b, s, n, d] := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    rfl
  have hyhead : (ys.head?.map (fun t => t.shape)).getD [] = [b, s, n, d] := by
    rfl
  have hgshape : (allGatherPrimDimN 1 K 0 ys).shape = [b, s * K, n, d] := by
    rw [allGatherPrimDimN_shape 1 K ys [b, s, n, d] hyhead]
    rfl
  have hlocalProd : prodShape [b, s, n, d] = prodShape [b, s, n * d] := by
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  have hmap : ys.map (fun x => fw_view [b, s, n * d] x) = x0 :: rest :=
    viewUnflatten_map_roundtrip [b, s, n, d] [b, s, n * d]
      (x0 :: rest) hlocalProd hshape
  have hflat := fw_view_allGatherPrimDimN_dim1_rank4_to_rank3
    K b s n d ys hK hb hs hn hd hylen hyshape
  rw [hmap] at hflat
  have hfullProd : prodShape [b, s * K, n * d] = prodShape [b, s * K, n, d] := by
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  calc
    fw_view [b, s * K, n, d] (allGatherPrimDimN 1 K 0 (x0 :: rest)) =
        fw_view [b, s * K, n, d]
          (fw_view [b, s * K, n * d] (allGatherPrimDimN 1 K 0 ys)) :=
      congrArg (fw_view [b, s * K, n, d]) hflat.symm
    _ = allGatherPrimDimN 1 K 0 ys :=
      viewUnflatten_roundtrip [b, s * K, n * d] [b, s * K, n, d]
        (allGatherPrimDimN 1 K 0 ys) hgshape hfullProd

/-- 沿 head 轴（dim 2）聚合与 rank3 → rank4 的 FW_view 交换。
每个 shard 的 [b,s,n*d] 拆为 [b,s,n,d]，全局 head 数为 n*K。
复用已经证明的 flatten 交换律和 view 往返恒等，无需重新证明索引算术。 -/
theorem fw_view_unflatten_allGather_dim2_rank3
    (K b s n d : Nat) (xs : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hn : 0 < n) (hd : 0 < d)
    (hlen : xs.length = K)
    (hshape : ∀ x ∈ xs, x.shape = [b, s, n * d]) :
    fw_view [b, s, n * K, d] (allGatherPrimDimN 2 K 0 xs) =
      allGatherPrimDimN 2 K 0 (xs.map (fun x => fw_view [b, s, n, d] x)) := by
  have hne : xs ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  let ys := (x0 :: rest).map (fun x => fw_view [b, s, n, d] x)
  have hylen : ys.length = K := (List.length_map ..).trans hlen
  have hyshape : ∀ y ∈ ys, y.shape = [b, s, n, d] := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    rfl
  have hyhead : (ys.head?.map (fun t => t.shape)).getD [] = [b, s, n, d] := by
    rfl
  have hgshape : (allGatherPrimDimN 2 K 0 ys).shape = [b, s, n * K, d] := by
    rw [allGatherPrimDimN_shape 2 K ys [b, s, n, d] hyhead]
    rfl
  have hlocalProd : prodShape [b, s, n, d] = prodShape [b, s, n * d] := by
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  have hmap : ys.map (fun x => fw_view [b, s, n * d] x) = x0 :: rest :=
    viewUnflatten_map_roundtrip [b, s, n, d] [b, s, n * d]
      (x0 :: rest) hlocalProd hshape
  have hflat := fw_view_allGatherPrimDimN_dim2_rank4_to_rank3
    K b s n d ys hK hb hs hn hd hylen hyshape
  rw [hmap] at hflat
  have hfullProd : prodShape [b, s, (n * K) * d] = prodShape [b, s, n * K, d] := by
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_assoc]
  calc
    fw_view [b, s, n * K, d] (allGatherPrimDimN 2 K 0 (x0 :: rest)) =
        fw_view [b, s, n * K, d]
          (fw_view [b, s, (n * K) * d] (allGatherPrimDimN 2 K 0 ys)) :=
      congrArg (fw_view [b, s, n * K, d]) hflat.symm
    _ = allGatherPrimDimN 2 K 0 ys :=
      viewUnflatten_roundtrip [b, s, (n * K) * d] [b, s, n * K, d]
        (allGatherPrimDimN 2 K 0 ys) hgshape hfullProd

end

end TrainVerify.Denote
