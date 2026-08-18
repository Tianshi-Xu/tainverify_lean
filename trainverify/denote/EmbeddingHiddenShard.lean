import denote.ChunkGatherDim0

/-!
# Hidden-sharded embedding reconstruction

Generic two-rank lemmas for weights sharded along the hidden dimension.  These
are independent of generated tensor ids and model sizes.
-/

namespace TrainVerify.Denote

/-- Read one element from a two-way dimension-1 gather of matrix shards. -/
theorem allGatherPrimDimN1_two_valAt
    (rows cols : Nat) (xs : List Tensor)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [rows, cols])
    (hxs : ∀ r (_ : r < 2),
      (xs.getD r (zeroTensor [rows, cols])).shape = [rows, cols])
    (row : Nat) (hrow : row < rows) (r : Nat) (hr : r < 2)
    (col : Nat) (hcol : col < cols) :
    valAt (allGatherPrimDimN 1 2 0 xs)
        (row * (cols * 2) + (r * cols + col)) =
      valAt (xs.getD r (zeroTensor [rows, cols])) (row * cols + col) := by
  have hshape : (allGatherPrimDimN 1 2 0 xs).shape = [rows, cols * 2] := by
    rw [allGatherPrimDimN_shape 1 2 xs [rows, cols] hhead]
    simp [List.set, List.getD]
  have hfullcol : r * cols + col < cols * 2 := by
    interval_cases r <;> omega
  have hidx : row * (cols * 2) + (r * cols + col) <
      prodShape (allGatherPrimDimN 1 2 0 xs).shape := by
    rw [hshape]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one]
    nlinarith [Nat.mul_le_mul_right (cols * 2) hrow]
  have hpieceShape := hxs r hr
  have hpieceIdx : row * cols + col <
      prodShape (xs.getD r (zeroTensor [rows, cols])).shape := by
    rw [hpieceShape]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one]
    nlinarith [Nat.mul_le_mul_right cols hrow]
  have hcolsne : cols ≠ 0 := hcols.ne'
  have htwocolsne : cols * 2 ≠ 0 := by omega
  have hgetD1 : ([rows, cols] : List Nat).getD 1 0 = cols := rfl
  have hdrop2 : List.foldl (fun (a b : Nat) => a * b) 1
      (List.drop (1 + 1) ([rows, cols] : List Nat)) = 1 := by rfl
  have hdivFull :
      (row * (cols * 2) + (r * cols + col)) / (cols * 2) = row := by
    rw [show row * (cols * 2) + (r * cols + col) =
        (r * cols + col) + (cols * 2) * row by ring,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hfullcol, Nat.zero_add]
  have hmodFull :
      (row * (cols * 2) + (r * cols + col)) % (cols * 2) = r * cols + col := by
    rw [show row * (cols * 2) + (r * cols + col) =
        (r * cols + col) + (cols * 2) * row by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hfullcol]
  have hdivCols : (r * cols + col) / cols = r := by
    rw [show r * cols + col = col + cols * r by ring,
      Nat.add_mul_div_left _ _ hcols, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmodCols : (r * cols + col) % cols = col := by
    rw [show r * cols + col = col + cols * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have h0 : valAt (allGatherPrimDimN 1 2 0 xs)
      (row * (cols * 2) + (r * cols + col)) =
      (allGatherPrimDimN 1 2 0 xs).val
        ⟨row * (cols * 2) + (r * cols + col), hidx⟩ := by
    exact valAt_of_lt _ _ hidx
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead, hgetD1, hdrop2,
    Nat.mul_one, if_neg hcolsne, if_neg htwocolsne,
    if_neg (show (1 : Nat) ≠ 0 by decide)]
  rw [hdivFull, hmodFull, Nat.div_one, Nat.mod_one, hdivCols, hmodCols]
  simp only [Nat.mul_one, Nat.add_zero, valAt, hpieceIdx, dif_pos]

/-- Read one element from a rank-count-polymorphic dimension-1 matrix gather. -/
theorem allGatherPrimDimN1_k_valAt
    (K rows cols : Nat) (xs : List Tensor)
    (hK : 0 < K) (hrows : 0 < rows) (hcols : 0 < cols)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [rows, cols])
    (row : Nat) (hrow : row < rows) (r : Nat) (hr : r < K)
    (col : Nat) (hcol : col < cols) :
    valAt (allGatherPrimDimN 1 K 0 xs)
        (row * (cols * K) + (r * cols + col)) =
      valAt (xs.getD r (zeroTensor [rows, cols])) (row * cols + col) := by
  have hcolsK : 0 < cols * K := Nat.mul_pos hcols hK
  have hrc : r * cols + col < cols * K := by
    calc
      r * cols + col < (r + 1) * cols := by nlinarith
      _ ≤ K * cols := Nat.mul_le_mul_right cols hr
      _ = cols * K := by ring
  have hshape : (allGatherPrimDimN 1 K 0 xs).shape = [rows, cols * K] := by
    rw [allGatherPrimDimN_shape 1 K xs [rows, cols] hhead]
    simp [List.set, List.getD]
  have hidx : row * (cols * K) + (r * cols + col) <
      prodShape (allGatherPrimDimN 1 K 0 xs).shape := by
    rw [hshape]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one]
    calc
      row * (cols * K) + (r * cols + col) < row * (cols * K) + cols * K :=
        Nat.add_lt_add_left hrc _
      _ = (row + 1) * (cols * K) := by ring
      _ ≤ rows * (cols * K) :=
        Nat.mul_le_mul_right (cols * K) (Nat.succ_le_iff.mpr hrow)
  rw [valAt_of_lt _ _ hidx]
  unfold allGatherPrimDimN
  simp only [hhead, Tensor.mkShape, List.getD_cons_succ, List.getD_cons_zero,
    List.drop, List.foldl, Nat.mul_one,
    show cols ≠ 0 from Nat.ne_of_gt hcols,
    show cols * K ≠ 0 from Nat.ne_of_gt hcolsK,
    show (1 : Nat) ≠ 0 by decide, ite_false]
  have hdiv : (row * (cols * K) + (r * cols + col)) / (cols * K) = row := by
    rw [show row * (cols * K) + (r * cols + col) =
        (r * cols + col) + (cols * K) * row by ring,
      Nat.add_mul_div_left _ _ hcolsK, Nat.div_eq_of_lt hrc, Nat.zero_add]
  have hmod : (row * (cols * K) + (r * cols + col)) % (cols * K) =
      r * cols + col := by
    rw [show row * (cols * K) + (r * cols + col) =
        (r * cols + col) + (cols * K) * row by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrc]
  have hdivCols : (r * cols + col) / cols = r := by
    rw [show r * cols + col = col + cols * r by ring,
      Nat.add_mul_div_left _ _ hcols, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmodCols : (r * cols + col) % cols = col := by
    rw [show r * cols + col = col + cols * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  rw [hdiv, hmod, Nat.div_one, Nat.mod_one, hdivCols, hmodCols]
  congr 1

/-- Read one element from a rank-count-polymorphic last-axis 3D gather. -/
theorem allGatherPrimDimN2_k_valAt
    (K b tokens cols : Nat) (xs : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (htokens : 0 < tokens) (hcols : 0 < cols)
    (hhead : (xs.head?.map (fun t => t.shape)).getD [] = [b, tokens, cols])
    (row : Nat) (hrow : row < b * tokens) (r : Nat) (hr : r < K)
    (col : Nat) (hcol : col < cols) :
    valAt (allGatherPrimDimN 2 K 0 xs)
        (row * (cols * K) + (r * cols + col)) =
      valAt (xs.getD r (zeroTensor [b, tokens, cols])) (row * cols + col) := by
  have hcolsK : 0 < cols * K := Nat.mul_pos hcols hK
  have hrc : r * cols + col < cols * K := by
    calc
      r * cols + col < (r + 1) * cols := by nlinarith
      _ ≤ K * cols := Nat.mul_le_mul_right cols hr
      _ = cols * K := by ring
  have hshape : (allGatherPrimDimN 2 K 0 xs).shape = [b, tokens, cols * K] := by
    rw [allGatherPrimDimN_shape 2 K xs [b, tokens, cols] hhead]
    simp [List.set, List.getD]
  have hidx : row * (cols * K) + (r * cols + col) <
      prodShape (allGatherPrimDimN 2 K 0 xs).shape := by
    rw [hshape]
    simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one]
    calc
      row * (cols * K) + (r * cols + col) < row * (cols * K) + cols * K :=
        Nat.add_lt_add_left hrc _
      _ = (row + 1) * (cols * K) := by ring
      _ ≤ (b * tokens) * (cols * K) :=
        Nat.mul_le_mul_right (cols * K) (Nat.succ_le_iff.mpr hrow)
  rw [valAt_of_lt _ _ hidx]
  unfold allGatherPrimDimN
  simp only [hhead, Tensor.mkShape, List.getD_cons_succ, List.getD_cons_zero,
    List.drop, List.foldl, Nat.mul_one,
    show cols ≠ 0 from Nat.ne_of_gt hcols,
    show cols * K ≠ 0 from Nat.ne_of_gt hcolsK,
    show (1 : Nat) ≠ 0 by decide, ite_false]
  have hdiv : (row * (cols * K) + (r * cols + col)) / (cols * K) = row := by
    rw [show row * (cols * K) + (r * cols + col) =
        (r * cols + col) + (cols * K) * row by ring,
      Nat.add_mul_div_left _ _ hcolsK, Nat.div_eq_of_lt hrc, Nat.zero_add]
  have hmod : (row * (cols * K) + (r * cols + col)) % (cols * K) =
      r * cols + col := by
    rw [show row * (cols * K) + (r * cols + col) =
        (r * cols + col) + (cols * K) * row by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrc]
  have hdivCols : (r * cols + col) / cols = r := by
    rw [show r * cols + col = col + cols * r by ring,
      Nat.add_mul_div_left _ _ hcols, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmodCols : (r * cols + col) % cols = col := by
    rw [show r * cols + col = col + cols * r by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  rw [hdiv, hmod, Nat.div_one, Nat.mod_one, hdivCols, hmodCols]
  congr 1

/-- Embedding commutes with an arbitrary nonempty ordered hidden-axis shard list.
The rank count is authority from `Ws.length`; no concrete rank count is encoded. -/
theorem fw_embedding_hidden_shards_k_rank
    (K b tokens vocab hidden : Nat) (ids : Tensor) (Ws : List Tensor)
    (hK : 0 < K) (hb : 0 < b) (htokens : 0 < tokens)
    (hvocab : 0 < vocab) (hhidden : 0 < hidden)
    (hlen : Ws.length = K) (hids : ids.shape = [b, tokens])
    (hWs : ∀ W ∈ Ws, W.shape = [vocab, hidden]) :
    fw_embedding ids (allGatherPrimDimN 1 K 0 Ws) =
      allGatherPrimDimN 2 K 0 (Ws.map (fun W => fw_embedding ids W)) := by
  have hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [vocab, hidden] := by
    cases hlist : Ws with
    | nil => simp [hlist] at hlen; omega
    | cons W rest =>
      simp only [hlist, List.head?, Option.map, Option.getD]
      exact hWs W (hlist ▸ List.mem_cons_self ..)
  have hfullW : (allGatherPrimDimN 1 K 0 Ws).shape = [vocab, hidden * K] := by
    rw [allGatherPrimDimN_shape 1 K Ws [vocab, hidden] hhead]
    simp [List.set, List.getD]
  have hmapHead : ((Ws.map (fun W => fw_embedding ids W)).head?.map
      (fun t => t.shape)).getD [] = [b, tokens, hidden] := by
    cases hlist : Ws with
    | nil => simp [hlist] at hlen; omega
    | cons W rest =>
      simp only [hlist, List.map, List.head?, Option.map, Option.getD]
      rw [fw_embedding_shape, hids, hWs W (hlist ▸ List.mem_cons_self ..)]
      rfl
  have hlhs : (fw_embedding ids (allGatherPrimDimN 1 K 0 Ws)).shape =
      [b, tokens, hidden * K] := by
    rw [fw_embedding_shape, hids, hfullW]
    rfl
  have hrhs : (allGatherPrimDimN 2 K 0
      (Ws.map (fun W => fw_embedding ids W))).shape = [b, tokens, hidden * K] := by
    rw [allGatherPrimDimN_shape 2 K _ [b, tokens, hidden] hmapHead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs, hrhs])
  intro idx hidx
  rw [hlhs] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul] at hidx
  let row := idx / (hidden * K)
  let fullCol := idx % (hidden * K)
  let r := fullCol / hidden
  let col := fullCol % hidden
  have hhiddenK : 0 < hidden * K := Nat.mul_pos hhidden hK
  have hrow : row < b * tokens := by
    dsimp [row]
    apply Nat.div_lt_of_lt_mul
    calc
      idx < b * tokens * (hidden * K) := hidx
      _ = (hidden * K) * (b * tokens) := by ring
  have hfullCol : fullCol < hidden * K := Nat.mod_lt _ hhiddenK
  have hr : r < K := by
    dsimp [r]
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hfullCol)
  have hcol : col < hidden := by
    dsimp [col]
    exact Nat.mod_lt _ hhidden
  have hfullColDecomp : fullCol = r * hidden + col := by
    dsimp [r, col]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod fullCol hidden).symm
  have hidxDecomp : idx = row * (hidden * K) + (r * hidden + col) := by
    calc
      idx = row * (hidden * K) + fullCol := by
        dsimp [row, fullCol]
        rw [Nat.mul_comm]
        exact (Nat.div_add_mod idx (hidden * K)).symm
      _ = row * (hidden * K) + (r * hidden + col) := by rw [hfullColDecomp]
  rw [hidxDecomp]
  rw [fw_embedding_valAt]
  have hlastFullW : lastD (allGatherPrimDimN 1 K 0 Ws).shape = hidden * K := by
    rw [hfullW]
    rfl
  have hlhsBound : row * (hidden * K) + (r * hidden + col) <
      prodShape (ids.shape ++ [lastD (allGatherPrimDimN 1 K 0 Ws).shape]) := by
    rw [hids, hlastFullW]
    simpa [prodShape, ← hidxDecomp] using hidx
  rw [dif_pos hlhsBound, hlastFullW]
  rw [allGatherPrimDimN2_k_valAt K b tokens hidden
    (Ws.map (fun W => fw_embedding ids W)) hK hb htokens hhidden hmapHead
    row hrow r hr col hcol]
  have hrlen : r < Ws.length := by omega
  have hmapGet : (Ws.map (fun W => fw_embedding ids W)).getD r
      (zeroTensor [b, tokens, hidden]) = fw_embedding ids Ws[r] := by
    simp [List.getD, List.getElem?_eq_getElem hrlen, List.getElem_map]
  rw [hmapGet, fw_embedding_valAt]
  have hWr : Ws[r].shape = [vocab, hidden] := hWs _ (List.getElem_mem hrlen)
  have hrhsBound : row * hidden + col < prodShape (ids.shape ++ [lastD Ws[r].shape]) := by
    rw [hids, hWr]
    rw [show lastD [vocab, hidden] = hidden by rfl]
    rw [show prodShape ([b, tokens] ++ [hidden]) = b * tokens * hidden by simp [prodShape]]
    calc
      row * hidden + col < row * hidden + hidden := Nat.add_lt_add_left hcol _
      _ = (row + 1) * hidden := by ring
      _ ≤ (b * tokens) * hidden :=
        Nat.mul_le_mul_right hidden (Nat.succ_le_iff.mpr hrow)
  rw [dif_pos hrhsBound, hWr]
  have hdivFull :
      (row * (hidden * K) + (r * hidden + col)) / (hidden * K) = row := by
    rw [show row * (hidden * K) + (r * hidden + col) =
        (r * hidden + col) + (hidden * K) * row by ring,
      Nat.add_mul_div_left _ _ hhiddenK,
      Nat.div_eq_of_lt (by simpa [hfullColDecomp] using hfullCol), Nat.zero_add]
  have hmodFull :
      (row * (hidden * K) + (r * hidden + col)) % (hidden * K) =
        r * hidden + col := by
    rw [show row * (hidden * K) + (r * hidden + col) =
        (r * hidden + col) + (hidden * K) * row by ring,
      Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by simpa [hfullColDecomp] using hfullCol)]
  rw [hdivFull, hmodFull]
  simp only [lastD, List.getLast?_cons, Option.getD_some]
  change valAt (allGatherPrimDimN 1 K 0 Ws)
      (scalarToNat (valAt ids row) * (hidden * K) + (r * hidden + col)) =
    valAt Ws[r] (scalarToNat (valAt ids ((row * hidden + col) / hidden)) * hidden +
      (row * hidden + col) % hidden)
  have hdiv : (row * hidden + col) / hidden = row := by
    rw [show row * hidden + col = col + hidden * row by ring,
      Nat.add_mul_div_left _ _ hhidden, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod : (row * hidden + col) % hidden = col := by
    rw [show row * hidden + col = col + hidden * row by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  rw [hdiv, hmod]
  let label := scalarToNat (valAt ids row)
  by_cases hlabel : label < vocab
  · have hpiece : Ws.getD r (zeroTensor [vocab, hidden]) = Ws[r] := by
      simp [List.getD, List.getElem?_eq_getElem hrlen]
    rw [← hpiece]
    exact allGatherPrimDimN1_k_valAt K vocab hidden Ws hK hvocab hhidden hhead
      label hlabel r hr col hcol
  · have hfullZero : valAt (allGatherPrimDimN 1 K 0 Ws)
        (label * (hidden * K) + (r * hidden + col)) = 0 := by
      have hnot : ¬ label * (hidden * K) + (r * hidden + col) <
          prodShape (allGatherPrimDimN 1 K 0 Ws).shape := by
        apply Nat.not_lt.mpr
        rw [hfullW]
        simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one]
        calc
          vocab * (hidden * K) ≤ label * (hidden * K) :=
            Nat.mul_le_mul_right (hidden * K) (Nat.le_of_not_gt hlabel)
          _ ≤ label * (hidden * K) + (r * hidden + col) := Nat.le_add_right _ _
      simp [valAt, hnot]
    have hpieceZero : valAt Ws[r] (label * hidden + col) = 0 := by
      have hnot : ¬ label * hidden + col < prodShape Ws[r].shape := by
        apply Nat.not_lt.mpr
        rw [hWr]
        simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one]
        calc
          vocab * hidden ≤ label * hidden :=
            Nat.mul_le_mul_right hidden (Nat.le_of_not_gt hlabel)
          _ ≤ label * hidden + col := Nat.le_add_right _ _
      simp [valAt, hnot]
    rw [hfullZero, hpieceZero]

/-- Embedding commutes with gathering two weight shards on the hidden axis.
The out-of-vocabulary branch is handled explicitly: both weight reads are
outside their matrix shapes and therefore evaluate to zero. -/
theorem fw_embedding_hidden_shards_two
    (tokens vocab hidden : Nat) (ids W0 W1 : Tensor)
    (htokens : 0 < tokens) (hvocab : 0 < vocab) (hhidden : 0 < hidden)
    (hids : ids.shape = [tokens])
    (hW0 : W0.shape = [vocab, hidden])
    (hW1 : W1.shape = [vocab, hidden]) :
    fw_embedding ids (allGatherPrimDimN 1 2 0 [W0, W1]) =
      allGatherPrimDimN 1 2 0 [fw_embedding ids W0, fw_embedding ids W1] := by
  have hWhead : (([W0, W1].head?.map (fun t => t.shape)).getD []) =
      [vocab, hidden] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hW0
  have hWget : ∀ r (_ : r < 2),
      ([W0, W1].getD r (zeroTensor [vocab, hidden])).shape = [vocab, hidden] := by
    intro r hr
    interval_cases r <;> simp [List.getD, hW0, hW1]
  have hE0 : (fw_embedding ids W0).shape = [tokens, hidden] := by
    rw [fw_embedding_shape, hids, hW0]
    rfl
  have hE1 : (fw_embedding ids W1).shape = [tokens, hidden] := by
    rw [fw_embedding_shape, hids, hW1]
    rfl
  have hEhead : (([fw_embedding ids W0, fw_embedding ids W1].head?.map
      (fun t => t.shape)).getD []) = [tokens, hidden] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hE0
  have hEget : ∀ r (_ : r < 2),
      ([fw_embedding ids W0, fw_embedding ids W1].getD r
        (zeroTensor [tokens, hidden])).shape = [tokens, hidden] := by
    intro r hr
    interval_cases r <;> simp [List.getD, hE0, hE1]
  have hfullW : (allGatherPrimDimN 1 2 0 [W0, W1]).shape =
      [vocab, hidden * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [vocab, hidden] hWhead]
    simp [List.set, List.getD]
  have hlhs : (fw_embedding ids (allGatherPrimDimN 1 2 0 [W0, W1])).shape =
      [tokens, hidden * 2] := by
    rw [fw_embedding_shape, hids, hfullW]
    rfl
  have hrhs : (allGatherPrimDimN 1 2 0
      [fw_embedding ids W0, fw_embedding ids W1]).shape =
      [tokens, hidden * 2] := by
    rw [allGatherPrimDimN_shape 1 2 _ [tokens, hidden] hEhead]
    simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs, hrhs])
  intro idx hidx
  rw [hlhs] at hidx
  simp only [prodShape, List.foldl, Nat.one_mul, Nat.mul_one] at hidx
  let token := idx / (hidden * 2)
  let fullCol := idx % (hidden * 2)
  let r := fullCol / hidden
  let col := fullCol % hidden
  have htwopos : 0 < hidden * 2 := by omega
  have htoken : token < tokens := by
    dsimp [token]
    apply Nat.div_lt_of_lt_mul
    calc
      idx < tokens * (hidden * 2) := by simpa using hidx
      _ = (hidden * 2) * tokens := by ring
  have hfullCol : fullCol < hidden * 2 := Nat.mod_lt _ htwopos
  have hr : r < 2 := by
    dsimp [r]
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hfullCol)
  have hcol : col < hidden := by
    dsimp [col]
    exact Nat.mod_lt _ hhidden
  have hfullColDecomp : fullCol = r * hidden + col := by
    dsimp [r, col]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod fullCol hidden).symm
  have hidxDecomp : idx = token * (hidden * 2) + (r * hidden + col) := by
    calc
      idx = token * (hidden * 2) + fullCol := by
        dsimp [token, fullCol]
        rw [Nat.mul_comm]
        exact (Nat.div_add_mod idx (hidden * 2)).symm
      _ = token * (hidden * 2) + (r * hidden + col) := by rw [hfullColDecomp]
  rw [hidxDecomp]
  rw [fw_embedding_valAt]
  have hlastFullW : lastD (allGatherPrimDimN 1 2 0 [W0, W1]).shape = hidden * 2 := by
    rw [hfullW]
    rfl
  have hlhsBound : token * (hidden * 2) + (r * hidden + col) <
      prodShape (ids.shape ++ [lastD (allGatherPrimDimN 1 2 0 [W0, W1]).shape]) := by
    rw [hids, hlastFullW]
    rw [← hidxDecomp]
    simpa [prodShape] using hidx
  rw [dif_pos hlhsBound]
  rw [hlastFullW]
  have hdivToken : (token * (hidden * 2) + (r * hidden + col)) / (hidden * 2) = token := by
    rw [show token * (hidden * 2) + (r * hidden + col) =
        (r * hidden + col) + (hidden * 2) * token by ring,
      Nat.add_mul_div_left _ _ htwopos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hmodToken : (token * (hidden * 2) + (r * hidden + col)) % (hidden * 2) =
      r * hidden + col := by
    rw [show token * (hidden * 2) + (r * hidden + col) =
        (r * hidden + col) + (hidden * 2) * token by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hdivToken, hmodToken]
  rw [allGatherPrimDimN1_two_valAt tokens hidden
    [fw_embedding ids W0, fw_embedding ids W1] htokens hhidden hEhead hEget
    token htoken r hr col hcol]
  have hpiece : [fw_embedding ids W0, fw_embedding ids W1].getD r
      (zeroTensor [tokens, hidden]) =
      fw_embedding ids ([W0, W1].getD r (zeroTensor [vocab, hidden])) := by
    interval_cases r <;> simp [List.getD]
  rw [hpiece, fw_embedding_valAt]
  have hpieceBound : token * hidden + col <
      prodShape (ids.shape ++ [lastD ([W0, W1].getD r
        (zeroTensor [vocab, hidden])).shape]) := by
    have hlastPiece : lastD ([W0, W1].getD r
        (zeroTensor [vocab, hidden])).shape = hidden := by
      rw [hWget r hr]
      rfl
    have hshape : ids.shape ++ [lastD ([W0, W1].getD r
        (zeroTensor [vocab, hidden])).shape] = [tokens, hidden] := by
      rw [hids, hlastPiece]
      rfl
    rw [hshape]
    simp only [prodShape, List.foldl, Nat.one_mul]
    calc
      token * hidden + col < token * hidden + hidden := by omega
      _ = (token + 1) * hidden := by ring
      _ ≤ tokens * hidden := Nat.mul_le_mul_right hidden htoken
  rw [dif_pos hpieceBound, hWget r hr]
  change valAt (allGatherPrimDimN 1 2 0 [W0, W1])
      (scalarToNat (valAt ids token) * (hidden * 2) + (r * hidden + col)) =
    valAt ([W0, W1].getD r (zeroTensor [vocab, hidden]))
      (scalarToNat (valAt ids ((token * hidden + col) / hidden)) * hidden +
        (token * hidden + col) % hidden)
  have hdivPiece : (token * hidden + col) / hidden = token := by
    rw [show token * hidden + col = col + hidden * token by ring,
      Nat.add_mul_div_left _ _ hhidden, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmodPiece : (token * hidden + col) % hidden = col := by
    rw [show token * hidden + col = col + hidden * token by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  rw [hdivPiece, hmodPiece]
  let label := scalarToNat (valAt ids token)
  change valAt (allGatherPrimDimN 1 2 0 [W0, W1])
      (label * (hidden * 2) + (r * hidden + col)) =
    valAt ([W0, W1].getD r (zeroTensor [vocab, hidden]))
      (label * hidden + col)
  by_cases hlabel : label < vocab
  · exact allGatherPrimDimN1_two_valAt vocab hidden [W0, W1]
      hvocab hhidden hWhead hWget label hlabel r hr col hcol
  · have hfullZero : valAt (allGatherPrimDimN 1 2 0 [W0, W1])
        (label * (hidden * 2) + (r * hidden + col)) = 0 := by
      have hnot : ¬ label * (hidden * 2) + (r * hidden + col) <
          prodShape (allGatherPrimDimN 1 2 0 [W0, W1]).shape := by
        have hm := Nat.mul_le_mul_right (hidden * 2) (Nat.le_of_not_gt hlabel)
        apply Nat.not_lt.mpr
        calc
          prodShape (allGatherPrimDimN 1 2 0 [W0, W1]).shape =
              vocab * (hidden * 2) := by
            rw [hfullW]
            simp only [prodShape, List.foldl, Nat.one_mul]
          _ ≤ label * (hidden * 2) := hm
          _ ≤ label * (hidden * 2) + (r * hidden + col) := Nat.le_add_right _ _
      simp [valAt, hnot]
    have hpieceZero : valAt ([W0, W1].getD r (zeroTensor [vocab, hidden]))
        (label * hidden + col) = 0 := by
      have hnot : ¬ label * hidden + col <
          prodShape ([W0, W1].getD r (zeroTensor [vocab, hidden])).shape := by
        have hm := Nat.mul_le_mul_right hidden (Nat.le_of_not_gt hlabel)
        apply Nat.not_lt.mpr
        calc
          prodShape ([W0, W1].getD r (zeroTensor [vocab, hidden])).shape =
              vocab * hidden := by
            rw [hWget r hr]
            simp only [prodShape, List.foldl, Nat.one_mul]
          _ ≤ label * hidden := hm
          _ ≤ label * hidden + col := Nat.le_add_right _ _
      unfold valAt
      rw [dif_neg hnot]
    rw [hfullZero, hpieceZero]

/-- Hidden-sharded embedding followed by `(idim = 1, odim = 0)` all-to-all
redistributes hidden width into sequence shards; gathering rank outputs on
sequence dimension 0 recovers the full embedding. -/
theorem fw_embedding_hidden_shards_allToAll_two
    (tokens vocab hidden : Nat) (ids W0 W1 : Tensor)
    (htokens : 0 < tokens) (hvocab : 0 < vocab) (hhidden : 0 < hidden)
    (hids : ids.shape = [2 * tokens])
    (hW0 : W0.shape = [vocab, hidden])
    (hW1 : W1.shape = [vocab, hidden]) :
    fw_embedding ids (allGatherPrimDimN 1 2 0 [W0, W1]) =
      allGatherPrimDimN 0 2 0
        [allToAllPrimWithDims 2 0 [fw_embedding ids W0, fw_embedding ids W1] 1 0,
         allToAllPrimWithDims 2 1 [fw_embedding ids W0, fw_embedding ids W1] 1 0] := by
  have hE0 : (fw_embedding ids W0).shape = [2 * tokens, hidden] := by
    rw [fw_embedding_shape, hids, hW0]
    rfl
  have hEhead : (([fw_embedding ids W0, fw_embedding ids W1].head?.map
      (fun t => t.shape)).getD []) = [2 * tokens, hidden] := by
    simp only [List.head?, Option.map, Option.getD]
    exact hE0
  let fullE := allGatherPrimDimN 1 2 0 [fw_embedding ids W0, fw_embedding ids W1]
  have hfullE : fullE.shape = [2 * tokens, hidden * 2] := by
    dsimp [fullE]
    rw [allGatherPrimDimN_shape 1 2 _ [2 * tokens, hidden] hEhead]
    simp [List.set, List.getD]
  rw [fw_embedding_hidden_shards_two (2 * tokens) vocab hidden ids W0 W1
    (by omega) hvocab hhidden hids hW0 hW1]
  change fullE = allGatherPrimDimN 0 2 0
    [chunkPrimDimN 0 2 0 fullE, chunkPrimDimN 0 2 1 fullE]
  exact (allGatherPrimDimN_chunkPrimDimN_id_dim0_2 fullE (2 * tokens) (hidden * 2)
    hfullE (by omega) (by omega) (by omega)).symm

end TrainVerify.Denote
