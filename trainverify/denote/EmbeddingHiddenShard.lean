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
    simp only [prodShape, List.foldl, Nat.mul_one]
    nlinarith [Nat.mul_le_mul_right (cols * 2) hrow]
  have hpieceShape := hxs r hr
  have hpieceIdx : row * cols + col <
      prodShape (xs.getD r (zeroTensor [rows, cols])).shape := by
    rw [hpieceShape]
    simp only [prodShape, List.foldl, Nat.mul_one]
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
  simp only [prodShape, List.foldl, Nat.mul_one] at hidx
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
