/- Auto-generated pattern proof file.
   Pattern: 6
   Hash: 50d559b40c026d8e
   Goals: 6, 7, 32, 58, 83
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_129

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_6_goalIds : List Nat := [6, 7, 32, 58, 83]
inductive pattern_6_target : Prop → Prop
  | goal_6 : pattern_6_target goal_6_stmt
  | goal_7 : pattern_6_target goal_7_stmt
  | goal_32 : pattern_6_target goal_32_stmt
  | goal_58 : pattern_6_target goal_58_stmt
  | goal_83 : pattern_6_target goal_83_stmt

def pattern_6_stmt : Prop :=
  ∀ {target : Prop}, pattern_6_target target → target

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

/-! ## Helper lemmas

Pointwise valAt characterizations of `chunkPrimDimN` along dim 1 for the
shape used in this pattern (`x : [1, 8, 32]` sharded into 4 pieces
`[1, 2, 32]`). These are the building blocks for the `fw_linear`
distribution helper used by `prove_pattern_6`. -/

private lemma chunk1_x_1_8_32_shape (x : Tensor) (r : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) :
    (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
  rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
  simp [List.set, List.getD]

private lemma chunk1_x_1_8_32_valAt (x : Tensor) (r : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4)
    (jLocal : Nat) (k : Nat) (hjLocal : jLocal < 2) (hk : k < 32) :
    valAt (chunkPrimDimN 1 4 r x) (jLocal * 32 + k) =
      valAt x ((r * 2 + jLocal) * 32 + k) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] :=
    chunk1_x_1_8_32_shape x r hx hr
  have hflat_lt : jLocal * 32 + k < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hflat_lt]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.getD,
    show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (32 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega, ite_false]
  have hr' : r % 4 = r := Nat.mod_eq_of_lt hr
  have h_lt : jLocal * 32 + k < 64 := by omega
  have h_div : (jLocal * 32 + k) / 64 = 0 := Nat.div_eq_of_lt h_lt
  have h_mod : (jLocal * 32 + k) % 64 = jLocal * 32 + k := Nat.mod_eq_of_lt h_lt
  have h_div32 : (jLocal * 32 + k) / 32 = jLocal := by
    have heq : jLocal * 32 + k = k + 32 * jLocal := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by norm_num : (0:Nat) < 32),
        Nat.div_eq_of_lt hk, Nat.zero_add]
  have h_mod32 : (jLocal * 32 + k) % 32 = k := by
    have heq : jLocal * 32 + k = k + 32 * jLocal := by ring
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  have hjm : jLocal % 2 = jLocal := Nat.mod_eq_of_lt hjLocal
  have hidx : (jLocal * 32 + k) / (8 / 4 * (1 * 32)) * (8 * (1 * 32)) +
      (r % 4 * (8 / 4) +
        (jLocal * 32 + k) % (8 / 4 * (1 * 32)) / (1 * 32)) * (1 * 32) +
        (jLocal * 32 + k) % (8 / 4 * (1 * 32)) % (1 * 32) =
      (r * 2 + jLocal) * 32 + k := by
    simp only [show (8 / 4 * (1 * 32) : Nat) = 64 by norm_num,
      show (8 * (1 * 32) : Nat) = 256 by norm_num,
      show (1 * 32 : Nat) = 32 by norm_num,
      show (8 / 4 : Nat) = 2 by norm_num,
      h_div, h_mod, h_div32, h_mod32, hr', hjm]
    ring
  rw [show (8 / 4 * (1 * 32) : Nat) = 64 by norm_num] at *
  simp only [show (64 : Nat) ≠ 0 by omega, ite_false]
  rw [hidx]

/-! ### Helper: 3D `fw_linear` valAt formula for shape `[1, s, 32]` with `w : [32, 32]`. -/

private lemma fw_linear_valAt_b1_s_32 (s : Nat) (hs : 0 < s) (x w : Tensor)
    (hx : x.shape = [1, s, 32]) (hw : w.shape = [32, 32])
    (p : Nat) (hp : p < s) (c : Nat) (hc : c < 32) :
    valAt (fw_linear x w) (p * 32 + c) =
      ∑ k ∈ Finset.range 32, valAt x (p * 32 + k) * valAt w (c * 32 + k) := by
  have hshape : (fw_linear x w).shape = [1, s, 32] :=
    fw_linear_3d_shape 1 s 32 32 x w hx hw
  have hp32 : p * 32 < s * 32 :=
    (Nat.mul_lt_mul_right (by omega : 0 < 32)).mpr hp
  have hflat_lt' : p * 32 + c < s * 32 := by omega
  have hs32_ne : s * 32 ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h32_ne : (32 : Nat) ≠ 0 := by omega
  have hd : (p * 32 + c) / (s * 32) = 0 := Nat.div_eq_of_lt hflat_lt'
  have hm : (p * 32 + c) % (s * 32) = p * 32 + c := Nat.mod_eq_of_lt hflat_lt'
  have hd32 : (p * 32 + c) / 32 = p := by
    have heq : p * 32 + c = c + 32 * p := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by norm_num : (0:Nat) < 32),
        Nat.div_eq_of_lt hc, Nat.zero_add]
  have hm32 : (p * 32 + c) % 32 = c := by
    have heq : p * 32 + c = c + 32 * p := by ring
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  -- Unfold fw_linear to its 3D arm Tensor.mkShape body
  have hfw_eq : fw_linear x w = Tensor.mkShape [1, s, 32] (fun outIdx =>
        let flat := outIdx.1
        let so := s * 32
        let row := if so = 0 then 0 else flat / so
        let rem := if so = 0 then 0 else flat % so
        let seq := if (32 : Nat) = 0 then 0 else rem / 32
        let col := if (32 : Nat) = 0 then 0 else rem % 32
        ∑ j ∈ Finset.range 32,
          (valAt x ((row * s + seq) * 32 + j)) * (valAt w (col * 32 + j))) := by
    simp only [fw_linear, hx, hw]
  rw [hfw_eq]
  have hflat_lt : p * 32 + c < prodShape ([1, s, 32] : Shape) := by
    simp [prodShape]; omega
  rw [valAt_of_lt _ _ hflat_lt]
  simp only [Tensor.mkShape, hs32_ne, h32_ne, ite_false, hd, hm, hd32, hm32]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  ring

/-! ### Helper: valAt of dim-1 `allGatherPrimDimN` on `[1, 2, 32]` shards. -/

private lemma valAt_ag1_1_2_32_pj (xs : List Tensor) (p j : Nat)
    (hhead : (xs.head?.map (·.shape)).getD [] = [1, 2, 32])
    (hp : p < 8) (hj : j < 32) :
    valAt (allGatherPrimDimN 1 4 0 xs) (p * 32 + j) =
      valAt (xs.getD (p / 2) (zeroTensor [1, 2, 32])) ((p % 2) * 32 + j) := by
  have hshape_out : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hidx_lt : p * 32 + j < 256 := by
    have : p * 32 ≤ 7 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  have hlt_prod : p * 32 + j < prodShape (allGatherPrimDimN 1 4 0 xs).shape := by
    rw [hshape_out]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hlt_prod]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.drop, List.foldl,
    show ([1, 2, 32] : List Nat).getD 1 0 = 2 from rfl,
    show (2 : Nat) * 4 * 32 = 256 from by norm_num,
    show (2 : Nat) * 32 = 64 from by norm_num,
    show (256 : Nat) ≠ 0 from by omega,
    show (32 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega,
    ite_false]
  have hd256 : (p * 32 + j) / 256 = 0 := Nat.div_eq_of_lt hidx_lt
  have hm256 : (p * 32 + j) % 256 = p * 32 + j := Nat.mod_eq_of_lt hidx_lt
  have hd32 : (p * 32 + j) / 32 = p := by
    have heq : p * 32 + j = j + 32 * p := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by norm_num : (0:Nat) < 32),
        Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm32 : (p * 32 + j) % 32 = j := by
    have heq : p * 32 + j = j + 32 * p := by ring
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [hm256, hd32, hm32]
  congr 1
  rw [hd256]
  ring

/-! ### Helper: chunk-of-allGather inverse for `[1,2,32]` shards along dim 1.

`chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [t0,t1,t2,t3]) = t_r` when each
`t_i` has shape `[1,2,32]`. Adapted from Pattern_5. -/

private lemma chunk1_4_of_ag1_1_2_32 (xs : List Tensor) (r : Nat) (hr : r < 4)
    (hhead : (xs.head?.map (·.shape)).getD [] = [1, 2, 32])
    (hshapes : ∀ i, i < 4 →
      (xs.getD i (zeroTensor [1, 2, 32])).shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 xs) =
      xs.getD r (zeroTensor [1, 2, 32]) := by
  have hag_shape : (allGatherPrimDimN 1 4 0 xs).shape = [1, 8, 32] := by
    simp [allGatherPrimDimN, Tensor.mkShape, hhead]
  have hchunk_shape : (chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 xs)).shape =
      [1, 2, 32] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hag_shape (by omega)]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hchunk_shape, hshapes r hr]
  · intro idx hidx
    have hidx_lt : idx < 64 := by
      rw [hchunk_shape] at hidx; simp [prodShape] at hidx; omega
    set p := idx / 32 with hpdef
    set j := idx % 32 with hjdef
    have hpb : p < 2 := by simp [hpdef]; omega
    have hjb : j < 32 := by simp [hjdef]; omega
    have hidx_eq : idx = p * 32 + j := by simp [hpdef, hjdef]; omega
    rw [hidx_eq]
    rw [chunk1_x_1_8_32_valAt _ r hag_shape hr p j hpb hjb]
    have hrp_lt : r * 2 + p < 8 := by
      have : r * 2 ≤ 3 * 2 := Nat.mul_le_mul_right 2 (by omega); omega
    rw [valAt_ag1_1_2_32_pj xs (r * 2 + p) j hhead hrp_lt hjb]
    have hd : (r * 2 + p) / 2 = r := by omega
    have hm : (r * 2 + p) % 2 = p := by omega
    rw [hd, hm]

private lemma chunk1_4_of_ag1_1_2_32_explicit (t0 t1 t2 t3 : Tensor) (r : Nat) (hr : r < 4)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) =
      ([t0, t1, t2, t3]).getD r (zeroTensor [1, 2, 32]) := by
  apply chunk1_4_of_ag1_1_2_32 _ r hr
  · simp [h0]
  · intro i hi
    match i, hi with
    | 0, _ => simpa [List.getD] using h0
    | 1, _ => simpa [List.getD] using h1
    | 2, _ => simpa [List.getD] using h2
    | 3, _ => simpa [List.getD] using h3

private lemma chunk1_4_of_ag1_1_2_32_idx0 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 0 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t0 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 0 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx1 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 1 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t1 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 1 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx2 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 2 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t2 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 2 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx3 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 3 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t3 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit t0 t1 t2 t3 3 (by omega) h0 h1 h2 h3]; rfl

/-! ### Bridging lemma: `fw_linear` distributes over dim-1 `allGatherPrimDimN`.

For `x : [1,8,32]` sharded along dim 1 into 4 pieces of shape `[1,2,32]`, and a
weight `w : [32,32]`, the linear application commutes with the gather:
  `fw_linear x w = allGatherPrimDimN 1 4 0 [fw_linear (chunk r x) w | r ∈ 0..3]`.

This is the key algebraic fact behind `prove_pattern_6` for goal_6. -/
private theorem fw_linear_split_dim1_4_1_8_32 (x w : Tensor)
    (hx : x.shape = [1, 8, 32]) (hw : w.shape = [32, 32]) :
    fw_linear x w = allGatherPrimDimN 1 4 0
      [fw_linear (chunkPrimDimN 1 4 0 x) w,
       fw_linear (chunkPrimDimN 1 4 1 x) w,
       fw_linear (chunkPrimDimN 1 4 2 x) w,
       fw_linear (chunkPrimDimN 1 4 3 x) w] := by
  have hchunk_shape : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := fun r _ =>
    chunk1_x_1_8_32_shape x r hx (by omega)
  have hpiece_shape : ∀ r, r < 4 →
      (fw_linear (chunkPrimDimN 1 4 r x) w).shape = [1, 2, 32] :=
    fun r hr => fw_linear_3d_shape 1 2 32 32 _ _ (hchunk_shape r hr) hw
  have h0sh := hpiece_shape 0 (by decide)
  have h1sh := hpiece_shape 1 (by decide)
  have h2sh := hpiece_shape 2 (by decide)
  have h3sh := hpiece_shape 3 (by decide)
  have hhead :
      ((([fw_linear (chunkPrimDimN 1 4 0 x) w,
           fw_linear (chunkPrimDimN 1 4 1 x) w,
           fw_linear (chunkPrimDimN 1 4 2 x) w,
           fw_linear (chunkPrimDimN 1 4 3 x) w] : List Tensor).head?).map
         (·.shape)).getD [] = [1, 2, 32] := by
    simp [List.head?, h0sh]
  have hLHS_shape : (fw_linear x w).shape = [1, 8, 32] :=
    fw_linear_3d_shape 1 8 32 32 x w hx hw
  have hRHS_shape :
      (allGatherPrimDimN 1 4 0
        [fw_linear (chunkPrimDimN 1 4 0 x) w,
         fw_linear (chunkPrimDimN 1 4 1 x) w,
         fw_linear (chunkPrimDimN 1 4 2 x) w,
         fw_linear (chunkPrimDimN 1 4 3 x) w]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro idx hidx
    rw [hLHS_shape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape] using hidx
    set p := idx / 32 with hp_def
    set j := idx % 32 with hj_def
    have hp_lt : p < 8 := by
      have : idx / 32 < 256 / 32 := Nat.div_lt_div_of_lt_of_dvd ⟨8, rfl⟩ hidx256
      simpa using this
    have hj_lt : j < 32 := by simp [hj_def]; omega
    have hidx_eq : idx = p * 32 + j := by
      simp [hp_def, hj_def]; omega
    rw [hidx_eq]
    -- LHS via fw_linear_valAt_b1_s_32
    rw [fw_linear_valAt_b1_s_32 8 (by omega) x w hx hw p hp_lt j hj_lt]
    -- RHS: gather over pieces
    rw [valAt_ag1_1_2_32_pj _ p j hhead hp_lt hj_lt]
    -- Decompose p = (p/2)*2 + (p%2)
    set r := p / 2 with hr_def
    set p' := p % 2 with hp'_def
    have hr_lt : r < 4 := by
      have : p / 2 < 8 / 2 := Nat.div_lt_div_of_lt_of_dvd ⟨4, rfl⟩ hp_lt
      simpa using this
    have hp'_lt : p' < 2 := by simp [hp'_def]; omega
    have hp_eq : p = r * 2 + p' := by simp [hr_def, hp'_def]; omega
    -- Pick the piece by case analysis on r
    have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    -- Show: piece getD (xs.getD r ...) = fw_linear (chunkPrimDimN 1 4 r x) w
    have hpiece_eq :
        ([fw_linear (chunkPrimDimN 1 4 0 x) w,
          fw_linear (chunkPrimDimN 1 4 1 x) w,
          fw_linear (chunkPrimDimN 1 4 2 x) w,
          fw_linear (chunkPrimDimN 1 4 3 x) w] : List Tensor).getD r
            (zeroTensor [1, 2, 32]) =
          fw_linear (chunkPrimDimN 1 4 r x) w := by
      rcases hr_cases with h | h | h | h
      all_goals (rw [h]; rfl)
    rw [hpiece_eq]
    -- Reduce piece's valAt via fw_linear_valAt_b1_s_32 (s=2)
    rw [fw_linear_valAt_b1_s_32 2 (by omega) (chunkPrimDimN 1 4 r x) w
        (hchunk_shape r hr_lt) hw p' hp'_lt j hj_lt]
    -- Convert chunk valAt back to original x
    apply Finset.sum_congr rfl
    intro k hk
    have hk_lt : k < 32 := by simpa using hk
    rw [chunk1_x_1_8_32_valAt x r hx hr_lt p' k hp'_lt hk_lt]
    rw [← hp_eq]

/-! ### Per-graph evaluation lemmas

These lemmas give a clean characterization of the relevant tensors in the
single-machine and parallel-machine graphs, by stripping non-writing suffixes
of the graph and reducing the cons step using `applyNode_fw_linear_out`. -/

private theorem sm_eval_572 (initSM : Store) :
    denoteGraph sm initSM 572 =
      fw_linear (denoteGraph sm initSM 918) (denoteGraph sm initSM 571) := by
  -- 572 is produced by node at index 6 in `sm.nodes`.
  have hsub : (denoteGraph sm initSM) 572 =
      (denoteGraph { sm with nodes := sm.nodes.take 7 } initSM) 572 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 572
      (sm.nodes.take 7) (sm.nodes.drop 7)
      (List.take_append_drop 7 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 7 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 6 ++
        [{ rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm
      { rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 6 } initSM)
      { rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] }) 572 = _
  rw [applyNode_fw_linear_out]
  have h918 : denoteGraph { sm with nodes := sm.nodes.take 6 } initSM 918 =
      denoteGraph sm initSM 918 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 918
      (sm.nodes.take 6) (sm.nodes.drop 6)
      (List.take_append_drop 6 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { sm with nodes := sm.nodes.take 6 } initSM 571 =
      denoteGraph sm initSM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 571
      (sm.nodes.take 6) (sm.nodes.drop 6)
      (List.take_append_drop 6 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h918, h571]

private theorem pm_eval_1177 (initPM : Store) :
    denoteGraph pm initPM 1177 =
      fw_linear (denoteGraph pm initPM 1173) (denoteGraph pm initPM 571) := by
  -- 1177 is produced by node at index 41 in `pm.nodes`.
  have hsub : (denoteGraph pm initPM) 1177 =
      (denoteGraph { pm with nodes := pm.nodes.take 42 } initPM) 1177 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1177
      (pm.nodes.take 42) (pm.nodes.drop 42)
      (List.take_append_drop 42 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 42 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 41 ++
        [{ rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 41 } initPM)
      { rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] }) 1177 = _
  rw [applyNode_fw_linear_out]
  have h1173 : denoteGraph { pm with nodes := pm.nodes.take 41 } initPM 1173 =
      denoteGraph pm initPM 1173 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1173
      (pm.nodes.take 41) (pm.nodes.drop 41)
      (List.take_append_drop 41 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 41 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 41) (pm.nodes.drop 41)
      (List.take_append_drop 41 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1173, h571]

private theorem pm_eval_1178 (initPM : Store) :
    denoteGraph pm initPM 1178 =
      fw_linear (denoteGraph pm initPM 1174) (denoteGraph pm initPM 571) := by
  have hsub : (denoteGraph pm initPM) 1178 =
      (denoteGraph { pm with nodes := pm.nodes.take 44 } initPM) 1178 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1178
      (pm.nodes.take 44) (pm.nodes.drop 44)
      (List.take_append_drop 44 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 44 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 43 ++
        [{ rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 43 } initPM)
      { rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] }) 1178 = _
  rw [applyNode_fw_linear_out]
  have h1174 : denoteGraph { pm with nodes := pm.nodes.take 43 } initPM 1174 =
      denoteGraph pm initPM 1174 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1174
      (pm.nodes.take 43) (pm.nodes.drop 43)
      (List.take_append_drop 43 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 43 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 43) (pm.nodes.drop 43)
      (List.take_append_drop 43 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1174, h571]

private theorem pm_eval_1179 (initPM : Store) :
    denoteGraph pm initPM 1179 =
      fw_linear (denoteGraph pm initPM 1175) (denoteGraph pm initPM 571) := by
  have hsub : (denoteGraph pm initPM) 1179 =
      (denoteGraph { pm with nodes := pm.nodes.take 46 } initPM) 1179 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1179
      (pm.nodes.take 46) (pm.nodes.drop 46)
      (List.take_append_drop 46 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 46 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 45 ++
        [{ rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 45 } initPM)
      { rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] }) 1179 = _
  rw [applyNode_fw_linear_out]
  have h1175 : denoteGraph { pm with nodes := pm.nodes.take 45 } initPM 1175 =
      denoteGraph pm initPM 1175 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1175
      (pm.nodes.take 45) (pm.nodes.drop 45)
      (List.take_append_drop 45 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 45 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 45) (pm.nodes.drop 45)
      (List.take_append_drop 45 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1175, h571]

private theorem pm_eval_1180 (initPM : Store) :
    denoteGraph pm initPM 1180 =
      fw_linear (denoteGraph pm initPM 1176) (denoteGraph pm initPM 571) := by
  -- 1180 is at idx 48 in pm.nodes.
  have hsub : (denoteGraph pm initPM) 1180 =
      (denoteGraph { pm with nodes := pm.nodes.take 49 } initPM) 1180 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1180
      (pm.nodes.take 49) (pm.nodes.drop 49)
      (List.take_append_drop 49 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 49 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 48 ++
        [{ rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 48 } initPM)
      { rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] }) 1180 = _
  rw [applyNode_fw_linear_out]
  have h1176 : denoteGraph { pm with nodes := pm.nodes.take 48 } initPM 1176 =
      denoteGraph pm initPM 1176 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1176
      (pm.nodes.take 48) (pm.nodes.drop 48)
      (List.take_append_drop 48 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 48 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 48) (pm.nodes.drop 48)
      (List.take_append_drop 48 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1176, h571]

/-! ### PM eval for tid 572 = AllGatherPrim of [1177..1180] dim 1.

Tid 572 is produced in PM by an AllGatherPrim node (at index 54 in `pm.nodes`,
i.e. `pm.nodes.take 55` ends with that node). -/

private theorem pm_eval_572 (initPM : Store) :
    denoteGraph pm initPM 572 = allGatherPrimDimN 1 4 0
      [denoteGraph pm initPM 1177, denoteGraph pm initPM 1178,
       denoteGraph pm initPM 1179, denoteGraph pm initPM 1180] := by
  have hsub : (denoteGraph pm initPM) 572 =
      (denoteGraph { pm with nodes := pm.nodes.take 55 } initPM) 572 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 572
      (pm.nodes.take 55) (pm.nodes.drop 55)
      (List.take_append_drop 55 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 55 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 54 ++
        [{ rank := 0, op := "OpName.AllGatherPrim",
           ins := (List.range 4).map (fun r => 1177 + r),
           outs := [572], params := [1] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 0, op := "OpName.AllGatherPrim",
        ins := (List.range 4).map (fun r => 1177 + r),
        outs := [572], params := [1] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 54 } initPM)
      { rank := 0, op := "OpName.AllGatherPrim",
        ins := (List.range 4).map (fun r => 1177 + r),
        outs := [572], params := [1] }) 572 = _
  rw [applyNode_allGatherPrimDimN_out]
  -- Suffix-equivalence for each input tid in 1177..1180
  have h1177 : denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1177 =
      denoteGraph pm initPM 1177 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1177
      (pm.nodes.take 54) (pm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h1178 : denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1178 =
      denoteGraph pm initPM 1178 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1178
      (pm.nodes.take 54) (pm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h1179 : denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1179 =
      denoteGraph pm initPM 1179 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1179
      (pm.nodes.take 54) (pm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h1180 : denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1180 =
      denoteGraph pm initPM 1180 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1180
      (pm.nodes.take 54) (pm.nodes.drop 54)
      (List.take_append_drop 54 _).symm
      (by set_option maxRecDepth 20000 in decide)
  -- Reduce ((List.range 4).map (1177+r)).map s = [s 1177, s 1178, s 1179, s 1180]
  show allGatherPrimDimN 1 pm.numRanks 0
        (((List.range 4).map (fun r => 1177 + r)).map
          (denoteGraph { pm with nodes := pm.nodes.take 54 } initPM)) = _
  have hlist :
      (((List.range 4).map (fun r => 1177 + r)).map
        (denoteGraph { pm with nodes := pm.nodes.take 54 } initPM)) =
      [denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1177,
       denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1178,
       denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1179,
       denoteGraph { pm with nodes := pm.nodes.take 54 } initPM 1180] := by
    show (((List.range 4).map (fun r => 1177 + r)).map _) = _
    rfl
  rw [hlist, h1177, h1178, h1179, h1180]
  rfl

/-! ### Goal_6 case

Combines `sm_eval_572`, `pm_eval_117{7,8,9}`, `pm_eval_1180`, `pm_eval_572`,
the bridging lemma `fw_linear_split_dim1_4_1_8_32`, and the prereq `goal_261`
(supplied via `prove_pattern_129`).

The other goals (7/32/58/83) follow the same structural pattern but require
their own SM/PM eval lemmas and their own prerequisite alpha-equivalence
patterns. They are left as `sorry` for now. -/

theorem prove_pattern_6 : pattern_6_stmt := by
  intro target h
  cases h with
  | goal_6 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    -- Get goal_261: SM 918 = AllGather of PM [1173..1176] dim 1
    have hL : goal_261_stmt :=
      prove_pattern_129 pattern_129_target.goal_261
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape_918, h_pm_shapes_918, h_eq_rec_918⟩ := hLtr
    have h_pm_shapes_918' :
        [(denoteGraph pm initPM 1173).shape, (denoteGraph pm initPM 1174).shape,
         (denoteGraph pm initPM 1175).shape, (denoteGraph pm initPM 1176).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      simpa [goal_261, List.map_cons, List.map_nil] using h_pm_shapes_918
    have h_pm_shapes_split :
        (denoteGraph pm initPM 1173).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1174).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1175).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1176).shape = [1, 2, 32] := by
      have hh := h_pm_shapes_918'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have h_x_sm_shape : (denoteGraph sm initSM 918).shape = [1, 8, 32] := by
      simpa [goal_261] using h_sm_shape_918
    have h_input_gather : denoteGraph sm initSM 918 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1173, denoteGraph pm initPM 1174,
         denoteGraph pm initPM 1175, denoteGraph pm initPM 1176] := by
      have hh := h_eq_rec_918
      simp only [goal_261, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      rw [h_pm_shapes_split.1]
      intro hbad; cases hbad
    -- Init equality of weight 571
    have h_init_W : InitGoalHolds pm.numRanks initGoal_571 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 571 = initPM 571 := by
      have hh := h_init_W.2.2
      simpa [initGoal_571, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 571 = initSM 571 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 571
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 571 = initPM 571 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 571 = denoteGraph pm initPM 571 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    -- Shape of W = [32, 32]
    have hW_init_shape : (initPM 571).shape = [32, 32] := by
      have hh := h_init_W.2.1
      simpa [initGoal_571, List.map_cons, List.map_nil] using hh
    have hW_sm_shape : (denoteGraph sm initSM 571).shape = [32, 32] := by
      rw [h_smW_init, hW_init_eq]; exact hW_init_shape
    -- Now compute SM 572
    have h_SM_572 := sm_eval_572 initSM
    -- Shape of SM 572
    have hSM572_shape : (denoteGraph sm initSM 572).shape = [1, 8, 32] := by
      rw [h_SM_572]
      exact fw_linear_3d_shape 1 8 32 32 _ _ h_x_sm_shape hW_sm_shape
    -- PM evals for 1177..1180
    have h_PM_1177 := pm_eval_1177 initPM
    have h_PM_1178 := pm_eval_1178 initPM
    have h_PM_1179 := pm_eval_1179 initPM
    have h_PM_1180 := pm_eval_1180 initPM
    have h_PM_572 := pm_eval_572 initPM
    -- Apply the bridging lemma to convert SM 572 to allGather of pieces
    have h_main : denoteGraph sm initSM 572 = denoteGraph pm initPM 572 := by
      rw [h_SM_572, h_input_gather, hW_sm_pm]
      -- Now goal: fw_linear (allGather PM[1173..]) PM571 = PM 572
      -- For the bridging lemma to apply we need allGather to have shape [1,8,32]
      -- and we need to phrase it so each piece is chunkPrimDimN.
      -- Actually our bridging lemma takes x : [1,8,32] and chunks. The result LHS
      -- is fw_linear x w, RHS is allGather of pieces of fw_linear chunk r x.
      -- We want fw_linear (allGather PM[1173..1176]) PM571 = allGather [PM1177..1180]
      -- Substitute via h_input_gather already done. Rewrite using bridging lemma:
      set X := allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1173, denoteGraph pm initPM 1174,
         denoteGraph pm initPM 1175, denoteGraph pm initPM 1176] with hXdef
      have hX_shape : X.shape = [1, 8, 32] := by
        rw [hXdef]
        rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32]
          (by simp [List.head?, h_pm_shapes_split.1])]
        rfl
      -- Apply bridging
      rw [fw_linear_split_dim1_4_1_8_32 X (denoteGraph pm initPM 571) hX_shape
        (by rw [h_pmW_init]; exact hW_init_shape)]
      -- Now LHS = allGather [fw_linear (chunk r X) W for r in 0..3]
      -- We need: chunk r X = PM (1173 + r). This is via chunk-of-allGather.
      have hI0_shape := h_pm_shapes_split.1
      have hI1_shape := h_pm_shapes_split.2.1
      have hI2_shape := h_pm_shapes_split.2.2.1
      have hI3_shape := h_pm_shapes_split.2.2.2
      have hchunk0 : chunkPrimDimN 1 4 0 X = denoteGraph pm initPM 1173 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk1 : chunkPrimDimN 1 4 1 X = denoteGraph pm initPM 1174 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk2 : chunkPrimDimN 1 4 2 X = denoteGraph pm initPM 1175 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk3 : chunkPrimDimN 1 4 3 X = denoteGraph pm initPM 1176 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      rw [hchunk0, hchunk1, hchunk2, hchunk3]
      rw [← h_PM_1177, ← h_PM_1178, ← h_PM_1179, ← h_PM_1180]
      rw [← h_PM_572]
    -- Conclude: goal_6_stmt
    show (denoteGraph sm initSM 572).shape = goal_6.tsShape ∧
      _ = goal_6.tpShapes ∧
      denoteGraph sm initSM 572 =
        reconstructWithDim goal_6.gatherDim pm.numRanks 0
          (goal_6.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · change (denoteGraph sm initSM 572).shape = [1, 8, 32]
      exact hSM572_shape
    · have hPM572_shape : (denoteGraph pm initPM 572).shape = [1, 8, 32] := by
        rw [← h_main]; exact hSM572_shape
      change [(denoteGraph pm initPM 572).shape] = [[1, 8, 32]]
      rw [hPM572_shape]
    · change denoteGraph sm initSM 572 =
        reconstructWithDim 1 pm.numRanks 0 [denoteGraph pm initPM 572]
      rw [reconstructWithDim_singleton]
      exact h_main
  | goal_7 => sorry
  | goal_32 => sorry
  | goal_58 => sorry
  | goal_83 => sorry

end TrainVerify.Denote.GeneratedPatterns
