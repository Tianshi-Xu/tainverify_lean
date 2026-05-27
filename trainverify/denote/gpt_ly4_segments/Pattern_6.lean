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

/-! ### Per-graph evaluation lemmas (helper-step style; see helpers above). -/

/-! ## Generic helpers for unfolding `denoteGraph` at FW_linear / AllGatherPrim nodes.

These are written à la `denote_bw_layernorm_dx_step` in Pattern_125: by taking
the relevant `NodeDecl` as a `@[reducible]` private def and pushing the
expensive `whnf` of `g.nodes.take K` out of the caller, we keep each per-tid
eval to a single `apply ... (by decide) ...` line.  Without this packaging
the per-eval `whnf` cost grows superlinearly with K and times out at
`maxHeartbeats 4000000` for the K = 205/414/602 nodes used in this pattern. -/

private theorem denote_fw_linear_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (xTid wTid outTid : Tid) (rk : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.FW_linear",
                      ins := [xTid, wTid], outs := [outTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), outTid ∉ n.outs)
    (hsuf_x : ∀ n ∈ g.nodes.drop K, xTid ∉ n.outs)
    (hsuf_w : ∀ n ∈ g.nodes.drop K, wTid ∉ n.outs) :
    denoteGraph g initStore outTid =
      fw_linear (denoteGraph g initStore xTid) (denoteGraph g initStore wTid) := by
  have hh1 : denoteGraph g initStore outTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore outTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore outTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_out
  rw [hh1]
  have htake : g.nodes.take (K+1) = g.nodes.take K ++ [node] := by
    rw [list_take_succ_eq_take_append_get g.nodes K hKlt, hidx]
  have hg_eq : ({ g with nodes := g.nodes.take (K+1) } : GraphDecl) =
      { g with nodes := g.nodes.take K ++ [node] } := by
    cases g; congr 1
  rw [hg_eq, denoteGraph_nodes_append]
  have hsing : ({ g with nodes := [node] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := node :: [] } := by cases g; rfl
  rw [hsing, denoteGraph_cons_eq g node []]
  change applyNode g (denoteGraph { g with nodes := g.nodes.take K } initStore) node outTid = _
  rw [hnode]
  rw [applyNode_fw_linear_out]
  have hx : (denoteGraph { g with nodes := g.nodes.take K } initStore) xTid =
      denoteGraph g initStore xTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore xTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_x).symm
  have hw : (denoteGraph { g with nodes := g.nodes.take K } initStore) wTid =
      denoteGraph g initStore wTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore wTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_w).symm
  rw [hx, hw]

private theorem denote_allGather4_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (t0 outTid : Tid) (rk dim : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.AllGatherPrim",
                      ins := (List.range 4).map (fun r => t0 + r),
                      outs := [outTid], params := [dim] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), outTid ∉ n.outs)
    (hsuf_0 : ∀ n ∈ g.nodes.drop K, t0 ∉ n.outs)
    (hsuf_1 : ∀ n ∈ g.nodes.drop K, (t0 + 1) ∉ n.outs)
    (hsuf_2 : ∀ n ∈ g.nodes.drop K, (t0 + 2) ∉ n.outs)
    (hsuf_3 : ∀ n ∈ g.nodes.drop K, (t0 + 3) ∉ n.outs) :
    denoteGraph g initStore outTid =
      allGatherPrimDimN dim g.numRanks rk
        [denoteGraph g initStore t0,
         denoteGraph g initStore (t0 + 1),
         denoteGraph g initStore (t0 + 2),
         denoteGraph g initStore (t0 + 3)] := by
  have hh1 : denoteGraph g initStore outTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore outTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore outTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_out
  rw [hh1]
  have htake : g.nodes.take (K+1) = g.nodes.take K ++ [node] := by
    rw [list_take_succ_eq_take_append_get g.nodes K hKlt, hidx]
  have hg_eq : ({ g with nodes := g.nodes.take (K+1) } : GraphDecl) =
      { g with nodes := g.nodes.take K ++ [node] } := by
    cases g; congr 1
  rw [hg_eq, denoteGraph_nodes_append]
  have hsing : ({ g with nodes := [node] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := node :: [] } := by cases g; rfl
  rw [hsing, denoteGraph_cons_eq g node []]
  change applyNode g (denoteGraph { g with nodes := g.nodes.take K } initStore) node outTid = _
  rw [hnode]
  rw [applyNode_allGatherPrimDimN_out]
  have h0 : (denoteGraph { g with nodes := g.nodes.take K } initStore) t0 =
      denoteGraph g initStore t0 :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore t0
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_0).symm
  have h1 : (denoteGraph { g with nodes := g.nodes.take K } initStore) (t0 + 1) =
      denoteGraph g initStore (t0 + 1) :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore (t0 + 1)
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_1).symm
  have h2 : (denoteGraph { g with nodes := g.nodes.take K } initStore) (t0 + 2) =
      denoteGraph g initStore (t0 + 2) :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore (t0 + 2)
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_2).symm
  have h3 : (denoteGraph { g with nodes := g.nodes.take K } initStore) (t0 + 3) =
      denoteGraph g initStore (t0 + 3) :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore (t0 + 3)
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_3).symm
  have hlist :
      (((List.range 4).map (fun r => t0 + r)).map
        (denoteGraph { g with nodes := g.nodes.take K } initStore)) =
      [denoteGraph { g with nodes := g.nodes.take K } initStore t0,
       denoteGraph { g with nodes := g.nodes.take K } initStore (t0 + 1),
       denoteGraph { g with nodes := g.nodes.take K } initStore (t0 + 2),
       denoteGraph { g with nodes := g.nodes.take K } initStore (t0 + 3)] := by
    simp [List.range, List.range.loop, List.map]
  rw [hlist, h0, h1, h2, h3]

/-! ## Reducible NodeDecl handles for each FW_linear / AllGatherPrim node we need. -/

@[reducible] private def smN_572 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] }
@[reducible] private def pmN_1177 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] }
@[reducible] private def pmN_1178 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] }
@[reducible] private def pmN_1179 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] }
@[reducible] private def pmN_1180 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] }
@[reducible] private def pmN_AG_572 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := (List.range 4).map (fun r => 1177 + r),
    outs := [572], params := [1] }
@[reducible] private def smN_574 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [922, 573], outs := [574] }
@[reducible] private def pmN_1205 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1201, 573], outs := [1205] }
@[reducible] private def pmN_1206 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [1202, 573], outs := [1206] }
@[reducible] private def pmN_1207 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [1203, 573], outs := [1207] }
@[reducible] private def pmN_1208 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [1204, 573], outs := [1208] }
@[reducible] private def pmN_AG_574 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := (List.range 4).map (fun r => 1205 + r),
    outs := [574], params := [1] }
@[reducible] private def smN_609 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [965, 608], outs := [609] }
@[reducible] private def pmN_1725 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1721, 608], outs := [1725] }
@[reducible] private def pmN_1726 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [1722, 608], outs := [1726] }
@[reducible] private def pmN_1727 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [1723, 608], outs := [1727] }
@[reducible] private def pmN_1728 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [1724, 608], outs := [1728] }
@[reducible] private def pmN_AG_609 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := (List.range 4).map (fun r => 1725 + r),
    outs := [609], params := [1] }
@[reducible] private def smN_646 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1012, 645], outs := [646] }
@[reducible] private def pmN_2317 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [2313, 645], outs := [2317] }
@[reducible] private def pmN_2318 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [2314, 645], outs := [2318] }
@[reducible] private def pmN_2319 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [2315, 645], outs := [2319] }
@[reducible] private def pmN_2320 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [2316, 645], outs := [2320] }
@[reducible] private def pmN_AG_646 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := (List.range 4).map (fun r => 2317 + r),
    outs := [646], params := [1] }
@[reducible] private def smN_681 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [1055, 680], outs := [681] }
@[reducible] private def pmN_2873 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [2869, 680], outs := [2873] }
@[reducible] private def pmN_2874 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [2870, 680], outs := [2874] }
@[reducible] private def pmN_2875 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [2871, 680], outs := [2875] }
@[reducible] private def pmN_2876 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [2872, 680], outs := [2876] }
@[reducible] private def pmN_AG_681 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim",
    ins := (List.range 4).map (fun r => 2873 + r),
    outs := [681], params := [1] }

private theorem sm_eval_572 (initSM : Store) :
    denoteGraph sm initSM 572 =
      fw_linear (denoteGraph sm initSM 918) (denoteGraph sm initSM 571) :=
  denote_fw_linear_step sm initSM 6 918 571 572 0 smN_572 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1177 (initPM : Store) :
    denoteGraph pm initPM 1177 =
      fw_linear (denoteGraph pm initPM 1173) (denoteGraph pm initPM 571) :=
  denote_fw_linear_step pm initPM 41 1173 571 1177 0 pmN_1177 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1178 (initPM : Store) :
    denoteGraph pm initPM 1178 =
      fw_linear (denoteGraph pm initPM 1174) (denoteGraph pm initPM 571) :=
  denote_fw_linear_step pm initPM 43 1174 571 1178 1 pmN_1178 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1179 (initPM : Store) :
    denoteGraph pm initPM 1179 =
      fw_linear (denoteGraph pm initPM 1175) (denoteGraph pm initPM 571) :=
  denote_fw_linear_step pm initPM 45 1175 571 1179 2 pmN_1179 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1180 (initPM : Store) :
    denoteGraph pm initPM 1180 =
      fw_linear (denoteGraph pm initPM 1176) (denoteGraph pm initPM 571) :=
  denote_fw_linear_step pm initPM 48 1176 571 1180 3 pmN_1180 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_572 (initPM : Store) :
    denoteGraph pm initPM 572 = allGatherPrimDimN 1 4 0
      [denoteGraph pm initPM 1177, denoteGraph pm initPM 1178,
       denoteGraph pm initPM 1179, denoteGraph pm initPM 1180] := by
  have h := denote_allGather4_step pm initPM 54 1177 572 0 1 pmN_AG_572 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- helper produces RHS with (t0 + k); g.numRanks reduces to 4
  simpa using h

private theorem sm_eval_574 (initSM : Store) :
    denoteGraph sm initSM 574 =
      fw_linear (denoteGraph sm initSM 922) (denoteGraph sm initSM 573) :=
  denote_fw_linear_step sm initSM 7 922 573 574 0 smN_574 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1205 (initPM : Store) :
    denoteGraph pm initPM 1205 =
      fw_linear (denoteGraph pm initPM 1201) (denoteGraph pm initPM 573) :=
  denote_fw_linear_step pm initPM 42 1201 573 1205 0 pmN_1205 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1206 (initPM : Store) :
    denoteGraph pm initPM 1206 =
      fw_linear (denoteGraph pm initPM 1202) (denoteGraph pm initPM 573) :=
  denote_fw_linear_step pm initPM 44 1202 573 1206 1 pmN_1206 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1207 (initPM : Store) :
    denoteGraph pm initPM 1207 =
      fw_linear (denoteGraph pm initPM 1203) (denoteGraph pm initPM 573) :=
  denote_fw_linear_step pm initPM 46 1203 573 1207 2 pmN_1207 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1208 (initPM : Store) :
    denoteGraph pm initPM 1208 =
      fw_linear (denoteGraph pm initPM 1204) (denoteGraph pm initPM 573) :=
  denote_fw_linear_step pm initPM 49 1204 573 1208 3 pmN_1208 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_574 (initPM : Store) :
    denoteGraph pm initPM 574 = allGatherPrimDimN 1 4 0
      [denoteGraph pm initPM 1205, denoteGraph pm initPM 1206,
       denoteGraph pm initPM 1207, denoteGraph pm initPM 1208] := by
  have h := denote_allGather4_step pm initPM 55 1205 574 0 1 pmN_AG_574 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- helper produces RHS with (t0 + k); g.numRanks reduces to 4
  simpa using h

private theorem sm_eval_609 (initSM : Store) :
    denoteGraph sm initSM 609 =
      fw_linear (denoteGraph sm initSM 965) (denoteGraph sm initSM 608) :=
  denote_fw_linear_step sm initSM 35 965 608 609 0 smN_609 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1725 (initPM : Store) :
    denoteGraph pm initPM 1725 =
      fw_linear (denoteGraph pm initPM 1721) (denoteGraph pm initPM 608) :=
  denote_fw_linear_step pm initPM 205 1721 608 1725 0 pmN_1725 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1726 (initPM : Store) :
    denoteGraph pm initPM 1726 =
      fw_linear (denoteGraph pm initPM 1722) (denoteGraph pm initPM 608) :=
  denote_fw_linear_step pm initPM 206 1722 608 1726 1 pmN_1726 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1727 (initPM : Store) :
    denoteGraph pm initPM 1727 =
      fw_linear (denoteGraph pm initPM 1723) (denoteGraph pm initPM 608) :=
  denote_fw_linear_step pm initPM 207 1723 608 1727 2 pmN_1727 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1728 (initPM : Store) :
    denoteGraph pm initPM 1728 =
      fw_linear (denoteGraph pm initPM 1724) (denoteGraph pm initPM 608) :=
  denote_fw_linear_step pm initPM 215 1724 608 1728 3 pmN_1728 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_609 (initPM : Store) :
    denoteGraph pm initPM 609 = allGatherPrimDimN 1 4 0
      [denoteGraph pm initPM 1725, denoteGraph pm initPM 1726,
       denoteGraph pm initPM 1727, denoteGraph pm initPM 1728] := by
  have h := denote_allGather4_step pm initPM 224 1725 609 0 1 pmN_AG_609 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- helper produces RHS with (t0 + k); g.numRanks reduces to 4
  simpa using h

private theorem sm_eval_646 (initSM : Store) :
    denoteGraph sm initSM 646 =
      fw_linear (denoteGraph sm initSM 1012) (denoteGraph sm initSM 645) :=
  denote_fw_linear_step sm initSM 64 1012 645 646 0 smN_646 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2317 (initPM : Store) :
    denoteGraph pm initPM 2317 =
      fw_linear (denoteGraph pm initPM 2313) (denoteGraph pm initPM 645) :=
  denote_fw_linear_step pm initPM 400 2313 645 2317 0 pmN_2317 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2318 (initPM : Store) :
    denoteGraph pm initPM 2318 =
      fw_linear (denoteGraph pm initPM 2314) (denoteGraph pm initPM 645) :=
  denote_fw_linear_step pm initPM 401 2314 645 2318 1 pmN_2318 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2319 (initPM : Store) :
    denoteGraph pm initPM 2319 =
      fw_linear (denoteGraph pm initPM 2315) (denoteGraph pm initPM 645) :=
  denote_fw_linear_step pm initPM 402 2315 645 2319 2 pmN_2319 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2320 (initPM : Store) :
    denoteGraph pm initPM 2320 =
      fw_linear (denoteGraph pm initPM 2316) (denoteGraph pm initPM 645) :=
  denote_fw_linear_step pm initPM 405 2316 645 2320 3 pmN_2320 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_646 (initPM : Store) :
    denoteGraph pm initPM 646 = allGatherPrimDimN 1 4 0
      [denoteGraph pm initPM 2317, denoteGraph pm initPM 2318,
       denoteGraph pm initPM 2319, denoteGraph pm initPM 2320] := by
  have h := denote_allGather4_step pm initPM 414 2317 646 0 1 pmN_AG_646 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- helper produces RHS with (t0 + k); g.numRanks reduces to 4
  simpa using h

private theorem sm_eval_681 (initSM : Store) :
    denoteGraph sm initSM 681 =
      fw_linear (denoteGraph sm initSM 1055) (denoteGraph sm initSM 680) :=
  denote_fw_linear_step sm initSM 92 1055 680 681 0 smN_681 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2873 (initPM : Store) :
    denoteGraph pm initPM 2873 =
      fw_linear (denoteGraph pm initPM 2869) (denoteGraph pm initPM 680) :=
  denote_fw_linear_step pm initPM 582 2869 680 2873 0 pmN_2873 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2874 (initPM : Store) :
    denoteGraph pm initPM 2874 =
      fw_linear (denoteGraph pm initPM 2870) (denoteGraph pm initPM 680) :=
  denote_fw_linear_step pm initPM 583 2870 680 2874 1 pmN_2874 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2875 (initPM : Store) :
    denoteGraph pm initPM 2875 =
      fw_linear (denoteGraph pm initPM 2871) (denoteGraph pm initPM 680) :=
  denote_fw_linear_step pm initPM 584 2871 680 2875 2 pmN_2875 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2876 (initPM : Store) :
    denoteGraph pm initPM 2876 =
      fw_linear (denoteGraph pm initPM 2872) (denoteGraph pm initPM 680) :=
  denote_fw_linear_step pm initPM 593 2872 680 2876 3 pmN_2876 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_681 (initPM : Store) :
    denoteGraph pm initPM 681 = allGatherPrimDimN 1 4 0
      [denoteGraph pm initPM 2873, denoteGraph pm initPM 2874,
       denoteGraph pm initPM 2875, denoteGraph pm initPM 2876] := by
  have h := denote_allGather4_step pm initPM 602 2873 681 0 1 pmN_AG_681 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- helper produces RHS with (t0 + k); g.numRanks reduces to 4
  simpa using h


/-! ## Main theorem. -/

theorem prove_pattern_6 : pattern_6_stmt := by
  intro target h
  cases h with
  | goal_6 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
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
    have hW_init_shape : (initPM 571).shape = [32, 32] := by
      have hh := h_init_W.2.1
      simpa [initGoal_571, List.map_cons, List.map_nil] using hh
    have hW_sm_shape : (denoteGraph sm initSM 571).shape = [32, 32] := by
      rw [h_smW_init, hW_init_eq]; exact hW_init_shape
    have h_SM_572 := sm_eval_572 initSM
    have hSM572_shape : (denoteGraph sm initSM 572).shape = [1, 8, 32] := by
      rw [h_SM_572]
      exact fw_linear_3d_shape 1 8 32 32 _ _ h_x_sm_shape hW_sm_shape
    have h_PM_1177 := pm_eval_1177 initPM
    have h_PM_1178 := pm_eval_1178 initPM
    have h_PM_1179 := pm_eval_1179 initPM
    have h_PM_1180 := pm_eval_1180 initPM
    have h_PM_572 := pm_eval_572 initPM
    have h_main : denoteGraph sm initSM 572 = denoteGraph pm initPM 572 := by
      rw [h_SM_572, h_input_gather, hW_sm_pm]
      set X := allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1173, denoteGraph pm initPM 1174,
         denoteGraph pm initPM 1175, denoteGraph pm initPM 1176] with hXdef
      have hX_shape : X.shape = [1, 8, 32] := by
        rw [hXdef]
        rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32]
          (by simp [List.head?, h_pm_shapes_split.1])]
        rfl
      rw [fw_linear_split_dim1_4_1_8_32 X (denoteGraph pm initPM 571) hX_shape
        (by rw [h_pmW_init]; exact hW_init_shape)]
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

  | goal_7 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_263_stmt :=
      prove_pattern_129 pattern_129_target.goal_263
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape_922, h_pm_shapes_922, h_eq_rec_922⟩ := hLtr
    have h_pm_shapes_922' :
        [(denoteGraph pm initPM 1201).shape, (denoteGraph pm initPM 1202).shape,
         (denoteGraph pm initPM 1203).shape, (denoteGraph pm initPM 1204).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      simpa [goal_263, List.map_cons, List.map_nil] using h_pm_shapes_922
    have h_pm_shapes_split :
        (denoteGraph pm initPM 1201).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1202).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1203).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1204).shape = [1, 2, 32] := by
      have hh := h_pm_shapes_922'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have h_x_sm_shape : (denoteGraph sm initSM 922).shape = [1, 8, 32] := by
      simpa [goal_263] using h_sm_shape_922
    have h_input_gather : denoteGraph sm initSM 922 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1201, denoteGraph pm initPM 1202,
         denoteGraph pm initPM 1203, denoteGraph pm initPM 1204] := by
      have hh := h_eq_rec_922
      simp only [goal_263, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      rw [h_pm_shapes_split.1]
      intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_573 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 573 = initPM 573 := by
      have hh := h_init_W.2.2
      simpa [initGoal_573, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 573 = initSM 573 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 573
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 573 = initPM 573 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 573
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 573 = denoteGraph pm initPM 573 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hW_init_shape : (initPM 573).shape = [32, 32] := by
      have hh := h_init_W.2.1
      simpa [initGoal_573, List.map_cons, List.map_nil] using hh
    have hW_sm_shape : (denoteGraph sm initSM 573).shape = [32, 32] := by
      rw [h_smW_init, hW_init_eq]; exact hW_init_shape
    have h_SM_574 := sm_eval_574 initSM
    have hSM574_shape : (denoteGraph sm initSM 574).shape = [1, 8, 32] := by
      rw [h_SM_574]
      exact fw_linear_3d_shape 1 8 32 32 _ _ h_x_sm_shape hW_sm_shape
    have h_PM_1205 := pm_eval_1205 initPM
    have h_PM_1206 := pm_eval_1206 initPM
    have h_PM_1207 := pm_eval_1207 initPM
    have h_PM_1208 := pm_eval_1208 initPM
    have h_PM_574 := pm_eval_574 initPM
    have h_main : denoteGraph sm initSM 574 = denoteGraph pm initPM 574 := by
      rw [h_SM_574, h_input_gather, hW_sm_pm]
      set X := allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1201, denoteGraph pm initPM 1202,
         denoteGraph pm initPM 1203, denoteGraph pm initPM 1204] with hXdef
      have hX_shape : X.shape = [1, 8, 32] := by
        rw [hXdef]
        rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32]
          (by simp [List.head?, h_pm_shapes_split.1])]
        rfl
      rw [fw_linear_split_dim1_4_1_8_32 X (denoteGraph pm initPM 573) hX_shape
        (by rw [h_pmW_init]; exact hW_init_shape)]
      have hI0_shape := h_pm_shapes_split.1
      have hI1_shape := h_pm_shapes_split.2.1
      have hI2_shape := h_pm_shapes_split.2.2.1
      have hI3_shape := h_pm_shapes_split.2.2.2
      have hchunk0 : chunkPrimDimN 1 4 0 X = denoteGraph pm initPM 1201 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk1 : chunkPrimDimN 1 4 1 X = denoteGraph pm initPM 1202 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk2 : chunkPrimDimN 1 4 2 X = denoteGraph pm initPM 1203 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk3 : chunkPrimDimN 1 4 3 X = denoteGraph pm initPM 1204 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      rw [hchunk0, hchunk1, hchunk2, hchunk3]
      rw [← h_PM_1205, ← h_PM_1206, ← h_PM_1207, ← h_PM_1208]
      rw [← h_PM_574]
    show (denoteGraph sm initSM 574).shape = goal_7.tsShape ∧
      _ = goal_7.tpShapes ∧
      denoteGraph sm initSM 574 =
        reconstructWithDim goal_7.gatherDim pm.numRanks 0
          (goal_7.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · change (denoteGraph sm initSM 574).shape = [1, 8, 32]
      exact hSM574_shape
    · have hPM574_shape : (denoteGraph pm initPM 574).shape = [1, 8, 32] := by
        rw [← h_main]; exact hSM574_shape
      change [(denoteGraph pm initPM 574).shape] = [[1, 8, 32]]
      rw [hPM574_shape]
    · change denoteGraph sm initSM 574 =
        reconstructWithDim 1 pm.numRanks 0 [denoteGraph pm initPM 574]
      rw [reconstructWithDim_singleton]
      exact h_main

  | goal_32 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_277_stmt :=
      prove_pattern_129 pattern_129_target.goal_277
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape_965, h_pm_shapes_965, h_eq_rec_965⟩ := hLtr
    have h_pm_shapes_965' :
        [(denoteGraph pm initPM 1721).shape, (denoteGraph pm initPM 1722).shape,
         (denoteGraph pm initPM 1723).shape, (denoteGraph pm initPM 1724).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      simpa [goal_277, List.map_cons, List.map_nil] using h_pm_shapes_965
    have h_pm_shapes_split :
        (denoteGraph pm initPM 1721).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1722).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1723).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 1724).shape = [1, 2, 32] := by
      have hh := h_pm_shapes_965'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have h_x_sm_shape : (denoteGraph sm initSM 965).shape = [1, 8, 32] := by
      simpa [goal_277] using h_sm_shape_965
    have h_input_gather : denoteGraph sm initSM 965 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1721, denoteGraph pm initPM 1722,
         denoteGraph pm initPM 1723, denoteGraph pm initPM 1724] := by
      have hh := h_eq_rec_965
      simp only [goal_277, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      rw [h_pm_shapes_split.1]
      intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_608 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 608 = initPM 608 := by
      have hh := h_init_W.2.2
      simpa [initGoal_608, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 608 = initSM 608 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 608
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 608 = initPM 608 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 608
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 608 = denoteGraph pm initPM 608 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hW_init_shape : (initPM 608).shape = [32, 32] := by
      have hh := h_init_W.2.1
      simpa [initGoal_608, List.map_cons, List.map_nil] using hh
    have hW_sm_shape : (denoteGraph sm initSM 608).shape = [32, 32] := by
      rw [h_smW_init, hW_init_eq]; exact hW_init_shape
    have h_SM_609 := sm_eval_609 initSM
    have hSM609_shape : (denoteGraph sm initSM 609).shape = [1, 8, 32] := by
      rw [h_SM_609]
      exact fw_linear_3d_shape 1 8 32 32 _ _ h_x_sm_shape hW_sm_shape
    have h_PM_1725 := pm_eval_1725 initPM
    have h_PM_1726 := pm_eval_1726 initPM
    have h_PM_1727 := pm_eval_1727 initPM
    have h_PM_1728 := pm_eval_1728 initPM
    have h_PM_609 := pm_eval_609 initPM
    have h_main : denoteGraph sm initSM 609 = denoteGraph pm initPM 609 := by
      rw [h_SM_609, h_input_gather, hW_sm_pm]
      set X := allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 1721, denoteGraph pm initPM 1722,
         denoteGraph pm initPM 1723, denoteGraph pm initPM 1724] with hXdef
      have hX_shape : X.shape = [1, 8, 32] := by
        rw [hXdef]
        rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32]
          (by simp [List.head?, h_pm_shapes_split.1])]
        rfl
      rw [fw_linear_split_dim1_4_1_8_32 X (denoteGraph pm initPM 608) hX_shape
        (by rw [h_pmW_init]; exact hW_init_shape)]
      have hI0_shape := h_pm_shapes_split.1
      have hI1_shape := h_pm_shapes_split.2.1
      have hI2_shape := h_pm_shapes_split.2.2.1
      have hI3_shape := h_pm_shapes_split.2.2.2
      have hchunk0 : chunkPrimDimN 1 4 0 X = denoteGraph pm initPM 1721 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk1 : chunkPrimDimN 1 4 1 X = denoteGraph pm initPM 1722 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk2 : chunkPrimDimN 1 4 2 X = denoteGraph pm initPM 1723 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk3 : chunkPrimDimN 1 4 3 X = denoteGraph pm initPM 1724 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      rw [hchunk0, hchunk1, hchunk2, hchunk3]
      rw [← h_PM_1725, ← h_PM_1726, ← h_PM_1727, ← h_PM_1728]
      rw [← h_PM_609]
    show (denoteGraph sm initSM 609).shape = goal_32.tsShape ∧
      _ = goal_32.tpShapes ∧
      denoteGraph sm initSM 609 =
        reconstructWithDim goal_32.gatherDim pm.numRanks 0
          (goal_32.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · change (denoteGraph sm initSM 609).shape = [1, 8, 32]
      exact hSM609_shape
    · have hPM609_shape : (denoteGraph pm initPM 609).shape = [1, 8, 32] := by
        rw [← h_main]; exact hSM609_shape
      change [(denoteGraph pm initPM 609).shape] = [[1, 8, 32]]
      rw [hPM609_shape]
    · change denoteGraph sm initSM 609 =
        reconstructWithDim 1 pm.numRanks 0 [denoteGraph pm initPM 609]
      rw [reconstructWithDim_singleton]
      exact h_main

  | goal_58 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_293_stmt :=
      prove_pattern_129 pattern_129_target.goal_293
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape_1012, h_pm_shapes_1012, h_eq_rec_1012⟩ := hLtr
    have h_pm_shapes_1012' :
        [(denoteGraph pm initPM 2313).shape, (denoteGraph pm initPM 2314).shape,
         (denoteGraph pm initPM 2315).shape, (denoteGraph pm initPM 2316).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      simpa [goal_293, List.map_cons, List.map_nil] using h_pm_shapes_1012
    have h_pm_shapes_split :
        (denoteGraph pm initPM 2313).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2314).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2315).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2316).shape = [1, 2, 32] := by
      have hh := h_pm_shapes_1012'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have h_x_sm_shape : (denoteGraph sm initSM 1012).shape = [1, 8, 32] := by
      simpa [goal_293] using h_sm_shape_1012
    have h_input_gather : denoteGraph sm initSM 1012 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2313, denoteGraph pm initPM 2314,
         denoteGraph pm initPM 2315, denoteGraph pm initPM 2316] := by
      have hh := h_eq_rec_1012
      simp only [goal_293, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      rw [h_pm_shapes_split.1]
      intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_645 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 645 = initPM 645 := by
      have hh := h_init_W.2.2
      simpa [initGoal_645, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 645 = initSM 645 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 645
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 645 = initPM 645 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 645
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 645 = denoteGraph pm initPM 645 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hW_init_shape : (initPM 645).shape = [32, 32] := by
      have hh := h_init_W.2.1
      simpa [initGoal_645, List.map_cons, List.map_nil] using hh
    have hW_sm_shape : (denoteGraph sm initSM 645).shape = [32, 32] := by
      rw [h_smW_init, hW_init_eq]; exact hW_init_shape
    have h_SM_646 := sm_eval_646 initSM
    have hSM646_shape : (denoteGraph sm initSM 646).shape = [1, 8, 32] := by
      rw [h_SM_646]
      exact fw_linear_3d_shape 1 8 32 32 _ _ h_x_sm_shape hW_sm_shape
    have h_PM_2317 := pm_eval_2317 initPM
    have h_PM_2318 := pm_eval_2318 initPM
    have h_PM_2319 := pm_eval_2319 initPM
    have h_PM_2320 := pm_eval_2320 initPM
    have h_PM_646 := pm_eval_646 initPM
    have h_main : denoteGraph sm initSM 646 = denoteGraph pm initPM 646 := by
      rw [h_SM_646, h_input_gather, hW_sm_pm]
      set X := allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2313, denoteGraph pm initPM 2314,
         denoteGraph pm initPM 2315, denoteGraph pm initPM 2316] with hXdef
      have hX_shape : X.shape = [1, 8, 32] := by
        rw [hXdef]
        rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32]
          (by simp [List.head?, h_pm_shapes_split.1])]
        rfl
      rw [fw_linear_split_dim1_4_1_8_32 X (denoteGraph pm initPM 645) hX_shape
        (by rw [h_pmW_init]; exact hW_init_shape)]
      have hI0_shape := h_pm_shapes_split.1
      have hI1_shape := h_pm_shapes_split.2.1
      have hI2_shape := h_pm_shapes_split.2.2.1
      have hI3_shape := h_pm_shapes_split.2.2.2
      have hchunk0 : chunkPrimDimN 1 4 0 X = denoteGraph pm initPM 2313 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk1 : chunkPrimDimN 1 4 1 X = denoteGraph pm initPM 2314 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk2 : chunkPrimDimN 1 4 2 X = denoteGraph pm initPM 2315 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk3 : chunkPrimDimN 1 4 3 X = denoteGraph pm initPM 2316 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      rw [hchunk0, hchunk1, hchunk2, hchunk3]
      rw [← h_PM_2317, ← h_PM_2318, ← h_PM_2319, ← h_PM_2320]
      rw [← h_PM_646]
    show (denoteGraph sm initSM 646).shape = goal_58.tsShape ∧
      _ = goal_58.tpShapes ∧
      denoteGraph sm initSM 646 =
        reconstructWithDim goal_58.gatherDim pm.numRanks 0
          (goal_58.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · change (denoteGraph sm initSM 646).shape = [1, 8, 32]
      exact hSM646_shape
    · have hPM646_shape : (denoteGraph pm initPM 646).shape = [1, 8, 32] := by
        rw [← h_main]; exact hSM646_shape
      change [(denoteGraph pm initPM 646).shape] = [[1, 8, 32]]
      rw [hPM646_shape]
    · change denoteGraph sm initSM 646 =
        reconstructWithDim 1 pm.numRanks 0 [denoteGraph pm initPM 646]
      rw [reconstructWithDim_singleton]
      exact h_main

  | goal_83 =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hL : goal_307_stmt :=
      prove_pattern_129 pattern_129_target.goal_307
    have hLtr := hL initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨h_sm_shape_1055, h_pm_shapes_1055, h_eq_rec_1055⟩ := hLtr
    have h_pm_shapes_1055' :
        [(denoteGraph pm initPM 2869).shape, (denoteGraph pm initPM 2870).shape,
         (denoteGraph pm initPM 2871).shape, (denoteGraph pm initPM 2872).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      simpa [goal_307, List.map_cons, List.map_nil] using h_pm_shapes_1055
    have h_pm_shapes_split :
        (denoteGraph pm initPM 2869).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2870).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2871).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM 2872).shape = [1, 2, 32] := by
      have hh := h_pm_shapes_1055'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have h_x_sm_shape : (denoteGraph sm initSM 1055).shape = [1, 8, 32] := by
      simpa [goal_307] using h_sm_shape_1055
    have h_input_gather : denoteGraph sm initSM 1055 = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2869, denoteGraph pm initPM 2870,
         denoteGraph pm initPM 2871, denoteGraph pm initPM 2872] := by
      have hh := h_eq_rec_1055
      simp only [goal_307, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      rw [h_pm_shapes_split.1]
      intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_680 initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM 680 = initPM 680 := by
      have hh := h_init_W.2.2
      simpa [initGoal_680, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM 680 = initSM 680 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM 680
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM 680 = initPM 680 := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM 680
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM 680 = denoteGraph pm initPM 680 := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hW_init_shape : (initPM 680).shape = [32, 32] := by
      have hh := h_init_W.2.1
      simpa [initGoal_680, List.map_cons, List.map_nil] using hh
    have hW_sm_shape : (denoteGraph sm initSM 680).shape = [32, 32] := by
      rw [h_smW_init, hW_init_eq]; exact hW_init_shape
    have h_SM_681 := sm_eval_681 initSM
    have hSM681_shape : (denoteGraph sm initSM 681).shape = [1, 8, 32] := by
      rw [h_SM_681]
      exact fw_linear_3d_shape 1 8 32 32 _ _ h_x_sm_shape hW_sm_shape
    have h_PM_2873 := pm_eval_2873 initPM
    have h_PM_2874 := pm_eval_2874 initPM
    have h_PM_2875 := pm_eval_2875 initPM
    have h_PM_2876 := pm_eval_2876 initPM
    have h_PM_681 := pm_eval_681 initPM
    have h_main : denoteGraph sm initSM 681 = denoteGraph pm initPM 681 := by
      rw [h_SM_681, h_input_gather, hW_sm_pm]
      set X := allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM 2869, denoteGraph pm initPM 2870,
         denoteGraph pm initPM 2871, denoteGraph pm initPM 2872] with hXdef
      have hX_shape : X.shape = [1, 8, 32] := by
        rw [hXdef]
        rw [allGatherPrimDimN_shape 1 4 _ [1, 2, 32]
          (by simp [List.head?, h_pm_shapes_split.1])]
        rfl
      rw [fw_linear_split_dim1_4_1_8_32 X (denoteGraph pm initPM 680) hX_shape
        (by rw [h_pmW_init]; exact hW_init_shape)]
      have hI0_shape := h_pm_shapes_split.1
      have hI1_shape := h_pm_shapes_split.2.1
      have hI2_shape := h_pm_shapes_split.2.2.1
      have hI3_shape := h_pm_shapes_split.2.2.2
      have hchunk0 : chunkPrimDimN 1 4 0 X = denoteGraph pm initPM 2869 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx0 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk1 : chunkPrimDimN 1 4 1 X = denoteGraph pm initPM 2870 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx1 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk2 : chunkPrimDimN 1 4 2 X = denoteGraph pm initPM 2871 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx2 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      have hchunk3 : chunkPrimDimN 1 4 3 X = denoteGraph pm initPM 2872 := by
        rw [hXdef]
        exact chunk1_4_of_ag1_1_2_32_idx3 _ _ _ _ hI0_shape hI1_shape hI2_shape hI3_shape
      rw [hchunk0, hchunk1, hchunk2, hchunk3]
      rw [← h_PM_2873, ← h_PM_2874, ← h_PM_2875, ← h_PM_2876]
      rw [← h_PM_681]
    show (denoteGraph sm initSM 681).shape = goal_83.tsShape ∧
      _ = goal_83.tpShapes ∧
      denoteGraph sm initSM 681 =
        reconstructWithDim goal_83.gatherDim pm.numRanks 0
          (goal_83.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · change (denoteGraph sm initSM 681).shape = [1, 8, 32]
      exact hSM681_shape
    · have hPM681_shape : (denoteGraph pm initPM 681).shape = [1, 8, 32] := by
        rw [← h_main]; exact hSM681_shape
      change [(denoteGraph pm initPM 681).shape] = [[1, 8, 32]]
      rw [hPM681_shape]
    · change denoteGraph sm initSM 681 =
        reconstructWithDim 1 pm.numRanks 0 [denoteGraph pm initPM 681]
      rw [reconstructWithDim_singleton]
      exact h_main

end TrainVerify.Denote.GeneratedPatterns
