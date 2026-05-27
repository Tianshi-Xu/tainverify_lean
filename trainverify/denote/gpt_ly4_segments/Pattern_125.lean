/- Auto-generated pattern proof file.
   Pattern: 125
   Hash: 9df962180fe72704
   Goals: 251, 258, 268, 272, 282, 286, 296, 300, 310

   Structural argument:
     SM has 9 distinct `BW_layernorm` nodes; for each, PM has 4 per-rank
     `BW_layernorm` nodes (sharded along sequence axis dim=1) producing per-shard
     `dx`. This file:
       * registers per-node `applyNode_bw_layernorm_fst_out` unfoldings
         via per-goal `sm_eval_*` / `pm_eval_*` private theorems,
       * proves the algebraic bridge
           `(bw_layernorm g x w b).1 = allGatherDim1 [(bw_layernorm chunk_r g, chunk_r x, w, b).1 | r ∈ {0,1,2,3}]`
         for shape `[1,8,32]` (layernorm normalises over the last dim, so per-row
         derivatives are row-local and dim=1 sharding is orthogonal),
       * applies a generic singleton-lift to each of the 9 goals.
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_44
import denote.gpt_ly4_segments.Pattern_60
import denote.gpt_ly4_segments.Pattern_78
import denote.gpt_ly4_segments.Pattern_83
import denote.gpt_ly4_segments.Pattern_101
import denote.gpt_ly4_segments.Pattern_113
import denote.gpt_ly4_segments.Pattern_116
import denote.gpt_ly4_segments.Pattern_127
import denote.gpt_ly4_segments.Pattern_128

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_125_goalIds : List Nat := [251, 258, 268, 272, 282, 286, 296, 300, 310]
inductive pattern_125_target : Prop → Prop
  | goal_251 : pattern_125_target goal_251_stmt
  | goal_258 : pattern_125_target goal_258_stmt
  | goal_268 : pattern_125_target goal_268_stmt
  | goal_272 : pattern_125_target goal_272_stmt
  | goal_282 : pattern_125_target goal_282_stmt
  | goal_286 : pattern_125_target goal_286_stmt
  | goal_296 : pattern_125_target goal_296_stmt
  | goal_300 : pattern_125_target goal_300_stmt
  | goal_310 : pattern_125_target goal_310_stmt

def pattern_125_stmt : Prop :=
  ∀ {target : Prop}, pattern_125_target target → target

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

/-! ## Generic helpers for unfolding `denoteGraph` at a `BW_layernorm` node. -/

private theorem denote_bw_layernorm_dx_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (gTid xTid wTid bTid dxTid dwTid dbTid : Tid) (rk : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.BW_layernorm",
                      ins := [gTid, xTid, wTid, bTid],
                      outs := [dxTid, dwTid, dbTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (h1 : dxTid ≠ dwTid) (h2 : dxTid ≠ dbTid) (h3 : dwTid ≠ dbTid)
    (hsuf_dx : ∀ n ∈ g.nodes.drop (K+1), dxTid ∉ n.outs)
    (hsuf_g : ∀ n ∈ g.nodes.drop K, gTid ∉ n.outs)
    (hsuf_x : ∀ n ∈ g.nodes.drop K, xTid ∉ n.outs)
    (hsuf_w : ∀ n ∈ g.nodes.drop K, wTid ∉ n.outs)
    (hsuf_b : ∀ n ∈ g.nodes.drop K, bTid ∉ n.outs) :
    denoteGraph g initStore dxTid =
      (bw_layernorm (denoteGraph g initStore gTid) (denoteGraph g initStore xTid)
                    (denoteGraph g initStore wTid) (denoteGraph g initStore bTid)).1 := by
  have hh1 : denoteGraph g initStore dxTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore dxTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore dxTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_dx
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
  change applyNode g (denoteGraph { g with nodes := g.nodes.take K } initStore) node dxTid = _
  rw [hnode]
  rw [applyNode_bw_layernorm_fst_out g _ rk gTid xTid wTid bTid dxTid dwTid dbTid h1 h2 h3]
  have hg : (denoteGraph { g with nodes := g.nodes.take K } initStore) gTid =
      denoteGraph g initStore gTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore gTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_g).symm
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
  have hb : (denoteGraph { g with nodes := g.nodes.take K } initStore) bTid =
      denoteGraph g initStore bTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore bTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_b).symm
  rw [hg, hx, hw, hb]

private theorem denote_init_tid (g : GraphDecl) (initStore : Store) (tid : Tid)
    (hno : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraph g initStore tid = initStore tid := by
  have h := denoteGraph_tid_eq_of_suffix_no_writes g initStore tid
    [] g.nodes (by simp) hno
  rw [h]
  have heq : ({ g with nodes := [] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := [] } := by cases g; rfl
  rw [heq, denoteGraph_nodes_nil]

/-! ## Algebraic bridge for `bw_layernorm` (dx component) under dim=1 sharding. -/

/-- Unfolding of `(bw_layernorm g x w b).1` when `x.shape.reverse` starts with `d`. -/
private theorem bw_layernorm_dx_eq (g x w b : Tensor) (d : Nat) (rest : List Nat)
    (hrev : x.shape.reverse = d :: rest) :
    (bw_layernorm g x w b).1 = Tensor.mkShape x.shape (fun outIdx =>
      let row := outIdx.1 / d
      let j := outIdx.1 % d
      let mean := layerNormMeanAt x row d
      let var := layerNormVarAt x row d mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      let xhat := (valAt x outIdx.1 - mean) * invStd
      let sumDy := ∑ k ∈ Finset.range d,
        valAt g (row * d + k) * valAt w k
      let sumDyXhat := ∑ k ∈ Finset.range d,
        let xhatK := (valAt x (row * d + k) - mean) * invStd
        (valAt g (row * d + k) * valAt w k) * xhatK
      invStd / (d : Scalar) *
        ((d : Scalar) * (valAt g outIdx.1 * valAt w j) - sumDy - xhat * sumDyXhat)) := by
  unfold bw_layernorm
  rw [hrev]

/-- Shape of `(bw_layernorm g x w b).1` for input shape `[1,8,32]`. -/
private theorem bw_layernorm_dx_shape_1_8_32 (g x w b : Tensor)
    (hx : x.shape = [1, 8, 32]) :
    (bw_layernorm g x w b).1.shape = [1, 8, 32] := by
  rw [bw_layernorm_dx_eq g x w b 32 [8, 1] (by rw [hx]; rfl)]
  simp [Tensor.mkShape, hx]

/-- Shape of `(bw_layernorm g x w b).1` for input shape `[1,2,32]`. -/
private theorem bw_layernorm_dx_shape_1_2_32 (g x w b : Tensor)
    (hx : x.shape = [1, 2, 32]) :
    (bw_layernorm g x w b).1.shape = [1, 2, 32] := by
  rw [bw_layernorm_dx_eq g x w b 32 [2, 1] (by rw [hx]; rfl)]
  simp [Tensor.mkShape, hx]

/-- valAt of `(bw_layernorm g x w b).1` at index `p*32+j` for shape `[1,8,32]`. -/
private theorem bw_layernorm_dx_valAt_1_8_32 (g x w b : Tensor) (p j : Nat)
    (hx : x.shape = [1, 8, 32]) (hp : p < 8) (hj : j < 32) :
    valAt (bw_layernorm g x w b).1 (p * 32 + j) =
      let mean := layerNormMeanAt x p 32
      let var := layerNormVarAt x p 32 mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      let xhat := (valAt x (p * 32 + j) - mean) * invStd
      let sumDy := ∑ k ∈ Finset.range 32,
        valAt g (p * 32 + k) * valAt w k
      let sumDyXhat := ∑ k ∈ Finset.range 32,
        let xhatK := (valAt x (p * 32 + k) - mean) * invStd
        (valAt g (p * 32 + k) * valAt w k) * xhatK
      invStd / (32 : Scalar) *
        ((32 : Scalar) * (valAt g (p * 32 + j) * valAt w j) - sumDy - xhat * sumDyXhat) := by
  have hidx : p * 32 + j < 256 := by
    have h1 : p * 32 ≤ 7 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  rw [bw_layernorm_dx_eq g x w b 32 [8, 1] (by rw [hx]; rfl)]
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, hx, prodShape]; exact hidx)]
  simp only [Tensor.mkShape]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  rw [hdj, hmj]
  push_cast
  ring

/-- valAt of `(bw_layernorm g x w b).1` at index `p*32+j` for shape `[1,2,32]`. -/
private theorem bw_layernorm_dx_valAt_1_2_32 (g x w b : Tensor) (p j : Nat)
    (hx : x.shape = [1, 2, 32]) (hp : p < 2) (hj : j < 32) :
    valAt (bw_layernorm g x w b).1 (p * 32 + j) =
      let mean := layerNormMeanAt x p 32
      let var := layerNormVarAt x p 32 mean
      let invStd := 1 / sqrtFn (var + layerNormEps)
      let xhat := (valAt x (p * 32 + j) - mean) * invStd
      let sumDy := ∑ k ∈ Finset.range 32,
        valAt g (p * 32 + k) * valAt w k
      let sumDyXhat := ∑ k ∈ Finset.range 32,
        let xhatK := (valAt x (p * 32 + k) - mean) * invStd
        (valAt g (p * 32 + k) * valAt w k) * xhatK
      invStd / (32 : Scalar) *
        ((32 : Scalar) * (valAt g (p * 32 + j) * valAt w j) - sumDy - xhat * sumDyXhat) := by
  have hidx : p * 32 + j < 64 := by
    have h1 : p * 32 ≤ 1 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  rw [bw_layernorm_dx_eq g x w b 32 [2, 1] (by rw [hx]; rfl)]
  rw [valAt_of_lt _ _ (by simp [Tensor.mkShape, hx, prodShape]; exact hidx)]
  simp only [Tensor.mkShape]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  rw [hdj, hmj]
  push_cast
  ring

/-- The core bw_layernorm dx split lemma for shape [1,8,32], dim=1 sharded into
    4 chunks of size 2. -/
private theorem bw_layernorm_dx_split_dim1_4_1_8_32 (g x w b : Tensor)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 32]) :
    (bw_layernorm g x w b).1 =
      allGatherPrimDimN 1 4 0
        [(bw_layernorm (chunkPrimDimN 1 4 0 g) (chunkPrimDimN 1 4 0 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 1 g) (chunkPrimDimN 1 4 1 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 2 g) (chunkPrimDimN 1 4 2 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 3 g) (chunkPrimDimN 1 4 3 x) w b).1] := by
  have hchunk_x_shape : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
    intro r _
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hchunk_g_shape : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r g).shape = [1, 2, 32] := by
    intro r _
    rw [chunkPrimDimN_shape 1 4 r _ _ hg (by omega)]
    simp [List.set, List.getD]
  have hdx_chunk_shape : ∀ r, r < 4 →
      (bw_layernorm (chunkPrimDimN 1 4 r g) (chunkPrimDimN 1 4 r x) w b).1.shape = [1, 2, 32] := by
    intro r hr
    exact bw_layernorm_dx_shape_1_2_32 _ _ w b (hchunk_x_shape r hr)
  have hlhs_shape : (bw_layernorm g x w b).1.shape = [1, 8, 32] :=
    bw_layernorm_dx_shape_1_8_32 g x w b hx
  have hhead : ((([(bw_layernorm (chunkPrimDimN 1 4 0 g) (chunkPrimDimN 1 4 0 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 1 g) (chunkPrimDimN 1 4 1 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 2 g) (chunkPrimDimN 1 4 2 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 3 g) (chunkPrimDimN 1 4 3 x) w b).1] : List Tensor).head?).map
       (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [List.head?]
    exact hdx_chunk_shape 0 (by omega)
  have hrhs_shape : (allGatherPrimDimN 1 4 0
      [(bw_layernorm (chunkPrimDimN 1 4 0 g) (chunkPrimDimN 1 4 0 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 1 g) (chunkPrimDimN 1 4 1 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 2 g) (chunkPrimDimN 1 4 2 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 3 g) (chunkPrimDimN 1 4 3 x) w b).1]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hlhs_shape, hrhs_shape]
  · intro idx hidx
    rw [hlhs_shape] at hidx
    have hidx256 : idx < 256 := by simpa [prodShape] using hidx
    set p := idx / 32 with hp_def
    set j := idx % 32 with hj_def
    have hp_lt : p < 8 := by
      have : idx / 32 < 256 / 32 := Nat.div_lt_div_of_lt_of_dvd ⟨8, rfl⟩ hidx256
      simpa using this
    have hj_lt : j < 32 := by exact Nat.mod_lt idx (by omega)
    have hidx_eq : idx = p * 32 + j := by
      subst p j; omega
    rw [hidx_eq]
    rw [bw_layernorm_dx_valAt_1_8_32 g x w b p j hx hp_lt hj_lt]
    have hrhs_idx : p * 32 + j < prodShape (allGatherPrimDimN 1 4 0
        [(bw_layernorm (chunkPrimDimN 1 4 0 g) (chunkPrimDimN 1 4 0 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 1 g) (chunkPrimDimN 1 4 1 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 2 g) (chunkPrimDimN 1 4 2 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 3 g) (chunkPrimDimN 1 4 3 x) w b).1]).shape := by
      rw [hrhs_shape]; simp [prodShape]; omega
    rw [valAt_of_lt _ _ hrhs_idx]
    unfold allGatherPrimDimN Tensor.mkShape
    simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.drop, List.foldl,
      show (8 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
      show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
      show (1 : Nat) ≠ 0 by omega, ite_false]
    simp only [show (2 : Nat) * 4 * 1 = 8 by norm_num,
      show (2 : Nat) * 1 = 2 by norm_num,
      show (8 : Nat) * (1 * 32) = 256 by norm_num,
      show (1 : Nat) * 32 = 32 by norm_num,
      show (2 : Nat) * (1 * 32) = 64 by norm_num,
      show (256 : Nat) = 0 ↔ False by simp,
      show (32 : Nat) = 0 ↔ False by simp,
      show (64 : Nat) = 0 ↔ False by simp,
      ite_false]
    set r := p / 2 with hr_def
    set p' := p % 2 with hp'_def
    have hr_lt : r < 4 := by
      have : p / 2 < 8 / 2 := Nat.div_lt_div_of_lt_of_dvd ⟨4, rfl⟩ hp_lt
      simpa using this
    have hp'_lt : p' < 2 := Nat.mod_lt p (by omega)
    have hp_eq : p = r * 2 + p' := by subst r p'; omega
    have hd256 : (p * 32 + j) / 256 = 0 := by
      apply Nat.div_eq_of_lt; omega
    have hm256 : (p * 32 + j) % 256 = p * 32 + j := by
      apply Nat.mod_eq_of_lt; omega
    rw [hd256, hm256]
    have hd32 : (p * 32 + j) / 32 = p := by omega
    have hm32 : (p * 32 + j) % 32 = j := by omega
    rw [hd32, hm32]
    have hpieces : (p / 2 : Nat) = r := rfl
    rw [hpieces]
    have hjLocal : (p % 2 : Nat) = p' := rfl
    rw [show (p % 2 : Nat) = p' from rfl]
    have hpL_x : valAt x (p * 32 + j) =
        valAt (chunkPrimDimN 1 4 r x) (p' * 32 + j) := by
      rw [chunk_dim1_4_1_8_32_valAt x r p' j hx hr_lt hp'_lt hj_lt, ← hp_eq]
    have hmeanL : layerNormMeanAt x p 32 =
        layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32 := by
      rw [layerNormMeanAt_chunk_dim1_4_1_8_32 x r p' hx hr_lt hp'_lt, ← hp_eq]
    -- Pointwise per-k bridges for x and g.
    have hpL_x_k : ∀ k ∈ Finset.range 32,
        valAt x (p * 32 + k) =
          valAt (chunkPrimDimN 1 4 r x) (p' * 32 + k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [chunk_dim1_4_1_8_32_valAt x r p' k hx hr_lt hp'_lt hk, ← hp_eq]
    have hpL_g_k : ∀ k ∈ Finset.range 32,
        valAt g (p * 32 + k) =
          valAt (chunkPrimDimN 1 4 r g) (p' * 32 + k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [chunk_dim1_4_1_8_32_valAt g r p' k hg hr_lt hp'_lt hk, ← hp_eq]
    have hpL_g : valAt g (p * 32 + j) =
        valAt (chunkPrimDimN 1 4 r g) (p' * 32 + j) := by
      rw [chunk_dim1_4_1_8_32_valAt g r p' j hg hr_lt hp'_lt hj_lt, ← hp_eq]
    -- Rewrite the LHS via the chunk equalities.
    rw [hpL_x, hmeanL]
    rw [show layerNormVarAt x p 32 (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32)
            = layerNormVarAt (chunkPrimDimN 1 4 r x) p' 32
                (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) from by
      rw [layerNormVarAt_chunk_dim1_4_1_8_32 x r p'
          (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) hx hr_lt hp'_lt, ← hp_eq]]
    rw [hpL_g]
    -- Rewrite the two sums over k.
    rw [show (∑ k ∈ Finset.range 32, valAt g (p * 32 + k) * valAt w k)
          = ∑ k ∈ Finset.range 32, valAt (chunkPrimDimN 1 4 r g) (p' * 32 + k) * valAt w k from by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpL_g_k k hk]]
    rw [show (∑ k ∈ Finset.range 32,
          let xhatK := (valAt x (p * 32 + k) - layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) *
            (1 / sqrtFn (layerNormVarAt (chunkPrimDimN 1 4 r x) p' 32
              (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) + layerNormEps))
          (valAt g (p * 32 + k) * valAt w k) * xhatK)
        = ∑ k ∈ Finset.range 32,
          let xhatK := (valAt (chunkPrimDimN 1 4 r x) (p' * 32 + k) -
              layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) *
            (1 / sqrtFn (layerNormVarAt (chunkPrimDimN 1 4 r x) p' 32
              (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) + layerNormEps))
          (valAt (chunkPrimDimN 1 4 r g) (p' * 32 + k) * valAt w k) * xhatK from by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpL_x_k k hk, hpL_g_k k hk]]
    -- Now the LHS equals bw_layernorm_dx_valAt_1_2_32 of the chunked tensors.
    rw [← bw_layernorm_dx_valAt_1_2_32 (chunkPrimDimN 1 4 r g) (chunkPrimDimN 1 4 r x) w b p' j
        (hchunk_x_shape r hr_lt) hp'_lt hj_lt]
    rw [show (0 : Nat) * 64 + p' * 32 + j = p' * 32 + j by ring]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with h0 | h1 | h2 | h3
    all_goals first
      | (rw [h0]; rfl)
      | (rw [h1]; rfl)
      | (rw [h2]; rfl)
      | (rw [h3]; rfl)

/-! ## Chunk-of-AllGather helpers (private; identical in spirit to Pattern_21). -/

private lemma valAt_ag_1_2_32_pj (xs : List Tensor) (p j : Nat)
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
  have hd256 : (p * 32 + j) / 256 = 0 := by
    apply Nat.div_eq_of_lt; omega
  have hm256 : (p * 32 + j) % 256 = p * 32 + j := Nat.mod_eq_of_lt hidx_lt
  have hd32 : (p * 32 + j) / 32 = p := by omega
  have hm32 : (p * 32 + j) % 32 = j := by omega
  rw [hm256, hd32, hm32]
  congr 1
  rw [hd256]
  ring

private lemma chunk_of_ag_1_2_32 (xs : List Tensor) (r : Nat) (hr : r < 4)
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
    rw [chunk_dim1_4_1_8_32_valAt _ r p j hag_shape hr hpb hjb]
    have hrp_lt : r * 2 + p < 8 := by
      have : r * 2 ≤ 3 * 2 := Nat.mul_le_mul_right 2 (by omega); omega
    rw [valAt_ag_1_2_32_pj xs (r * 2 + p) j hhead hrp_lt hjb]
    have hd : (r * 2 + p) / 2 = r := by omega
    have hm : (r * 2 + p) % 2 = p := by omega
    rw [hd, hm]

private lemma chunk_of_ag_1_2_32_explicit (t0 t1 t2 t3 : Tensor) (r : Nat) (hr : r < 4)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) =
      ([t0, t1, t2, t3]).getD r (zeroTensor [1, 2, 32]) := by
  apply chunk_of_ag_1_2_32 _ r hr
  · simp [h0]
  · intro i hi
    match i, hi with
    | 0, _ => simpa [List.getD] using h0
    | 1, _ => simpa [List.getD] using h1
    | 2, _ => simpa [List.getD] using h2
    | 3, _ => simpa [List.getD] using h3

private lemma chunk_of_ag_1_2_32_idx0 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 0 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t0 := by
  rw [chunk_of_ag_1_2_32_explicit t0 t1 t2 t3 0 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk_of_ag_1_2_32_idx1 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 1 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t1 := by
  rw [chunk_of_ag_1_2_32_explicit t0 t1 t2 t3 1 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk_of_ag_1_2_32_idx2 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 2 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t2 := by
  rw [chunk_of_ag_1_2_32_explicit t0 t1 t2 t3 2 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk_of_ag_1_2_32_idx3 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 3 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t3 := by
  rw [chunk_of_ag_1_2_32_explicit t0 t1 t2 t3 3 (by omega) h0 h1 h2 h3]; rfl

/-! ## Generic singleton lift for `BW_layernorm (dx)` + `AllGather dim=1`. -/

private theorem bw_layernorm_dx_dim1_4_singleton_lift
    (initSM initPM : Store)
    (smOutTid smGTid smXTid wTid bTid : Tid)
    (pmOut0 pmOut1 pmOut2 pmOut3 : Tid)
    (pmG0 pmG1 pmG2 pmG3 : Tid)
    (pmX0 pmX1 pmX2 pmX3 : Tid)
    (h_sm_eval : denoteGraph sm initSM smOutTid =
      (bw_layernorm (denoteGraph sm initSM smGTid) (denoteGraph sm initSM smXTid)
                    (denoteGraph sm initSM wTid)  (denoteGraph sm initSM bTid)).1)
    (h_pm0_eval : denoteGraph pm initPM pmOut0 =
      (bw_layernorm (denoteGraph pm initPM pmG0) (denoteGraph pm initPM pmX0)
                    (denoteGraph pm initPM wTid)  (denoteGraph pm initPM bTid)).1)
    (h_pm1_eval : denoteGraph pm initPM pmOut1 =
      (bw_layernorm (denoteGraph pm initPM pmG1) (denoteGraph pm initPM pmX1)
                    (denoteGraph pm initPM wTid)  (denoteGraph pm initPM bTid)).1)
    (h_pm2_eval : denoteGraph pm initPM pmOut2 =
      (bw_layernorm (denoteGraph pm initPM pmG2) (denoteGraph pm initPM pmX2)
                    (denoteGraph pm initPM wTid)  (denoteGraph pm initPM bTid)).1)
    (h_pm3_eval : denoteGraph pm initPM pmOut3 =
      (bw_layernorm (denoteGraph pm initPM pmG3) (denoteGraph pm initPM pmX3)
                    (denoteGraph pm initPM wTid)  (denoteGraph pm initPM bTid)).1)
    (hW_sm_pm : denoteGraph sm initSM wTid = denoteGraph pm initPM wTid)
    (hB_sm_pm : denoteGraph sm initSM bTid = denoteGraph pm initPM bTid)
    (h_g_gather : denoteGraph sm initSM smGTid =
      allGatherPrimDimN 1 4 0 [denoteGraph pm initPM pmG0, denoteGraph pm initPM pmG1,
                                denoteGraph pm initPM pmG2, denoteGraph pm initPM pmG3])
    (h_x_gather : denoteGraph sm initSM smXTid =
      allGatherPrimDimN 1 4 0 [denoteGraph pm initPM pmX0, denoteGraph pm initPM pmX1,
                                denoteGraph pm initPM pmX2, denoteGraph pm initPM pmX3])
    (hG0 : (denoteGraph pm initPM pmG0).shape = [1, 2, 32])
    (hG1 : (denoteGraph pm initPM pmG1).shape = [1, 2, 32])
    (hG2 : (denoteGraph pm initPM pmG2).shape = [1, 2, 32])
    (hG3 : (denoteGraph pm initPM pmG3).shape = [1, 2, 32])
    (hX0 : (denoteGraph pm initPM pmX0).shape = [1, 2, 32])
    (hX1 : (denoteGraph pm initPM pmX1).shape = [1, 2, 32])
    (hX2 : (denoteGraph pm initPM pmX2).shape = [1, 2, 32])
    (hX3 : (denoteGraph pm initPM pmX3).shape = [1, 2, 32]) :
    (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] ∧
      [(denoteGraph pm initPM pmOut0).shape, (denoteGraph pm initPM pmOut1).shape,
       (denoteGraph pm initPM pmOut2).shape, (denoteGraph pm initPM pmOut3).shape] =
        ([[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] : List Shape) ∧
      denoteGraph sm initSM smOutTid =
        reconstructWithDim 1 pm.numRanks 0
          [denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
           denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3] := by
  have hG_gather_sh : (denoteGraph sm initSM smGTid).shape = [1, 8, 32] := by
    rw [h_g_gather]
    have hh : (([denoteGraph pm initPM pmG0, denoteGraph pm initPM pmG1,
                  denoteGraph pm initPM pmG2, denoteGraph pm initPM pmG3]
                 : List Tensor).head?.map (·.shape)).getD [] = [1, 2, 32] := by simp [hG0]
    rw [allGatherPrimDimN_shape 1 4 _ _ hh]; simp [List.set, List.getD]
  have hX_gather_sh : (denoteGraph sm initSM smXTid).shape = [1, 8, 32] := by
    rw [h_x_gather]
    have hh : (([denoteGraph pm initPM pmX0, denoteGraph pm initPM pmX1,
                  denoteGraph pm initPM pmX2, denoteGraph pm initPM pmX3]
                 : List Tensor).head?.map (·.shape)).getD [] = [1, 2, 32] := by simp [hX0]
    rw [allGatherPrimDimN_shape 1 4 _ _ hh]; simp [List.set, List.getD]
  have hSmOut_shape : (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] := by
    rw [h_sm_eval]
    exact bw_layernorm_dx_shape_1_8_32 _ _ _ _ hX_gather_sh
  have hP0_shape : (denoteGraph pm initPM pmOut0).shape = [1, 2, 32] := by
    rw [h_pm0_eval]; exact bw_layernorm_dx_shape_1_2_32 _ _ _ _ hX0
  have hP1_shape : (denoteGraph pm initPM pmOut1).shape = [1, 2, 32] := by
    rw [h_pm1_eval]; exact bw_layernorm_dx_shape_1_2_32 _ _ _ _ hX1
  have hP2_shape : (denoteGraph pm initPM pmOut2).shape = [1, 2, 32] := by
    rw [h_pm2_eval]; exact bw_layernorm_dx_shape_1_2_32 _ _ _ _ hX2
  have hP3_shape : (denoteGraph pm initPM pmOut3).shape = [1, 2, 32] := by
    rw [h_pm3_eval]; exact bw_layernorm_dx_shape_1_2_32 _ _ _ _ hX3
  refine ⟨hSmOut_shape, ?_, ?_⟩
  · simp [hP0_shape, hP1_shape, hP2_shape, hP3_shape]
  · have hnr : pm.numRanks = 4 := rfl
    rw [hnr]
    have hhead_pieces : (([denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
                            denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3]
                           : List Tensor).head?.map (·.shape)).getD [] = [1, 2, 32] := by
      simp [hP0_shape]
    rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
        (by rw [hP0_shape]; intro hc; cases hc)]
    rw [h_sm_eval, h_g_gather, h_x_gather, hW_sm_pm, hB_sm_pm]
    rw [bw_layernorm_dx_split_dim1_4_1_8_32 _ _ _ _
        (by have hh : (([denoteGraph pm initPM pmG0, denoteGraph pm initPM pmG1,
                          denoteGraph pm initPM pmG2, denoteGraph pm initPM pmG3]
                         : List Tensor).head?.map (·.shape)).getD [] = [1, 2, 32] := by simp [hG0]
            rw [allGatherPrimDimN_shape 1 4 _ _ hh]; simp [List.set, List.getD])
        (by have hh : (([denoteGraph pm initPM pmX0, denoteGraph pm initPM pmX1,
                          denoteGraph pm initPM pmX2, denoteGraph pm initPM pmX3]
                         : List Tensor).head?.map (·.shape)).getD [] = [1, 2, 32] := by simp [hX0]
            rw [allGatherPrimDimN_shape 1 4 _ _ hh]; simp [List.set, List.getD])]
    rw [chunk_of_ag_1_2_32_idx0 _ _ _ _ hG0 hG1 hG2 hG3,
        chunk_of_ag_1_2_32_idx1 _ _ _ _ hG0 hG1 hG2 hG3,
        chunk_of_ag_1_2_32_idx2 _ _ _ _ hG0 hG1 hG2 hG3,
        chunk_of_ag_1_2_32_idx3 _ _ _ _ hG0 hG1 hG2 hG3,
        chunk_of_ag_1_2_32_idx0 _ _ _ _ hX0 hX1 hX2 hX3,
        chunk_of_ag_1_2_32_idx1 _ _ _ _ hX0 hX1 hX2 hX3,
        chunk_of_ag_1_2_32_idx2 _ _ _ _ hX0 hX1 hX2 hX3,
        chunk_of_ag_1_2_32_idx3 _ _ _ _ hX0 hX1 hX2 hX3]
    rw [← h_pm0_eval, ← h_pm1_eval, ← h_pm2_eval, ← h_pm3_eval]
/-! ## Per-goal node declarations -/

@[reducible] private def smN_251 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [893, 707, 708, 709], outs := [890, 891, 892] }
@[reducible] private def pmN_251_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [3359, 3321, 708, 709], outs := [3335, 3357, 3358] }
@[reducible] private def pmN_251_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [3362, 3322, 708, 709], outs := [3338, 3360, 3361] }
@[reducible] private def pmN_251_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [3365, 3323, 708, 709], outs := [3341, 3363, 3364] }
@[reducible] private def pmN_251_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [3368, 3324, 708, 709], outs := [3344, 3366, 3367] }
@[reducible] private def smN_258 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [727, 903, 568, 569], outs := [904, 725, 726] }
@[reducible] private def pmN_258_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [1160, 1141, 568, 569], outs := [1157, 1158, 1159] }
@[reducible] private def pmN_258_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [1164, 1142, 568, 569], outs := [1161, 1162, 1163] }
@[reducible] private def pmN_258_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [1168, 1143, 568, 569], outs := [1165, 1166, 1167] }
@[reducible] private def pmN_258_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [1172, 1144, 568, 569], outs := [1169, 1170, 1171] }
@[reducible] private def smN_268 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [758, 934, 594, 595], outs := [935, 756, 757] }
@[reducible] private def pmN_268_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [1544, 1525, 594, 595], outs := [1541, 1542, 1543] }
@[reducible] private def pmN_268_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [1548, 1526, 594, 595], outs := [1545, 1546, 1547] }
@[reducible] private def pmN_268_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [1552, 1527, 594, 595], outs := [1549, 1550, 1551] }
@[reducible] private def pmN_268_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [1556, 1528, 594, 595], outs := [1553, 1554, 1555] }
@[reducible] private def smN_272 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [769, 946, 603, 604], outs := [947, 767, 768] }
@[reducible] private def pmN_272_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [1680, 1661, 603, 604], outs := [1677, 1678, 1679] }
@[reducible] private def pmN_272_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [1684, 1662, 603, 604], outs := [1681, 1682, 1683] }
@[reducible] private def pmN_272_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [1688, 1663, 603, 604], outs := [1685, 1686, 1687] }
@[reducible] private def pmN_272_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [1692, 1664, 603, 604], outs := [1689, 1690, 1691] }
@[reducible] private def smN_282 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [800, 977, 629, 630], outs := [978, 798, 799] }
@[reducible] private def pmN_282_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [2100, 2081, 629, 630], outs := [2097, 2098, 2099] }
@[reducible] private def pmN_282_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [2104, 2082, 629, 630], outs := [2101, 2102, 2103] }
@[reducible] private def pmN_282_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [2108, 2083, 629, 630], outs := [2105, 2106, 2107] }
@[reducible] private def pmN_282_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [2112, 2084, 629, 630], outs := [2109, 2110, 2111] }
@[reducible] private def smN_286 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [811, 989, 638, 639], outs := [990, 809, 810] }
@[reducible] private def pmN_286_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [2244, 2225, 638, 639], outs := [2241, 2242, 2243] }
@[reducible] private def pmN_286_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [2248, 2226, 638, 639], outs := [2245, 2246, 2247] }
@[reducible] private def pmN_286_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [2252, 2227, 638, 639], outs := [2249, 2250, 2251] }
@[reducible] private def pmN_286_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [2256, 2228, 638, 639], outs := [2253, 2254, 2255] }
@[reducible] private def smN_296 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [842, 1020, 664, 665], outs := [1021, 840, 841] }
@[reducible] private def pmN_296_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [2656, 2637, 664, 665], outs := [2653, 2654, 2655] }
@[reducible] private def pmN_296_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [2660, 2638, 664, 665], outs := [2657, 2658, 2659] }
@[reducible] private def pmN_296_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [2664, 2639, 664, 665], outs := [2661, 2662, 2663] }
@[reducible] private def pmN_296_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [2668, 2640, 664, 665], outs := [2665, 2666, 2667] }
@[reducible] private def smN_300 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [853, 1032, 673, 674], outs := [1033, 851, 852] }
@[reducible] private def pmN_300_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [2800, 2781, 673, 674], outs := [2797, 2798, 2799] }
@[reducible] private def pmN_300_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [2804, 2782, 673, 674], outs := [2801, 2802, 2803] }
@[reducible] private def pmN_300_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [2808, 2783, 673, 674], outs := [2805, 2806, 2807] }
@[reducible] private def pmN_300_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [2812, 2784, 673, 674], outs := [2809, 2810, 2811] }
@[reducible] private def smN_310 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [884, 1063, 699, 700], outs := [1064, 882, 883] }
@[reducible] private def pmN_310_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_layernorm", ins := [3220, 3201, 699, 700], outs := [3217, 3218, 3219] }
@[reducible] private def pmN_310_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_layernorm", ins := [3224, 3202, 699, 700], outs := [3221, 3222, 3223] }
@[reducible] private def pmN_310_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_layernorm", ins := [3228, 3203, 699, 700], outs := [3225, 3226, 3227] }
@[reducible] private def pmN_310_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_layernorm", ins := [3232, 3204, 699, 700], outs := [3229, 3230, 3231] }

/-! ## Per-goal SM and PM eval theorems. -/

private theorem sm_eval_p125_251 (initSM : Store) :
    denoteGraph sm initSM 890 =
      (bw_layernorm (denoteGraph sm initSM 893) (denoteGraph sm initSM 707)
        (denoteGraph sm initSM 708) (denoteGraph sm initSM 709)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 120 893 707 708 709 890 891 892 0 smN_251 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_251_0 (initPM : Store) :
    denoteGraph pm initPM 3335 =
      (bw_layernorm (denoteGraph pm initPM 3359) (denoteGraph pm initPM 3321)
        (denoteGraph pm initPM 708) (denoteGraph pm initPM 709)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 789 3359 3321 708 709 3335 3357 3358 0 pmN_251_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_251_1 (initPM : Store) :
    denoteGraph pm initPM 3338 =
      (bw_layernorm (denoteGraph pm initPM 3362) (denoteGraph pm initPM 3322)
        (denoteGraph pm initPM 708) (denoteGraph pm initPM 709)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 790 3362 3322 708 709 3338 3360 3361 1 pmN_251_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_251_2 (initPM : Store) :
    denoteGraph pm initPM 3341 =
      (bw_layernorm (denoteGraph pm initPM 3365) (denoteGraph pm initPM 3323)
        (denoteGraph pm initPM 708) (denoteGraph pm initPM 709)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 791 3365 3323 708 709 3341 3363 3364 2 pmN_251_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_251_3 (initPM : Store) :
    denoteGraph pm initPM 3344 =
      (bw_layernorm (denoteGraph pm initPM 3368) (denoteGraph pm initPM 3324)
        (denoteGraph pm initPM 708) (denoteGraph pm initPM 709)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 792 3368 3324 708 709 3344 3366 3367 3 pmN_251_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_258 (initSM : Store) :
    denoteGraph sm initSM 904 =
      (bw_layernorm (denoteGraph sm initSM 727) (denoteGraph sm initSM 903)
        (denoteGraph sm initSM 568) (denoteGraph sm initSM 569)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 231 727 903 568 569 904 725 726 0 smN_258 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_258_0 (initPM : Store) :
    denoteGraph pm initPM 1157 =
      (bw_layernorm (denoteGraph pm initPM 1160) (denoteGraph pm initPM 1141)
        (denoteGraph pm initPM 568) (denoteGraph pm initPM 569)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1533 1160 1141 568 569 1157 1158 1159 0 pmN_258_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_258_1 (initPM : Store) :
    denoteGraph pm initPM 1161 =
      (bw_layernorm (denoteGraph pm initPM 1164) (denoteGraph pm initPM 1142)
        (denoteGraph pm initPM 568) (denoteGraph pm initPM 569)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1534 1164 1142 568 569 1161 1162 1163 1 pmN_258_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_258_2 (initPM : Store) :
    denoteGraph pm initPM 1165 =
      (bw_layernorm (denoteGraph pm initPM 1168) (denoteGraph pm initPM 1143)
        (denoteGraph pm initPM 568) (denoteGraph pm initPM 569)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1535 1168 1143 568 569 1165 1166 1167 2 pmN_258_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_258_3 (initPM : Store) :
    denoteGraph pm initPM 1169 =
      (bw_layernorm (denoteGraph pm initPM 1172) (denoteGraph pm initPM 1144)
        (denoteGraph pm initPM 568) (denoteGraph pm initPM 569)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1536 1172 1144 568 569 1169 1170 1171 3 pmN_258_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_268 (initSM : Store) :
    denoteGraph sm initSM 935 =
      (bw_layernorm (denoteGraph sm initSM 758) (denoteGraph sm initSM 934)
        (denoteGraph sm initSM 594) (denoteGraph sm initSM 595)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 209 758 934 594 595 935 756 757 0 smN_268 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_268_0 (initPM : Store) :
    denoteGraph pm initPM 1541 =
      (bw_layernorm (denoteGraph pm initPM 1544) (denoteGraph pm initPM 1525)
        (denoteGraph pm initPM 594) (denoteGraph pm initPM 595)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1394 1544 1525 594 595 1541 1542 1543 0 pmN_268_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_268_1 (initPM : Store) :
    denoteGraph pm initPM 1545 =
      (bw_layernorm (denoteGraph pm initPM 1548) (denoteGraph pm initPM 1526)
        (denoteGraph pm initPM 594) (denoteGraph pm initPM 595)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1395 1548 1526 594 595 1545 1546 1547 1 pmN_268_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_268_2 (initPM : Store) :
    denoteGraph pm initPM 1549 =
      (bw_layernorm (denoteGraph pm initPM 1552) (denoteGraph pm initPM 1527)
        (denoteGraph pm initPM 594) (denoteGraph pm initPM 595)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1396 1552 1527 594 595 1549 1550 1551 2 pmN_268_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_268_3 (initPM : Store) :
    denoteGraph pm initPM 1553 =
      (bw_layernorm (denoteGraph pm initPM 1556) (denoteGraph pm initPM 1528)
        (denoteGraph pm initPM 594) (denoteGraph pm initPM 595)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1397 1556 1528 594 595 1553 1554 1555 3 pmN_268_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_272 (initSM : Store) :
    denoteGraph sm initSM 947 =
      (bw_layernorm (denoteGraph sm initSM 769) (denoteGraph sm initSM 946)
        (denoteGraph sm initSM 603) (denoteGraph sm initSM 604)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 203 769 946 603 604 947 767 768 0 smN_272 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_272_0 (initPM : Store) :
    denoteGraph pm initPM 1677 =
      (bw_layernorm (denoteGraph pm initPM 1680) (denoteGraph pm initPM 1661)
        (denoteGraph pm initPM 603) (denoteGraph pm initPM 604)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1350 1680 1661 603 604 1677 1678 1679 0 pmN_272_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_272_1 (initPM : Store) :
    denoteGraph pm initPM 1681 =
      (bw_layernorm (denoteGraph pm initPM 1684) (denoteGraph pm initPM 1662)
        (denoteGraph pm initPM 603) (denoteGraph pm initPM 604)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1351 1684 1662 603 604 1681 1682 1683 1 pmN_272_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_272_2 (initPM : Store) :
    denoteGraph pm initPM 1685 =
      (bw_layernorm (denoteGraph pm initPM 1688) (denoteGraph pm initPM 1663)
        (denoteGraph pm initPM 603) (denoteGraph pm initPM 604)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1352 1688 1663 603 604 1685 1686 1687 2 pmN_272_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_272_3 (initPM : Store) :
    denoteGraph pm initPM 1689 =
      (bw_layernorm (denoteGraph pm initPM 1692) (denoteGraph pm initPM 1664)
        (denoteGraph pm initPM 603) (denoteGraph pm initPM 604)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1353 1692 1664 603 604 1689 1690 1691 3 pmN_272_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_282 (initSM : Store) :
    denoteGraph sm initSM 978 =
      (bw_layernorm (denoteGraph sm initSM 800) (denoteGraph sm initSM 977)
        (denoteGraph sm initSM 629) (denoteGraph sm initSM 630)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 181 800 977 629 630 978 798 799 0 smN_282 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_282_0 (initPM : Store) :
    denoteGraph pm initPM 2097 =
      (bw_layernorm (denoteGraph pm initPM 2100) (denoteGraph pm initPM 2081)
        (denoteGraph pm initPM 629) (denoteGraph pm initPM 630)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1201 2100 2081 629 630 2097 2098 2099 0 pmN_282_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_282_1 (initPM : Store) :
    denoteGraph pm initPM 2101 =
      (bw_layernorm (denoteGraph pm initPM 2104) (denoteGraph pm initPM 2082)
        (denoteGraph pm initPM 629) (denoteGraph pm initPM 630)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1202 2104 2082 629 630 2101 2102 2103 1 pmN_282_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_282_2 (initPM : Store) :
    denoteGraph pm initPM 2105 =
      (bw_layernorm (denoteGraph pm initPM 2108) (denoteGraph pm initPM 2083)
        (denoteGraph pm initPM 629) (denoteGraph pm initPM 630)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1203 2108 2083 629 630 2105 2106 2107 2 pmN_282_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_282_3 (initPM : Store) :
    denoteGraph pm initPM 2109 =
      (bw_layernorm (denoteGraph pm initPM 2112) (denoteGraph pm initPM 2084)
        (denoteGraph pm initPM 629) (denoteGraph pm initPM 630)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1204 2112 2084 629 630 2109 2110 2111 3 pmN_282_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_286 (initSM : Store) :
    denoteGraph sm initSM 990 =
      (bw_layernorm (denoteGraph sm initSM 811) (denoteGraph sm initSM 989)
        (denoteGraph sm initSM 638) (denoteGraph sm initSM 639)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 175 811 989 638 639 990 809 810 0 smN_286 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_286_0 (initPM : Store) :
    denoteGraph pm initPM 2241 =
      (bw_layernorm (denoteGraph pm initPM 2244) (denoteGraph pm initPM 2225)
        (denoteGraph pm initPM 638) (denoteGraph pm initPM 639)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1153 2244 2225 638 639 2241 2242 2243 0 pmN_286_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_286_1 (initPM : Store) :
    denoteGraph pm initPM 2245 =
      (bw_layernorm (denoteGraph pm initPM 2248) (denoteGraph pm initPM 2226)
        (denoteGraph pm initPM 638) (denoteGraph pm initPM 639)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1154 2248 2226 638 639 2245 2246 2247 1 pmN_286_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_286_2 (initPM : Store) :
    denoteGraph pm initPM 2249 =
      (bw_layernorm (denoteGraph pm initPM 2252) (denoteGraph pm initPM 2227)
        (denoteGraph pm initPM 638) (denoteGraph pm initPM 639)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1155 2252 2227 638 639 2249 2250 2251 2 pmN_286_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_286_3 (initPM : Store) :
    denoteGraph pm initPM 2253 =
      (bw_layernorm (denoteGraph pm initPM 2256) (denoteGraph pm initPM 2228)
        (denoteGraph pm initPM 638) (denoteGraph pm initPM 639)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1156 2256 2228 638 639 2253 2254 2255 3 pmN_286_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_296 (initSM : Store) :
    denoteGraph sm initSM 1021 =
      (bw_layernorm (denoteGraph sm initSM 842) (denoteGraph sm initSM 1020)
        (denoteGraph sm initSM 664) (denoteGraph sm initSM 665)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 153 842 1020 664 665 1021 840 841 0 smN_296 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_296_0 (initPM : Store) :
    denoteGraph pm initPM 2653 =
      (bw_layernorm (denoteGraph pm initPM 2656) (denoteGraph pm initPM 2637)
        (denoteGraph pm initPM 664) (denoteGraph pm initPM 665)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1002 2656 2637 664 665 2653 2654 2655 0 pmN_296_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_296_1 (initPM : Store) :
    denoteGraph pm initPM 2657 =
      (bw_layernorm (denoteGraph pm initPM 2660) (denoteGraph pm initPM 2638)
        (denoteGraph pm initPM 664) (denoteGraph pm initPM 665)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1003 2660 2638 664 665 2657 2658 2659 1 pmN_296_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_296_2 (initPM : Store) :
    denoteGraph pm initPM 2661 =
      (bw_layernorm (denoteGraph pm initPM 2664) (denoteGraph pm initPM 2639)
        (denoteGraph pm initPM 664) (denoteGraph pm initPM 665)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1004 2664 2639 664 665 2661 2662 2663 2 pmN_296_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_296_3 (initPM : Store) :
    denoteGraph pm initPM 2665 =
      (bw_layernorm (denoteGraph pm initPM 2668) (denoteGraph pm initPM 2640)
        (denoteGraph pm initPM 664) (denoteGraph pm initPM 665)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 1005 2668 2640 664 665 2665 2666 2667 3 pmN_296_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_300 (initSM : Store) :
    denoteGraph sm initSM 1033 =
      (bw_layernorm (denoteGraph sm initSM 853) (denoteGraph sm initSM 1032)
        (denoteGraph sm initSM 673) (denoteGraph sm initSM 674)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 147 853 1032 673 674 1033 851 852 0 smN_300 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_300_0 (initPM : Store) :
    denoteGraph pm initPM 2797 =
      (bw_layernorm (denoteGraph pm initPM 2800) (denoteGraph pm initPM 2781)
        (denoteGraph pm initPM 673) (denoteGraph pm initPM 674)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 966 2800 2781 673 674 2797 2798 2799 0 pmN_300_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_300_1 (initPM : Store) :
    denoteGraph pm initPM 2801 =
      (bw_layernorm (denoteGraph pm initPM 2804) (denoteGraph pm initPM 2782)
        (denoteGraph pm initPM 673) (denoteGraph pm initPM 674)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 967 2804 2782 673 674 2801 2802 2803 1 pmN_300_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_300_2 (initPM : Store) :
    denoteGraph pm initPM 2805 =
      (bw_layernorm (denoteGraph pm initPM 2808) (denoteGraph pm initPM 2783)
        (denoteGraph pm initPM 673) (denoteGraph pm initPM 674)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 968 2808 2783 673 674 2805 2806 2807 2 pmN_300_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_300_3 (initPM : Store) :
    denoteGraph pm initPM 2809 =
      (bw_layernorm (denoteGraph pm initPM 2812) (denoteGraph pm initPM 2784)
        (denoteGraph pm initPM 673) (denoteGraph pm initPM 674)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 969 2812 2784 673 674 2809 2810 2811 3 pmN_300_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_p125_310 (initSM : Store) :
    denoteGraph sm initSM 1064 =
      (bw_layernorm (denoteGraph sm initSM 884) (denoteGraph sm initSM 1063)
        (denoteGraph sm initSM 699) (denoteGraph sm initSM 700)).1 := by
  apply denote_bw_layernorm_dx_step sm initSM 125 884 1063 699 700 1064 882 883 0 smN_310 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_310_0 (initPM : Store) :
    denoteGraph pm initPM 3217 =
      (bw_layernorm (denoteGraph pm initPM 3220) (denoteGraph pm initPM 3201)
        (denoteGraph pm initPM 699) (denoteGraph pm initPM 700)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 821 3220 3201 699 700 3217 3218 3219 0 pmN_310_0 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_310_1 (initPM : Store) :
    denoteGraph pm initPM 3221 =
      (bw_layernorm (denoteGraph pm initPM 3224) (denoteGraph pm initPM 3202)
        (denoteGraph pm initPM 699) (denoteGraph pm initPM 700)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 822 3224 3202 699 700 3221 3222 3223 1 pmN_310_1 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_310_2 (initPM : Store) :
    denoteGraph pm initPM 3225 =
      (bw_layernorm (denoteGraph pm initPM 3228) (denoteGraph pm initPM 3203)
        (denoteGraph pm initPM 699) (denoteGraph pm initPM 700)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 823 3228 3203 699 700 3225 3226 3227 2 pmN_310_2 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem pm_eval_p125_310_3 (initPM : Store) :
    denoteGraph pm initPM 3229 =
      (bw_layernorm (denoteGraph pm initPM 3232) (denoteGraph pm initPM 3204)
        (denoteGraph pm initPM 699) (denoteGraph pm initPM 700)).1 := by
  apply denote_bw_layernorm_dx_step pm initPM 824 3232 3204 699 700 3229 3230 3231 3 pmN_310_3 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Init evals for w/b tids (never written by sm or pm). -/
private theorem sm_eval_init_568 (initSM : Store) :
    denoteGraph sm initSM 568 = initSM 568 :=
  denote_init_tid sm initSM 568 (by decide)
private theorem pm_eval_init_568 (initPM : Store) :
    denoteGraph pm initPM 568 = initPM 568 :=
  denote_init_tid pm initPM 568 (by decide)
private theorem sm_eval_init_569 (initSM : Store) :
    denoteGraph sm initSM 569 = initSM 569 :=
  denote_init_tid sm initSM 569 (by decide)
private theorem pm_eval_init_569 (initPM : Store) :
    denoteGraph pm initPM 569 = initPM 569 :=
  denote_init_tid pm initPM 569 (by decide)
private theorem sm_eval_init_594 (initSM : Store) :
    denoteGraph sm initSM 594 = initSM 594 :=
  denote_init_tid sm initSM 594 (by decide)
private theorem pm_eval_init_594 (initPM : Store) :
    denoteGraph pm initPM 594 = initPM 594 :=
  denote_init_tid pm initPM 594 (by decide)
private theorem sm_eval_init_595 (initSM : Store) :
    denoteGraph sm initSM 595 = initSM 595 :=
  denote_init_tid sm initSM 595 (by decide)
private theorem pm_eval_init_595 (initPM : Store) :
    denoteGraph pm initPM 595 = initPM 595 :=
  denote_init_tid pm initPM 595 (by decide)
private theorem sm_eval_init_603 (initSM : Store) :
    denoteGraph sm initSM 603 = initSM 603 :=
  denote_init_tid sm initSM 603 (by decide)
private theorem pm_eval_init_603 (initPM : Store) :
    denoteGraph pm initPM 603 = initPM 603 :=
  denote_init_tid pm initPM 603 (by decide)
private theorem sm_eval_init_604 (initSM : Store) :
    denoteGraph sm initSM 604 = initSM 604 :=
  denote_init_tid sm initSM 604 (by decide)
private theorem pm_eval_init_604 (initPM : Store) :
    denoteGraph pm initPM 604 = initPM 604 :=
  denote_init_tid pm initPM 604 (by decide)
private theorem sm_eval_init_629 (initSM : Store) :
    denoteGraph sm initSM 629 = initSM 629 :=
  denote_init_tid sm initSM 629 (by decide)
private theorem pm_eval_init_629 (initPM : Store) :
    denoteGraph pm initPM 629 = initPM 629 :=
  denote_init_tid pm initPM 629 (by decide)
private theorem sm_eval_init_630 (initSM : Store) :
    denoteGraph sm initSM 630 = initSM 630 :=
  denote_init_tid sm initSM 630 (by decide)
private theorem pm_eval_init_630 (initPM : Store) :
    denoteGraph pm initPM 630 = initPM 630 :=
  denote_init_tid pm initPM 630 (by decide)
private theorem sm_eval_init_638 (initSM : Store) :
    denoteGraph sm initSM 638 = initSM 638 :=
  denote_init_tid sm initSM 638 (by decide)
private theorem pm_eval_init_638 (initPM : Store) :
    denoteGraph pm initPM 638 = initPM 638 :=
  denote_init_tid pm initPM 638 (by decide)
private theorem sm_eval_init_639 (initSM : Store) :
    denoteGraph sm initSM 639 = initSM 639 :=
  denote_init_tid sm initSM 639 (by decide)
private theorem pm_eval_init_639 (initPM : Store) :
    denoteGraph pm initPM 639 = initPM 639 :=
  denote_init_tid pm initPM 639 (by decide)
private theorem sm_eval_init_664 (initSM : Store) :
    denoteGraph sm initSM 664 = initSM 664 :=
  denote_init_tid sm initSM 664 (by decide)
private theorem pm_eval_init_664 (initPM : Store) :
    denoteGraph pm initPM 664 = initPM 664 :=
  denote_init_tid pm initPM 664 (by decide)
private theorem sm_eval_init_665 (initSM : Store) :
    denoteGraph sm initSM 665 = initSM 665 :=
  denote_init_tid sm initSM 665 (by decide)
private theorem pm_eval_init_665 (initPM : Store) :
    denoteGraph pm initPM 665 = initPM 665 :=
  denote_init_tid pm initPM 665 (by decide)
private theorem sm_eval_init_673 (initSM : Store) :
    denoteGraph sm initSM 673 = initSM 673 :=
  denote_init_tid sm initSM 673 (by decide)
private theorem pm_eval_init_673 (initPM : Store) :
    denoteGraph pm initPM 673 = initPM 673 :=
  denote_init_tid pm initPM 673 (by decide)
private theorem sm_eval_init_674 (initSM : Store) :
    denoteGraph sm initSM 674 = initSM 674 :=
  denote_init_tid sm initSM 674 (by decide)
private theorem pm_eval_init_674 (initPM : Store) :
    denoteGraph pm initPM 674 = initPM 674 :=
  denote_init_tid pm initPM 674 (by decide)
private theorem sm_eval_init_699 (initSM : Store) :
    denoteGraph sm initSM 699 = initSM 699 :=
  denote_init_tid sm initSM 699 (by decide)
private theorem pm_eval_init_699 (initPM : Store) :
    denoteGraph pm initPM 699 = initPM 699 :=
  denote_init_tid pm initPM 699 (by decide)
private theorem sm_eval_init_700 (initSM : Store) :
    denoteGraph sm initSM 700 = initSM 700 :=
  denote_init_tid sm initSM 700 (by decide)
private theorem pm_eval_init_700 (initPM : Store) :
    denoteGraph pm initPM 700 = initPM 700 :=
  denote_init_tid pm initPM 700 (by decide)
private theorem sm_eval_init_708 (initSM : Store) :
    denoteGraph sm initSM 708 = initSM 708 :=
  denote_init_tid sm initSM 708 (by decide)
private theorem pm_eval_init_708 (initPM : Store) :
    denoteGraph pm initPM 708 = initPM 708 :=
  denote_init_tid pm initPM 708 (by decide)
private theorem sm_eval_init_709 (initSM : Store) :
    denoteGraph sm initSM 709 = initSM 709 :=
  denote_init_tid sm initSM 709 (by decide)
private theorem pm_eval_init_709 (initPM : Store) :
    denoteGraph pm initPM 709 = initPM 709 :=
  denote_init_tid pm initPM 709 (by decide)

/-! ## Main prove_pattern_125 theorem. -/

theorem prove_pattern_125 : pattern_125_stmt := by
  intro target h
  cases h with
  | goal_251 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_254_stmt := prove_pattern_78 pattern_78_target.goal_254
      have hX : goal_104_stmt := prove_pattern_44 pattern_44_target.goal_104
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 3359).shape, (denoteGraph pm initPM 3362).shape,
           (denoteGraph pm initPM 3365).shape, (denoteGraph pm initPM 3368).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_254, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 3359).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3362).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3365).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3368).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 3321).shape, (denoteGraph pm initPM 3322).shape,
           (denoteGraph pm initPM 3323).shape, (denoteGraph pm initPM 3324).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_104, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 3321).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3322).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3323).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3324).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 893 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 3359, denoteGraph pm initPM 3362,
           denoteGraph pm initPM 3365, denoteGraph pm initPM 3368] := by
        have hh := hG_eq
        change denoteGraph sm initSM 893 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 3359 } : Piece), { rank := 1, tid := 3362 },
            { rank := 2, tid := 3365 }, { rank := 3, tid := 3368 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 707 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 3321, denoteGraph pm initPM 3322,
           denoteGraph pm initPM 3323, denoteGraph pm initPM 3324] := by
        have hh := hX_eq
        change denoteGraph sm initSM 707 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 3321 } : Piece), { rank := 1, tid := 3322 },
            { rank := 2, tid := 3323 }, { rank := 3, tid := 3324 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_708 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_709 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_708, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_709, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 708 = denoteGraph pm initPM 708 := by
        rw [sm_eval_init_708, pm_eval_init_708, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 709 = denoteGraph pm initPM 709 := by
        rw [sm_eval_init_709, pm_eval_init_709, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        890 893 707 708 709
        3335 3338 3341 3344
        3359 3362 3365 3368
        3321 3322 3323 3324
        (sm_eval_p125_251 initSM)
        (pm_eval_p125_251_0 initPM) (pm_eval_p125_251_1 initPM)
        (pm_eval_p125_251_2 initPM) (pm_eval_p125_251_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_258 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_114_stmt := prove_pattern_60 pattern_60_target.goal_114
      have hX : goal_257_stmt := prove_pattern_127 pattern_127_target.goal_257
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 1160).shape, (denoteGraph pm initPM 1164).shape,
           (denoteGraph pm initPM 1168).shape, (denoteGraph pm initPM 1172).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_114, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 1160).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1164).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1168).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1172).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 1141).shape, (denoteGraph pm initPM 1142).shape,
           (denoteGraph pm initPM 1143).shape, (denoteGraph pm initPM 1144).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_257, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 1141).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1142).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1143).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1144).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 727 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 1160, denoteGraph pm initPM 1164,
           denoteGraph pm initPM 1168, denoteGraph pm initPM 1172] := by
        have hh := hG_eq
        change denoteGraph sm initSM 727 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1160 } : Piece), { rank := 1, tid := 1164 },
            { rank := 2, tid := 1168 }, { rank := 3, tid := 1172 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 903 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 1141, denoteGraph pm initPM 1142,
           denoteGraph pm initPM 1143, denoteGraph pm initPM 1144] := by
        have hh := hX_eq
        change denoteGraph sm initSM 903 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1141 } : Piece), { rank := 1, tid := 1142 },
            { rank := 2, tid := 1143 }, { rank := 3, tid := 1144 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_568 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_569 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_568, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_569, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 568 = denoteGraph pm initPM 568 := by
        rw [sm_eval_init_568, pm_eval_init_568, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 569 = denoteGraph pm initPM 569 := by
        rw [sm_eval_init_569, pm_eval_init_569, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        904 727 903 568 569
        1157 1161 1165 1169
        1160 1164 1168 1172
        1141 1142 1143 1144
        (sm_eval_p125_258 initSM)
        (pm_eval_p125_258_0 initPM) (pm_eval_p125_258_1 initPM)
        (pm_eval_p125_258_2 initPM) (pm_eval_p125_258_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_268 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_140_stmt := prove_pattern_78 pattern_78_target.goal_140
      have hX : goal_267_stmt := prove_pattern_127 pattern_127_target.goal_267
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 1544).shape, (denoteGraph pm initPM 1548).shape,
           (denoteGraph pm initPM 1552).shape, (denoteGraph pm initPM 1556).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_140, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 1544).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1548).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1552).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1556).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 1525).shape, (denoteGraph pm initPM 1526).shape,
           (denoteGraph pm initPM 1527).shape, (denoteGraph pm initPM 1528).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_267, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 1525).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1526).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1527).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1528).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 758 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 1544, denoteGraph pm initPM 1548,
           denoteGraph pm initPM 1552, denoteGraph pm initPM 1556] := by
        have hh := hG_eq
        change denoteGraph sm initSM 758 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1544 } : Piece), { rank := 1, tid := 1548 },
            { rank := 2, tid := 1552 }, { rank := 3, tid := 1556 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 934 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 1525, denoteGraph pm initPM 1526,
           denoteGraph pm initPM 1527, denoteGraph pm initPM 1528] := by
        have hh := hX_eq
        change denoteGraph sm initSM 934 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1525 } : Piece), { rank := 1, tid := 1526 },
            { rank := 2, tid := 1527 }, { rank := 3, tid := 1528 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_594 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_595 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_594, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_595, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 594 = denoteGraph pm initPM 594 := by
        rw [sm_eval_init_594, pm_eval_init_594, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 595 = denoteGraph pm initPM 595 := by
        rw [sm_eval_init_595, pm_eval_init_595, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        935 758 934 594 595
        1541 1545 1549 1553
        1544 1548 1552 1556
        1525 1526 1527 1528
        (sm_eval_p125_268 initSM)
        (pm_eval_p125_268_0 initPM) (pm_eval_p125_268_1 initPM)
        (pm_eval_p125_268_2 initPM) (pm_eval_p125_268_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_272 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_149_stmt := prove_pattern_83 pattern_83_target.goal_149
      have hX : goal_271_stmt := prove_pattern_127 pattern_127_target.goal_271
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 1680).shape, (denoteGraph pm initPM 1684).shape,
           (denoteGraph pm initPM 1688).shape, (denoteGraph pm initPM 1692).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_149, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 1680).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1684).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1688).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1692).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 1661).shape, (denoteGraph pm initPM 1662).shape,
           (denoteGraph pm initPM 1663).shape, (denoteGraph pm initPM 1664).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_271, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 1661).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1662).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1663).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 1664).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 769 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 1680, denoteGraph pm initPM 1684,
           denoteGraph pm initPM 1688, denoteGraph pm initPM 1692] := by
        have hh := hG_eq
        change denoteGraph sm initSM 769 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1680 } : Piece), { rank := 1, tid := 1684 },
            { rank := 2, tid := 1688 }, { rank := 3, tid := 1692 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 946 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 1661, denoteGraph pm initPM 1662,
           denoteGraph pm initPM 1663, denoteGraph pm initPM 1664] := by
        have hh := hX_eq
        change denoteGraph sm initSM 946 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1661 } : Piece), { rank := 1, tid := 1662 },
            { rank := 2, tid := 1663 }, { rank := 3, tid := 1664 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_603 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_604 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_603, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_604, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 603 = denoteGraph pm initPM 603 := by
        rw [sm_eval_init_603, pm_eval_init_603, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 604 = denoteGraph pm initPM 604 := by
        rw [sm_eval_init_604, pm_eval_init_604, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        947 769 946 603 604
        1677 1681 1685 1689
        1680 1684 1688 1692
        1661 1662 1663 1664
        (sm_eval_p125_272 initSM)
        (pm_eval_p125_272_0 initPM) (pm_eval_p125_272_1 initPM)
        (pm_eval_p125_272_2 initPM) (pm_eval_p125_272_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_282 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_175_stmt := prove_pattern_78 pattern_78_target.goal_175
      have hX : goal_281_stmt := prove_pattern_127 pattern_127_target.goal_281
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 2100).shape, (denoteGraph pm initPM 2104).shape,
           (denoteGraph pm initPM 2108).shape, (denoteGraph pm initPM 2112).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_175, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 2100).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2104).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2108).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2112).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 2081).shape, (denoteGraph pm initPM 2082).shape,
           (denoteGraph pm initPM 2083).shape, (denoteGraph pm initPM 2084).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_281, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 2081).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2082).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2083).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2084).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 800 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2100, denoteGraph pm initPM 2104,
           denoteGraph pm initPM 2108, denoteGraph pm initPM 2112] := by
        have hh := hG_eq
        change denoteGraph sm initSM 800 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2100 } : Piece), { rank := 1, tid := 2104 },
            { rank := 2, tid := 2108 }, { rank := 3, tid := 2112 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 977 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2081, denoteGraph pm initPM 2082,
           denoteGraph pm initPM 2083, denoteGraph pm initPM 2084] := by
        have hh := hX_eq
        change denoteGraph sm initSM 977 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2081 } : Piece), { rank := 1, tid := 2082 },
            { rank := 2, tid := 2083 }, { rank := 3, tid := 2084 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_629 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_630 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_629, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_630, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 629 = denoteGraph pm initPM 629 := by
        rw [sm_eval_init_629, pm_eval_init_629, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 630 = denoteGraph pm initPM 630 := by
        rw [sm_eval_init_630, pm_eval_init_630, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        978 800 977 629 630
        2097 2101 2105 2109
        2100 2104 2108 2112
        2081 2082 2083 2084
        (sm_eval_p125_282 initSM)
        (pm_eval_p125_282_0 initPM) (pm_eval_p125_282_1 initPM)
        (pm_eval_p125_282_2 initPM) (pm_eval_p125_282_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_286 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_184_stmt := prove_pattern_101 pattern_101_target.goal_184
      have hX : goal_285_stmt := prove_pattern_128 pattern_128_target.goal_285
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 2244).shape, (denoteGraph pm initPM 2248).shape,
           (denoteGraph pm initPM 2252).shape, (denoteGraph pm initPM 2256).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_184, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 2244).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2248).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2252).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2256).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 2225).shape, (denoteGraph pm initPM 2226).shape,
           (denoteGraph pm initPM 2227).shape, (denoteGraph pm initPM 2228).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_285, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 2225).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2226).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2227).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2228).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 811 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2244, denoteGraph pm initPM 2248,
           denoteGraph pm initPM 2252, denoteGraph pm initPM 2256] := by
        have hh := hG_eq
        change denoteGraph sm initSM 811 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2244 } : Piece), { rank := 1, tid := 2248 },
            { rank := 2, tid := 2252 }, { rank := 3, tid := 2256 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 989 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2225, denoteGraph pm initPM 2226,
           denoteGraph pm initPM 2227, denoteGraph pm initPM 2228] := by
        have hh := hX_eq
        change denoteGraph sm initSM 989 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2225 } : Piece), { rank := 1, tid := 2226 },
            { rank := 2, tid := 2227 }, { rank := 3, tid := 2228 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_638 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_639 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_638, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_639, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 638 = denoteGraph pm initPM 638 := by
        rw [sm_eval_init_638, pm_eval_init_638, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 639 = denoteGraph pm initPM 639 := by
        rw [sm_eval_init_639, pm_eval_init_639, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        990 811 989 638 639
        2241 2245 2249 2253
        2244 2248 2252 2256
        2225 2226 2227 2228
        (sm_eval_p125_286 initSM)
        (pm_eval_p125_286_0 initPM) (pm_eval_p125_286_1 initPM)
        (pm_eval_p125_286_2 initPM) (pm_eval_p125_286_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_296 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_210_stmt := prove_pattern_113 pattern_113_target.goal_210
      have hX : goal_295_stmt := prove_pattern_128 pattern_128_target.goal_295
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 2656).shape, (denoteGraph pm initPM 2660).shape,
           (denoteGraph pm initPM 2664).shape, (denoteGraph pm initPM 2668).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_210, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 2656).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2660).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2664).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2668).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 2637).shape, (denoteGraph pm initPM 2638).shape,
           (denoteGraph pm initPM 2639).shape, (denoteGraph pm initPM 2640).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_295, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 2637).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2638).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2639).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2640).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 842 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2656, denoteGraph pm initPM 2660,
           denoteGraph pm initPM 2664, denoteGraph pm initPM 2668] := by
        have hh := hG_eq
        change denoteGraph sm initSM 842 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2656 } : Piece), { rank := 1, tid := 2660 },
            { rank := 2, tid := 2664 }, { rank := 3, tid := 2668 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 1020 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2637, denoteGraph pm initPM 2638,
           denoteGraph pm initPM 2639, denoteGraph pm initPM 2640] := by
        have hh := hX_eq
        change denoteGraph sm initSM 1020 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2637 } : Piece), { rank := 1, tid := 2638 },
            { rank := 2, tid := 2639 }, { rank := 3, tid := 2640 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_664 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_665 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_664, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_665, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 664 = denoteGraph pm initPM 664 := by
        rw [sm_eval_init_664, pm_eval_init_664, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 665 = denoteGraph pm initPM 665 := by
        rw [sm_eval_init_665, pm_eval_init_665, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        1021 842 1020 664 665
        2653 2657 2661 2665
        2656 2660 2664 2668
        2637 2638 2639 2640
        (sm_eval_p125_296 initSM)
        (pm_eval_p125_296_0 initPM) (pm_eval_p125_296_1 initPM)
        (pm_eval_p125_296_2 initPM) (pm_eval_p125_296_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_300 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_219_stmt := prove_pattern_116 pattern_116_target.goal_219
      have hX : goal_299_stmt := prove_pattern_128 pattern_128_target.goal_299
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 2800).shape, (denoteGraph pm initPM 2804).shape,
           (denoteGraph pm initPM 2808).shape, (denoteGraph pm initPM 2812).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_219, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 2800).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2804).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2808).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2812).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 2781).shape, (denoteGraph pm initPM 2782).shape,
           (denoteGraph pm initPM 2783).shape, (denoteGraph pm initPM 2784).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_299, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 2781).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2782).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2783).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 2784).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 853 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2800, denoteGraph pm initPM 2804,
           denoteGraph pm initPM 2808, denoteGraph pm initPM 2812] := by
        have hh := hG_eq
        change denoteGraph sm initSM 853 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2800 } : Piece), { rank := 1, tid := 2804 },
            { rank := 2, tid := 2808 }, { rank := 3, tid := 2812 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 1032 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 2781, denoteGraph pm initPM 2782,
           denoteGraph pm initPM 2783, denoteGraph pm initPM 2784] := by
        have hh := hX_eq
        change denoteGraph sm initSM 1032 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 2781 } : Piece), { rank := 1, tid := 2782 },
            { rank := 2, tid := 2783 }, { rank := 3, tid := 2784 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_673 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_674 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_673, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_674, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 673 = denoteGraph pm initPM 673 := by
        rw [sm_eval_init_673, pm_eval_init_673, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 674 = denoteGraph pm initPM 674 := by
        rw [sm_eval_init_674, pm_eval_init_674, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        1033 853 1032 673 674
        2797 2801 2805 2809
        2800 2804 2808 2812
        2781 2782 2783 2784
        (sm_eval_p125_300 initSM)
        (pm_eval_p125_300_0 initPM) (pm_eval_p125_300_1 initPM)
        (pm_eval_p125_300_2 initPM) (pm_eval_p125_300_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3
  | goal_310 =>
      intro initSM initPM hSmInit hPmInit hInitGoals
      have hG : goal_245_stmt := prove_pattern_113 pattern_113_target.goal_245
      have hX : goal_309_stmt := prove_pattern_128 pattern_128_target.goal_309
      have hGres := hG initSM initPM hSmInit hPmInit hInitGoals
      have hXres := hX initSM initPM hSmInit hPmInit hInitGoals
      obtain ⟨hG_sm_sh, hG_pm_sh, hG_eq⟩ := hGres
      obtain ⟨hX_sm_sh, hX_pm_sh, hX_eq⟩ := hXres
      -- Promote reconstruction equations to allGatherPrimDimN form.
      have hG_pm_sh' :
          [(denoteGraph pm initPM 3220).shape, (denoteGraph pm initPM 3224).shape,
           (denoteGraph pm initPM 3228).shape, (denoteGraph pm initPM 3232).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hG_pm_sh
        simp only [goal_245, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hG0, hG1, hG2, hG3⟩ :
          (denoteGraph pm initPM 3220).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3224).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3228).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3232).shape = [1, 2, 32] := by
        have hs := hG_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hX_pm_sh' :
          [(denoteGraph pm initPM 3201).shape, (denoteGraph pm initPM 3202).shape,
           (denoteGraph pm initPM 3203).shape, (denoteGraph pm initPM 3204).shape] =
            [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
        have hh := hX_pm_sh
        simp only [goal_309, List.map_cons, List.map_nil] at hh; exact hh
      have ⟨hX0, hX1, hX2, hX3⟩ :
          (denoteGraph pm initPM 3201).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3202).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3203).shape = [1, 2, 32] ∧
          (denoteGraph pm initPM 3204).shape = [1, 2, 32] := by
        have hs := hX_pm_sh'
        simp only [List.cons.injEq, and_true] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
      have hG_gather : denoteGraph sm initSM 884 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 3220, denoteGraph pm initPM 3224,
           denoteGraph pm initPM 3228, denoteGraph pm initPM 3232] := by
        have hh := hG_eq
        change denoteGraph sm initSM 884 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 3220 } : Piece), { rank := 1, tid := 3224 },
            { rank := 2, tid := 3228 }, { rank := 3, tid := 3232 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hG0]; intro hc; cases hc)]
      have hX_gather : denoteGraph sm initSM 1063 = allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM 3201, denoteGraph pm initPM 3202,
           denoteGraph pm initPM 3203, denoteGraph pm initPM 3204] := by
        have hh := hX_eq
        change denoteGraph sm initSM 1063 = reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 3201 } : Piece), { rank := 1, tid := 3202 },
            { rank := 2, tid := 3203 }, { rank := 3, tid := 3204 }].map
            (fun p => denoteGraph pm initPM p.tid)) at hh
        simp only [List.map_cons, List.map_nil] at hh
        rw [hh, show pm.numRanks = 4 from rfl]
        rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _
            (by rw [hX0]; intro hc; cases hc)]
      -- w/b equality across sm and pm via init goals
      have hInitW := hInitGoals initGoal_699 (by simp [initGoals])
      have hInitB := hInitGoals initGoal_700 (by simp [initGoals])
      obtain ⟨_, _, hW_rec⟩ := hInitW
      obtain ⟨_, _, hB_rec⟩ := hInitB
      simp only [initGoal_699, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hW_rec
      simp only [initGoal_700, List.map_cons, List.map_nil,
                 reconstructWithDim_singleton] at hB_rec
      have hW_sm_pm : denoteGraph sm initSM 699 = denoteGraph pm initPM 699 := by
        rw [sm_eval_init_699, pm_eval_init_699, hW_rec]
      have hB_sm_pm : denoteGraph sm initSM 700 = denoteGraph pm initPM 700 := by
        rw [sm_eval_init_700, pm_eval_init_700, hB_rec]
      -- Apply the singleton lift.
      exact bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
        1064 884 1063 699 700
        3217 3221 3225 3229
        3220 3224 3228 3232
        3201 3202 3203 3204
        (sm_eval_p125_310 initSM)
        (pm_eval_p125_310_0 initPM) (pm_eval_p125_310_1 initPM)
        (pm_eval_p125_310_2 initPM) (pm_eval_p125_310_3 initPM)
        hW_sm_pm hB_sm_pm hG_gather hX_gather
        hG0 hG1 hG2 hG3 hX0 hX1 hX2 hX3


end TrainVerify.Denote.GeneratedPatterns
