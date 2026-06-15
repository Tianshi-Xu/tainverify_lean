#!/usr/bin/env python3
"""Generate Pattern_125.lean - BW_layernorm dX with no comm, 9 goals."""
import re
from pathlib import Path

ROOT = Path("/home/argustest/.openclaw/workspace/tainverify_lean/trainverify")
GENDATA = (ROOT / "denote/gpt_ly4_segments/GeneratedData.lean").read_text().split("\n")

# Find sm.nodes and pm.nodes indexes for BW_layernorm
def collect(graph_name):
    """Return list of (node_idx, rank, ins, outs) for BW_layernorm nodes in graph."""
    in_graph = False
    node_idx = 0
    result = []
    for line in GENDATA:
        if line.startswith(f"def {graph_name} "):
            in_graph = True
            continue
        if in_graph and line.startswith("def "):
            break
        if in_graph and re.match(r"^    \{ rank", line):
            m = re.search(r"\{ rank := (\d+), op := \"OpName\.([^\"]+)\", ins := \[([^\]]+)\], outs := \[([^\]]+)\]", line)
            if m and m.group(2) == "BW_layernorm":
                rank = int(m.group(1))
                ins = [int(x.strip()) for x in m.group(3).split(",")]
                outs = [int(x.strip()) for x in m.group(4).split(",")]
                result.append((node_idx, rank, ins, outs))
            node_idx += 1
    return result

sm_bw = collect("sm")
pm_bw = collect("pm")

# Print discovered nodes for verification
print("SM BW_layernorm nodes:")
for idx, rank, ins, outs in sm_bw:
    print(f"  idx={idx} rank={rank} ins={ins} outs={outs}")
print("PM BW_layernorm nodes:")
for idx, rank, ins, outs in pm_bw[:20]:
    print(f"  idx={idx} rank={rank} ins={ins} outs={outs}")

# GOAL spec: (goal_id, sm_out_dx, pm_dx_outs [shard0..3], X_pat, X_goal, G_pat, G_goal)
GOALS = [
    (251, 890, [3335, 3338, 3341, 3344], 44, 104, 78, 254),
    (258, 904, [1157, 1161, 1165, 1169], 127, 257, 60, 114),
    (268, 935, [1541, 1545, 1549, 1553], 127, 267, 78, 140),
    (272, 947, [1677, 1681, 1685, 1689], 127, 271, 83, 149),
    (282, 978, [2097, 2101, 2105, 2109], 127, 281, 78, 175),
    (286, 990, [2241, 2245, 2249, 2253], 128, 285, 101, 184),
    (296, 1021, [2653, 2657, 2661, 2665], 128, 295, 113, 210),
    (300, 1033, [2797, 2801, 2805, 2809], 128, 299, 116, 219),
    (310, 1064, [3217, 3221, 3225, 3229], 128, 309, 113, 245),
]

# Build SM lookup: dx_out -> (idx, ins, outs)
sm_lookup = {outs[0]: (idx, ins, outs) for idx, rank, ins, outs in sm_bw}
pm_lookup = {outs[0]: (idx, rank, ins, outs) for idx, rank, ins, outs in pm_bw}

# Verify
for gid, sm_dx, pm_dxs, *_ in GOALS:
    assert sm_dx in sm_lookup, f"sm dx {sm_dx} not found"
    for pdx in pm_dxs:
        assert pdx in pm_lookup, f"pm dx {pdx} not found"

# ---- Generate file ----

def fmt_outs(outs):
    return ", ".join(str(o) for o in outs)

HEADER = '''/- Auto-generated pattern proof file.
   Pattern: 125
   Hash: 9df962180fe72704
   Goals: 251, 258, 268, 272, 282, 286, 296, 300, 310
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

set_option maxRecDepth 32768

/-! ## Chunk-of-allGather inverse for shape `[1, 2, 32]`. -/

private lemma valAt_ag1_1_2_32_pj_p125 (xs : List Tensor) (p j : Nat)
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

private lemma chunk1_4_of_ag1_1_2_32_p125 (xs : List Tensor) (r : Nat) (hr : r < 4)
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
    rw [valAt_ag1_1_2_32_pj_p125 xs (r * 2 + p) j hhead hrp_lt hjb]
    have hd : (r * 2 + p) / 2 = r := by omega
    have hm : (r * 2 + p) % 2 = p := by omega
    rw [hd, hm]

private lemma chunk1_4_of_ag1_1_2_32_explicit_p125 (t0 t1 t2 t3 : Tensor) (r : Nat) (hr : r < 4)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 r (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) =
      ([t0, t1, t2, t3]).getD r (zeroTensor [1, 2, 32]) := by
  apply chunk1_4_of_ag1_1_2_32_p125 _ r hr
  · simp [h0]
  · intro i hi
    match i, hi with
    | 0, _ => simpa [List.getD] using h0
    | 1, _ => simpa [List.getD] using h1
    | 2, _ => simpa [List.getD] using h2
    | 3, _ => simpa [List.getD] using h3

private lemma chunk1_4_of_ag1_1_2_32_idx0_p125 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 0 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t0 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p125 t0 t1 t2 t3 0 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx1_p125 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 1 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t1 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p125 t0 t1 t2 t3 1 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx2_p125 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 2 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t2 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p125 t0 t1 t2 t3 2 (by omega) h0 h1 h2 h3]; rfl

private lemma chunk1_4_of_ag1_1_2_32_idx3_p125 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 2, 32]) (h1 : t1.shape = [1, 2, 32])
    (h2 : t2.shape = [1, 2, 32]) (h3 : t3.shape = [1, 2, 32]) :
    chunkPrimDimN 1 4 3 (allGatherPrimDimN 1 4 0 [t0, t1, t2, t3]) = t3 := by
  rw [chunk1_4_of_ag1_1_2_32_explicit_p125 t0 t1 t2 t3 3 (by omega) h0 h1 h2 h3]; rfl

/-! ## BW_layernorm dX bridge for shape [1,8,32], dim=1 sharded into 4 chunks of size 2. -/

private theorem evalOp_bw_layernorm_p125 (numParts rank : Nat) (params : List Nat)
    (g x w b : Tensor) :
    evalOp numParts rank "OpName.BW_layernorm" params [g, x, w, b] =
      [(bw_layernorm g x w b).1, (bw_layernorm g x w b).2.1, (bw_layernorm g x w b).2.2] := by
  rfl

private theorem applyNode_bw_layernorm_dx_out_p125
    (g_decl : GraphDecl) (s : Store) (rank : Nat)
    (gTid xTid wTid bTid dxTid dwTid dbTid : Tid)
    (params : List Nat) :
    applyNode g_decl s { rank := rank, op := "OpName.BW_layernorm",
                    ins := [gTid, xTid, wTid, bTid],
                    outs := [dxTid, dwTid, dbTid], params := params } dxTid =
      (bw_layernorm (s gTid) (s xTid) (s wTid) (s bTid)).1 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid, bTid] : List Tid).map s =
      [s gTid, s xTid, s wTid, s bTid] from rfl,
      evalOp_bw_layernorm_p125]
  change storeSet s [(dxTid, (bw_layernorm (s gTid) (s xTid) (s wTid) (s bTid)).1),
                     (dwTid, (bw_layernorm (s gTid) (s xTid) (s wTid) (s bTid)).2.1),
                     (dbTid, (bw_layernorm (s gTid) (s xTid) (s wTid) (s bTid)).2.2)] dxTid = _
  unfold storeSet
  simp [List.find?]

private theorem bw_layernorm_dx_eq_p125 (g x w b : Tensor) (d : Nat) (rest : List Nat)
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

private theorem bw_layernorm_dx_shape_1_8_32_p125 (g x w b : Tensor) (hx : x.shape = [1, 8, 32]) :
    (bw_layernorm g x w b).1.shape = [1, 8, 32] := by
  rw [bw_layernorm_dx_eq_p125 g x w b 32 [8, 1] (by rw [hx]; rfl)]
  simp [Tensor.mkShape, hx]

private theorem bw_layernorm_dx_shape_1_2_32_p125 (g x w b : Tensor) (hx : x.shape = [1, 2, 32]) :
    (bw_layernorm g x w b).1.shape = [1, 2, 32] := by
  rw [bw_layernorm_dx_eq_p125 g x w b 32 [2, 1] (by rw [hx]; rfl)]
  simp [Tensor.mkShape, hx]

private theorem bw_layernorm_dx_valAt_1_8_32_p125 (g x w b : Tensor) (p j : Nat)
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
  rw [bw_layernorm_dx_eq_p125 g x w b 32 [8, 1] (by rw [hx]; rfl)]
  have hidx_shape : p * 32 + j < prodShape (Tensor.mkShape x.shape
      (fun outIdx : Fin (prodShape x.shape) =>
        let row := outIdx.1 / 32
        let j2 := outIdx.1 % 32
        let mean := layerNormMeanAt x row 32
        let var := layerNormVarAt x row 32 mean
        let invStd := 1 / sqrtFn (var + layerNormEps)
        let xhat := (valAt x outIdx.1 - mean) * invStd
        let sumDy := ∑ k ∈ Finset.range 32,
          valAt g (row * 32 + k) * valAt w k
        let sumDyXhat := ∑ k ∈ Finset.range 32,
          let xhatK := (valAt x (row * 32 + k) - mean) * invStd
          (valAt g (row * 32 + k) * valAt w k) * xhatK
        invStd / (32 : Scalar) *
          ((32 : Scalar) * (valAt g outIdx.1 * valAt w j2) - sumDy - xhat * sumDyXhat))).shape := by
    simp [Tensor.mkShape, hx, prodShape]; exact hidx
  rw [valAt_of_lt _ _ hidx_shape]
  simp only [Tensor.mkShape]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  rw [hdj, hmj]

private theorem bw_layernorm_dx_valAt_1_2_32_p125 (g x w b : Tensor) (p j : Nat)
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
  rw [bw_layernorm_dx_eq_p125 g x w b 32 [2, 1] (by rw [hx]; rfl)]
  have hidx_shape : p * 32 + j < prodShape (Tensor.mkShape x.shape
      (fun outIdx : Fin (prodShape x.shape) =>
        let row := outIdx.1 / 32
        let j2 := outIdx.1 % 32
        let mean := layerNormMeanAt x row 32
        let var := layerNormVarAt x row 32 mean
        let invStd := 1 / sqrtFn (var + layerNormEps)
        let xhat := (valAt x outIdx.1 - mean) * invStd
        let sumDy := ∑ k ∈ Finset.range 32,
          valAt g (row * 32 + k) * valAt w k
        let sumDyXhat := ∑ k ∈ Finset.range 32,
          let xhatK := (valAt x (row * 32 + k) - mean) * invStd
          (valAt g (row * 32 + k) * valAt w k) * xhatK
        invStd / (32 : Scalar) *
          ((32 : Scalar) * (valAt g outIdx.1 * valAt w j2) - sumDy - xhat * sumDyXhat))).shape := by
    simp [Tensor.mkShape, hx, prodShape]; exact hidx
  rw [valAt_of_lt _ _ hidx_shape]
  simp only [Tensor.mkShape]
  have hdj : (p * 32 + j) / 32 = p := by omega
  have hmj : (p * 32 + j) % 32 = j := by omega
  rw [hdj, hmj]

set_option maxHeartbeats 4000000 in
private theorem bw_layernorm_dx_split_dim1_4_1_8_32_p125 (g x w b : Tensor)
    (hg : g.shape = [1, 8, 32]) (hx : x.shape = [1, 8, 32]) :
    (bw_layernorm g x w b).1 =
      allGatherPrimDimN 1 4 0
        [(bw_layernorm (chunkPrimDimN 1 4 0 g) (chunkPrimDimN 1 4 0 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 1 g) (chunkPrimDimN 1 4 1 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 2 g) (chunkPrimDimN 1 4 2 x) w b).1,
         (bw_layernorm (chunkPrimDimN 1 4 3 g) (chunkPrimDimN 1 4 3 x) w b).1] := by
  have hchunkX_shape : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
    intro r _
    rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
    simp [List.set, List.getD]
  have hchunkG_shape : ∀ r, r < 4 →
      (chunkPrimDimN 1 4 r g).shape = [1, 2, 32] := by
    intro r _
    rw [chunkPrimDimN_shape 1 4 r _ _ hg (by omega)]
    simp [List.set, List.getD]
  have hbw_chunk_shape : ∀ r, r < 4 →
      (bw_layernorm (chunkPrimDimN 1 4 r g) (chunkPrimDimN 1 4 r x) w b).1.shape = [1, 2, 32] := by
    intro r hr
    exact bw_layernorm_dx_shape_1_2_32_p125 _ _ w b (hchunkX_shape r hr)
  have hlhs_shape : (bw_layernorm g x w b).1.shape = [1, 8, 32] :=
    bw_layernorm_dx_shape_1_8_32_p125 g x w b hx
  have hhead : ((([(bw_layernorm (chunkPrimDimN 1 4 0 g) (chunkPrimDimN 1 4 0 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 1 g) (chunkPrimDimN 1 4 1 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 2 g) (chunkPrimDimN 1 4 2 x) w b).1,
       (bw_layernorm (chunkPrimDimN 1 4 3 g) (chunkPrimDimN 1 4 3 x) w b).1] : List Tensor).head?).map
       (fun t => t.shape)).getD [] = [1, 2, 32] := by
    simp [List.head?]
    exact hbw_chunk_shape 0 (by omega)
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
    have hidx_eq : idx = p * 32 + j := by subst p j; omega
    rw [hidx_eq]
    rw [bw_layernorm_dx_valAt_1_8_32_p125 g x w b p j hx hp_lt hj_lt]
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
      show (32 : Nat) ≠ 0 by omega,
      show (2 : Nat) ≠ 0 by omega,
      ite_false]
    simp only [show (2 : Nat) * 4 * 1 = 8 by norm_num,
      show (8 : Nat) * (1 * 32) = 256 by norm_num,
      show (1 : Nat) * 32 = 32 by norm_num,
      show (2 : Nat) * (1 * 32) = 64 by norm_num,
      show (256 : Nat) = 0 ↔ False by simp,
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
    rw [show (p % 2 : Nat) = p' from rfl]
    have hxL : valAt x (p * 32 + j) =
        valAt (chunkPrimDimN 1 4 r x) (p' * 32 + j) := by
      rw [chunk_dim1_4_1_8_32_valAt x r p' j hx hr_lt hp'_lt hj_lt, ← hp_eq]
    have hmeanL : layerNormMeanAt x p 32 =
        layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32 := by
      rw [layerNormMeanAt_chunk_dim1_4_1_8_32 x r p' hx hr_lt hp'_lt, ← hp_eq]
    have hvarL : layerNormVarAt x p 32 (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32)
            = layerNormVarAt (chunkPrimDimN 1 4 r x) p' 32
                (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) := by
      rw [layerNormVarAt_chunk_dim1_4_1_8_32 x r p'
          (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) hx hr_lt hp'_lt, ← hp_eq]
    have hgL : valAt g (p * 32 + j) =
        valAt (chunkPrimDimN 1 4 r g) (p' * 32 + j) := by
      rw [chunk_dim1_4_1_8_32_valAt g r p' j hg hr_lt hp'_lt hj_lt, ← hp_eq]
    have hsumDy : (∑ k ∈ Finset.range 32, valAt g (p * 32 + k) * valAt w k) =
                  (∑ k ∈ Finset.range 32,
                    valAt (chunkPrimDimN 1 4 r g) (p' * 32 + k) * valAt w k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [chunk_dim1_4_1_8_32_valAt g r p' k hg hr_lt hp'_lt hk, ← hp_eq]
    have hsumDyXhat : (∑ k ∈ Finset.range 32,
                        (valAt g (p * 32 + k) * valAt w k) *
                          ((valAt x (p * 32 + k) - layerNormMeanAt x p 32) *
                            (1 / sqrtFn (layerNormVarAt x p 32 (layerNormMeanAt x p 32) + layerNormEps)))) =
                       (∑ k ∈ Finset.range 32,
                        (valAt (chunkPrimDimN 1 4 r g) (p' * 32 + k) * valAt w k) *
                          ((valAt (chunkPrimDimN 1 4 r x) (p' * 32 + k) -
                              layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) *
                            (1 / sqrtFn (layerNormVarAt (chunkPrimDimN 1 4 r x) p' 32
                                (layerNormMeanAt (chunkPrimDimN 1 4 r x) p' 32) + layerNormEps)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [chunk_dim1_4_1_8_32_valAt g r p' k hg hr_lt hp'_lt hk,
          chunk_dim1_4_1_8_32_valAt x r p' k hx hr_lt hp'_lt hk,
          layerNormMeanAt_chunk_dim1_4_1_8_32 x r p' hx hr_lt hp'_lt,
          layerNormVarAt_chunk_dim1_4_1_8_32 x r p'
            (layerNormMeanAt x (r * 2 + p') 32) hx hr_lt hp'_lt, ← hp_eq]
    rw [hxL, hmeanL, hvarL, hgL, hsumDy, hsumDyXhat]
    rw [← bw_layernorm_dx_valAt_1_2_32_p125 (chunkPrimDimN 1 4 r g) (chunkPrimDimN 1 4 r x) w b p' j
        (hchunkX_shape r hr_lt) hp'_lt hj_lt]
    rw [show (0 : Nat) * 64 + p' * 32 + j = p' * 32 + j by ring]
    have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr_cases with h0 | h1 | h2 | h3
    all_goals first
      | (rw [h0]; rfl)
      | (rw [h1]; rfl)
      | (rw [h2]; rfl)
      | (rw [h3]; rfl)

/-! ## Generic singleton lift for BW_layernorm dX over AllGather(dim=1, 4 parts). -/

private theorem bw_layernorm_dx_dim1_4_singleton_lift
    (initSM initPM : Store)
    (smOutTid smInGTid smInXTid wTid bTid : Tid)
    (pmOut0 pmOut1 pmOut2 pmOut3 : Tid)
    (pmInG0 pmInG1 pmInG2 pmInG3 : Tid)
    (pmInX0 pmInX1 pmInX2 pmInX3 : Tid)
    (h_sm_eval : denoteGraph sm initSM smOutTid =
      (bw_layernorm (denoteGraph sm initSM smInGTid)
                    (denoteGraph sm initSM smInXTid)
                    (denoteGraph sm initSM wTid)
                    (denoteGraph sm initSM bTid)).1)
    (h_pm0_eval : denoteGraph pm initPM pmOut0 =
      (bw_layernorm (denoteGraph pm initPM pmInG0)
                    (denoteGraph pm initPM pmInX0)
                    (denoteGraph pm initPM wTid)
                    (denoteGraph pm initPM bTid)).1)
    (h_pm1_eval : denoteGraph pm initPM pmOut1 =
      (bw_layernorm (denoteGraph pm initPM pmInG1)
                    (denoteGraph pm initPM pmInX1)
                    (denoteGraph pm initPM wTid)
                    (denoteGraph pm initPM bTid)).1)
    (h_pm2_eval : denoteGraph pm initPM pmOut2 =
      (bw_layernorm (denoteGraph pm initPM pmInG2)
                    (denoteGraph pm initPM pmInX2)
                    (denoteGraph pm initPM wTid)
                    (denoteGraph pm initPM bTid)).1)
    (h_pm3_eval : denoteGraph pm initPM pmOut3 =
      (bw_layernorm (denoteGraph pm initPM pmInG3)
                    (denoteGraph pm initPM pmInX3)
                    (denoteGraph pm initPM wTid)
                    (denoteGraph pm initPM bTid)).1)
    (hW_sm_pm : denoteGraph sm initSM wTid = denoteGraph pm initPM wTid)
    (hB_sm_pm : denoteGraph sm initSM bTid = denoteGraph pm initPM bTid)
    (hGshape : (denoteGraph sm initSM smInGTid).shape = [1, 8, 32])
    (hXshape : (denoteGraph sm initSM smInXTid).shape = [1, 8, 32])
    (hIG0 : (denoteGraph pm initPM pmInG0).shape = [1, 2, 32])
    (hIG1 : (denoteGraph pm initPM pmInG1).shape = [1, 2, 32])
    (hIG2 : (denoteGraph pm initPM pmInG2).shape = [1, 2, 32])
    (hIG3 : (denoteGraph pm initPM pmInG3).shape = [1, 2, 32])
    (hIX0 : (denoteGraph pm initPM pmInX0).shape = [1, 2, 32])
    (hIX1 : (denoteGraph pm initPM pmInX1).shape = [1, 2, 32])
    (hIX2 : (denoteGraph pm initPM pmInX2).shape = [1, 2, 32])
    (hIX3 : (denoteGraph pm initPM pmInX3).shape = [1, 2, 32])
    (h_g_gather : denoteGraph sm initSM smInGTid =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM pmInG0, denoteGraph pm initPM pmInG1,
         denoteGraph pm initPM pmInG2, denoteGraph pm initPM pmInG3])
    (h_x_gather : denoteGraph sm initSM smInXTid =
      allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM pmInX0, denoteGraph pm initPM pmInX1,
         denoteGraph pm initPM pmInX2, denoteGraph pm initPM pmInX3]) :
    (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] ∧
      [(denoteGraph pm initPM pmOut0).shape, (denoteGraph pm initPM pmOut1).shape,
       (denoteGraph pm initPM pmOut2).shape, (denoteGraph pm initPM pmOut3).shape] =
        ([[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] : List Shape) ∧
      denoteGraph sm initSM smOutTid =
        reconstructWithDim 1 pm.numRanks 0
          [denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
           denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3] := by
  have hSmOut_shape : (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] := by
    rw [h_sm_eval]; exact bw_layernorm_dx_shape_1_8_32_p125 _ _ _ _ hXshape
  have hP0_shape : (denoteGraph pm initPM pmOut0).shape = [1, 2, 32] := by
    rw [h_pm0_eval]; exact bw_layernorm_dx_shape_1_2_32_p125 _ _ _ _ hIX0
  have hP1_shape : (denoteGraph pm initPM pmOut1).shape = [1, 2, 32] := by
    rw [h_pm1_eval]; exact bw_layernorm_dx_shape_1_2_32_p125 _ _ _ _ hIX1
  have hP2_shape : (denoteGraph pm initPM pmOut2).shape = [1, 2, 32] := by
    rw [h_pm2_eval]; exact bw_layernorm_dx_shape_1_2_32_p125 _ _ _ _ hIX2
  have hP3_shape : (denoteGraph pm initPM pmOut3).shape = [1, 2, 32] := by
    rw [h_pm3_eval]; exact bw_layernorm_dx_shape_1_2_32_p125 _ _ _ _ hIX3
  refine ⟨hSmOut_shape, ?_, ?_⟩
  · simp [hP0_shape, hP1_shape, hP2_shape, hP3_shape]
  · rw [show pm.numRanks = 4 from rfl, reconstructWithDim_cons_cons_nonscalar]
    swap
    · rw [hP0_shape]; intro hbad; cases hbad
    rw [h_sm_eval, h_g_gather, h_x_gather]
    have hag_g_shape :
        (allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM pmInG0, denoteGraph pm initPM pmInG1,
           denoteGraph pm initPM pmInG2, denoteGraph pm initPM pmInG3]).shape = [1, 8, 32] := by
      have hh :
          (([denoteGraph pm initPM pmInG0, denoteGraph pm initPM pmInG1,
             denoteGraph pm initPM pmInG2, denoteGraph pm initPM pmInG3]
             : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
        simp [hIG0]
      rw [allGatherPrimDimN_shape 1 4 _ _ hh]; simp [List.set, List.getD]
    have hag_x_shape :
        (allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM pmInX0, denoteGraph pm initPM pmInX1,
           denoteGraph pm initPM pmInX2, denoteGraph pm initPM pmInX3]).shape = [1, 8, 32] := by
      have hh :
          (([denoteGraph pm initPM pmInX0, denoteGraph pm initPM pmInX1,
             denoteGraph pm initPM pmInX2, denoteGraph pm initPM pmInX3]
             : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 2, 32] := by
        simp [hIX0]
      rw [allGatherPrimDimN_shape 1 4 _ _ hh]; simp [List.set, List.getD]
    rw [bw_layernorm_dx_split_dim1_4_1_8_32_p125 _ _
        (denoteGraph sm initSM wTid) (denoteGraph sm initSM bTid) hag_g_shape hag_x_shape]
    rw [chunk1_4_of_ag1_1_2_32_idx0_p125 _ _ _ _ hIG0 hIG1 hIG2 hIG3,
        chunk1_4_of_ag1_1_2_32_idx1_p125 _ _ _ _ hIG0 hIG1 hIG2 hIG3,
        chunk1_4_of_ag1_1_2_32_idx2_p125 _ _ _ _ hIG0 hIG1 hIG2 hIG3,
        chunk1_4_of_ag1_1_2_32_idx3_p125 _ _ _ _ hIG0 hIG1 hIG2 hIG3]
    rw [chunk1_4_of_ag1_1_2_32_idx0_p125 _ _ _ _ hIX0 hIX1 hIX2 hIX3,
        chunk1_4_of_ag1_1_2_32_idx1_p125 _ _ _ _ hIX0 hIX1 hIX2 hIX3,
        chunk1_4_of_ag1_1_2_32_idx2_p125 _ _ _ _ hIX0 hIX1 hIX2 hIX3,
        chunk1_4_of_ag1_1_2_32_idx3_p125 _ _ _ _ hIX0 hIX1 hIX2 hIX3]
    rw [hW_sm_pm, hB_sm_pm]
    rw [← h_pm0_eval, ← h_pm1_eval, ← h_pm2_eval, ← h_pm3_eval]

/-! ## Per-goal SM/PM eval helpers -/

'''


def gen_eval(graph, store, name, node_idx, rank, ins, outs):
    """Generate sm_eval or pm_eval helper. graph = 'sm'|'pm', store = 'initSM'|'initPM'."""
    take_n = node_idx + 1
    take_prev = node_idx
    gTid, xTid, wTid, bTid = ins
    dxTid, dwTid, dbTid = outs
    return f'''set_option maxHeartbeats 4000000 in
private theorem {name} ({store} : Store) :
    denoteGraph {graph} {store} {dxTid} =
      (bw_layernorm (denoteGraph {graph} {store} {gTid})
                    (denoteGraph {graph} {store} {xTid})
                    (denoteGraph {graph} {store} {wTid})
                    (denoteGraph {graph} {store} {bTid})).1 := by
  have hsub : (denoteGraph {graph} {store}) {dxTid} =
      (denoteGraph {{ {graph} with nodes := {graph}.nodes.take {take_n} }} {store}) {dxTid} :=
    denoteGraph_tid_eq_of_suffix_no_writes {graph} {store} {dxTid}
      ({graph}.nodes.take {take_n}) ({graph}.nodes.drop {take_n})
      (List.take_append_drop {take_n} _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  rw [show ({{ {graph} with nodes := {graph}.nodes.take {take_n} }} : GraphDecl) =
      {{ {graph} with nodes := {graph}.nodes.take {take_prev} ++ [{{ rank := {rank}, op := "OpName.BW_layernorm", ins := [{gTid}, {xTid}, {wTid}, {bTid}], outs := [{dxTid}, {dwTid}, {dbTid}], params := [] }}] }} from rfl]
  rw [denoteGraph_nodes_append]
  rw [show ({{ {graph} with nodes := [{{ rank := {rank}, op := "OpName.BW_layernorm", ins := [{gTid}, {xTid}, {wTid}, {bTid}], outs := [{dxTid}, {dwTid}, {dbTid}], params := [] }}] }} : GraphDecl) =
      {{ numRanks := {graph}.numRanks, nodes := {{ rank := {rank}, op := "OpName.BW_layernorm", ins := [{gTid}, {xTid}, {wTid}, {bTid}], outs := [{dxTid}, {dwTid}, {dbTid}], params := [] }} :: [] }} from rfl]
  rw [denoteGraph_cons_eq {graph} _ []]
  rw [denoteGraph_nodes_nil]
  rw [applyNode_bw_layernorm_dx_out_p125]
  have hG : denoteGraph {{ {graph} with nodes := {graph}.nodes.take {take_prev} }} {store} {gTid} = denoteGraph {graph} {store} {gTid} := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes {graph} {store} {gTid}
      ({graph}.nodes.take {take_prev}) ({graph}.nodes.drop {take_prev})
      (List.take_append_drop {take_prev} _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hX : denoteGraph {{ {graph} with nodes := {graph}.nodes.take {take_prev} }} {store} {xTid} = denoteGraph {graph} {store} {xTid} := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes {graph} {store} {xTid}
      ({graph}.nodes.take {take_prev}) ({graph}.nodes.drop {take_prev})
      (List.take_append_drop {take_prev} _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hW : denoteGraph {{ {graph} with nodes := {graph}.nodes.take {take_prev} }} {store} {wTid} = denoteGraph {graph} {store} {wTid} := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes {graph} {store} {wTid}
      ({graph}.nodes.take {take_prev}) ({graph}.nodes.drop {take_prev})
      (List.take_append_drop {take_prev} _).symm
      (by set_option maxRecDepth 20000 in decide)
  have hB : denoteGraph {{ {graph} with nodes := {graph}.nodes.take {take_prev} }} {store} {bTid} = denoteGraph {graph} {store} {bTid} := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes {graph} {store} {bTid}
      ({graph}.nodes.take {take_prev}) ({graph}.nodes.drop {take_prev})
      (List.take_append_drop {take_prev} _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hG, hX, hW, hB]

'''

# Find upstream goal info to know X-lineage, G-lineage tids:
# X-pat goal gives smInXTid -> [x0,x1,x2,x3]
# G-pat goal gives smInGTid -> [g0,g1,g2,g3]

# Parse upstream LineageGoals from GeneratedData
LG_RE = re.compile(r'^def goal_(\d+) : LineageGoal :=\s*\{ ts := (\d+), tsShape := (\[[^\]]*\]), tps := \[((?:\{ rank := \d+, tid := \d+ \},?\s*)+)\], tpShapes := \[((?:\[[^\]]*\],?\s*)+)\](?:, gatherDim := (\d+))? \}', re.MULTILINE)

# Use simpler line-by-line approach
lineage = {}
gendata_lines = GENDATA
i = 0
while i < len(gendata_lines):
    line = gendata_lines[i]
    m = re.match(r'^def goal_(\d+) : LineageGoal :=', line)
    if m and i + 1 < len(gendata_lines):
        body = gendata_lines[i+1]
        ts_m = re.search(r'ts := (\d+)', body)
        tps_m = re.search(r'tps := \[(.*?)\], tpShapes', body)
        if ts_m and tps_m:
            gid = int(m.group(1))
            ts = int(ts_m.group(1))
            tids = [int(x) for x in re.findall(r'tid := (\d+)', tps_m.group(1))]
            lineage[gid] = (ts, tids)
    i += 1

for gid in [104, 114, 140, 149, 175, 184, 210, 219, 245, 254, 257, 267, 271, 281, 285, 295, 299, 309]:
    assert gid in lineage, f"missing lineage for goal_{gid}"
    print(f"goal_{gid}: ts={lineage[gid][0]}, tps={lineage[gid][1]}")


def gen_case(goal_id, sm_dx_out, pm_dxs, x_pat, x_goal, g_pat, g_goal):
    sm_idx, sm_ins, sm_outs = sm_lookup[sm_dx_out]
    sm_G, sm_X, sm_W, sm_B = sm_ins
    # Validate against lineage
    x_ts, x_shards = lineage[x_goal]
    g_ts, g_shards = lineage[g_goal]
    assert x_ts == sm_X, f"X-lineage mismatch goal {goal_id}: x_ts={x_ts}, sm_X={sm_X}"
    assert g_ts == sm_G, f"G-lineage mismatch goal {goal_id}: g_ts={g_ts}, sm_G={sm_G}"
    # PM shards
    pm_X_shards = []
    pm_G_shards = []
    for pdx in pm_dxs:
        idx, rank, ins, outs = pm_lookup[pdx]
        gTid, xTid, wTid, bTid = ins
        pm_G_shards.append(gTid)
        pm_X_shards.append(xTid)
    assert x_shards == pm_X_shards, f"X shards: {x_shards} vs {pm_X_shards}"
    assert g_shards == pm_G_shards, f"G shards: {g_shards} vs {pm_G_shards}"
    g0, g1, g2, g3 = g_shards
    x0, x1, x2, x3 = x_shards
    p0, p1, p2, p3 = pm_dxs

    return f'''  | goal_{goal_id} =>
    intro initSM initPM hSmInit hPmInit hInitGoals
    have hX_lin : goal_{x_goal}_stmt :=
      prove_pattern_{x_pat} pattern_{x_pat}_target.goal_{x_goal}
    have hX_tr := hX_lin initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨hX_sm_shape, hX_pm_shapes, hX_eq_rec⟩ := hX_tr
    have hX_pm_shapes' :
        [(denoteGraph pm initPM {x0}).shape, (denoteGraph pm initPM {x1}).shape,
         (denoteGraph pm initPM {x2}).shape, (denoteGraph pm initPM {x3}).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := hX_pm_shapes
      simpa [goal_{x_goal}, List.map_cons, List.map_nil] using hs
    have hX_split :
        (denoteGraph pm initPM {x0}).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM {x1}).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM {x2}).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM {x3}).shape = [1, 2, 32] := by
      have hh := hX_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hIX0 : (denoteGraph pm initPM {x0}).shape = [1, 2, 32] := hX_split.1
    have hIX1 : (denoteGraph pm initPM {x1}).shape = [1, 2, 32] := hX_split.2.1
    have hIX2 : (denoteGraph pm initPM {x2}).shape = [1, 2, 32] := hX_split.2.2.1
    have hIX3 : (denoteGraph pm initPM {x3}).shape = [1, 2, 32] := hX_split.2.2.2
    have hXshape : (denoteGraph sm initSM {sm_X}).shape = [1, 8, 32] := by
      have hs := hX_sm_shape; simpa [goal_{x_goal}] using hs
    have h_x_gather : denoteGraph sm initSM {sm_X} = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM {x0}, denoteGraph pm initPM {x1},
         denoteGraph pm initPM {x2}, denoteGraph pm initPM {x3}] := by
      have hh := hX_eq_rec
      simp only [goal_{x_goal}, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hIX0]; intro hbad; cases hbad
    have hG_lin : goal_{g_goal}_stmt :=
      prove_pattern_{g_pat} pattern_{g_pat}_target.goal_{g_goal}
    have hG_tr := hG_lin initSM initPM hSmInit hPmInit hInitGoals
    obtain ⟨hG_sm_shape, hG_pm_shapes, hG_eq_rec⟩ := hG_tr
    have hG_pm_shapes' :
        [(denoteGraph pm initPM {g0}).shape, (denoteGraph pm initPM {g1}).shape,
         (denoteGraph pm initPM {g2}).shape, (denoteGraph pm initPM {g3}).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]] := by
      have hs := hG_pm_shapes
      simpa [goal_{g_goal}, List.map_cons, List.map_nil] using hs
    have hG_split :
        (denoteGraph pm initPM {g0}).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM {g1}).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM {g2}).shape = [1, 2, 32] ∧
        (denoteGraph pm initPM {g3}).shape = [1, 2, 32] := by
      have hh := hG_pm_shapes'
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    have hIG0 : (denoteGraph pm initPM {g0}).shape = [1, 2, 32] := hG_split.1
    have hIG1 : (denoteGraph pm initPM {g1}).shape = [1, 2, 32] := hG_split.2.1
    have hIG2 : (denoteGraph pm initPM {g2}).shape = [1, 2, 32] := hG_split.2.2.1
    have hIG3 : (denoteGraph pm initPM {g3}).shape = [1, 2, 32] := hG_split.2.2.2
    have hGshape : (denoteGraph sm initSM {sm_G}).shape = [1, 8, 32] := by
      have hs := hG_sm_shape; simpa [goal_{g_goal}] using hs
    have h_g_gather : denoteGraph sm initSM {sm_G} = allGatherPrimDimN 1 4 0
        [denoteGraph pm initPM {g0}, denoteGraph pm initPM {g1},
         denoteGraph pm initPM {g2}, denoteGraph pm initPM {g3}] := by
      have hh := hG_eq_rec
      simp only [goal_{g_goal}, List.map_cons, List.map_nil] at hh
      rw [hh]
      rw [show pm.numRanks = 4 from rfl]
      rw [reconstructWithDim_cons_cons_nonscalar]
      · rw [hIG0]; intro hbad; cases hbad
    have h_init_W : InitGoalHolds pm.numRanks initGoal_{sm_W} initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have h_init_B : InitGoalHolds pm.numRanks initGoal_{sm_B} initSM initPM := by
      apply hInitGoals; simp [initGoals]
    have hW_init_eq : initSM {sm_W} = initPM {sm_W} := by
      have hh := h_init_W.2.2
      simpa [initGoal_{sm_W}, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have hB_init_eq : initSM {sm_B} = initPM {sm_B} := by
      have hh := h_init_B.2.2
      simpa [initGoal_{sm_B}, List.map_cons, List.map_nil, reconstructWithDim_singleton]
        using hh
    have h_smW_init : denoteGraph sm initSM {sm_W} = initSM {sm_W} := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM {sm_W}
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_smB_init : denoteGraph sm initSM {sm_B} = initSM {sm_B} := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes sm initSM {sm_B}
        [] sm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmW_init : denoteGraph pm initPM {sm_W} = initPM {sm_W} := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM {sm_W}
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have h_pmB_init : denoteGraph pm initPM {sm_B} = initPM {sm_B} := by
      have hh := denoteGraph_tid_eq_of_suffix_no_writes pm initPM {sm_B}
        [] pm.nodes (by simp)
        (by set_option maxRecDepth 20000 in decide)
      rw [hh]; rfl
    have hW_sm_pm : denoteGraph sm initSM {sm_W} = denoteGraph pm initPM {sm_W} := by
      rw [h_smW_init, h_pmW_init, hW_init_eq]
    have hB_sm_pm : denoteGraph sm initSM {sm_B} = denoteGraph pm initPM {sm_B} := by
      rw [h_smB_init, h_pmB_init, hB_init_eq]
    have h_main := bw_layernorm_dx_dim1_4_singleton_lift initSM initPM
      {sm_dx_out} {sm_G} {sm_X} {sm_W} {sm_B}
      {p0} {p1} {p2} {p3}
      {g0} {g1} {g2} {g3}
      {x0} {x1} {x2} {x3}
      (sm_eval_{sm_dx_out}_p125 initSM)
      (pm_eval_{p0}_p125 initPM) (pm_eval_{p1}_p125 initPM)
      (pm_eval_{p2}_p125 initPM) (pm_eval_{p3}_p125 initPM)
      hW_sm_pm hB_sm_pm hGshape hXshape
      hIG0 hIG1 hIG2 hIG3 hIX0 hIX1 hIX2 hIX3
      h_g_gather h_x_gather
    obtain ⟨hs1, hs2, hs3⟩ := h_main
    show (denoteGraph sm initSM {sm_dx_out}).shape = goal_{goal_id}.tsShape ∧
      _ = goal_{goal_id}.tpShapes ∧
      denoteGraph sm initSM {sm_dx_out} =
        reconstructWithDim goal_{goal_id}.gatherDim pm.numRanks 0
          (goal_{goal_id}.tps.map (fun p => denoteGraph pm initPM p.tid))
    refine ⟨?_, ?_, ?_⟩
    · simpa [goal_{goal_id}] using hs1
    · simpa [goal_{goal_id}, List.map_cons, List.map_nil] using hs2
    · simpa [goal_{goal_id}, List.map_cons, List.map_nil] using hs3
'''


# Build the file
out = HEADER

# Generate per-goal helpers in order
for gid, sm_dx, pm_dxs, *_ in GOALS:
    idx, ins, outs = sm_lookup[sm_dx]
    out += gen_eval("sm", "initSM", f"sm_eval_{sm_dx}_p125", idx, 0, ins, outs)
    for pdx in pm_dxs:
        idx, rank, ins, outs = pm_lookup[pdx]
        out += gen_eval("pm", "initPM", f"pm_eval_{pdx}_p125", idx, rank, ins, outs)

# Main theorem
out += '''theorem prove_pattern_125 : pattern_125_stmt := by
  intro target h
  cases h with
'''
for gid, sm_dx, pm_dxs, x_pat, x_goal, g_pat, g_goal in GOALS:
    out += gen_case(gid, sm_dx, pm_dxs, x_pat, x_goal, g_pat, g_goal)

out += '''
end TrainVerify.Denote.GeneratedPatterns
'''

(ROOT / "denote/gpt_ly4_segments/Pattern_125.lean").write_text(out)
print(f"\nWritten Pattern_125.lean: {len(out)} chars, {out.count(chr(10))} lines")
